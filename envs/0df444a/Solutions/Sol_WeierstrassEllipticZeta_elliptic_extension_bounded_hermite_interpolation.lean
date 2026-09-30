-- Prove2me | solution 1 for WeierstrassEllipticZeta.elliptic_extension_bounded_hermite_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T22:16:19.343454+00:00
-- url     : https://prove2.me/submissions/f4a20325-268a-4e4b-b3f6-3416c40cf16f

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveChartCalculus
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.FinCases

noncomputable section
open WeierstrassEllipticZeta

private lemma time_polynomial_jets (g₂ g₃ : ℂ) (c : Fin 2)
    (v : Fin 4 → ℂ) (p : Polynomial ℂ) (k : ℕ) :
    MvPolynomial.eval v ((extensionChartDerivation g₂ g₃ c)^[k]
      (Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) p)) =
        (Polynomial.derivative^[k] p).eval (v 0) := by
  have ht : extensionChartDerivation g₂ g₃ c (MvPolynomial.X (0 : Fin 4)) = 1 := by
    fin_cases c <;> simp [extensionChartDerivation]
  have h (k : ℕ) : (extensionChartDerivation g₂ g₃ c)^[k]
      (Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) p) =
      Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (Polynomial.derivative^[k] p) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, Derivation.comp_aeval_eq, ht,
        smul_eq_mul, mul_one, Function.iterate_succ_apply']
  rw [h]
  exact Polynomial.induction_on' (Polynomial.derivative^[k] p)
    (fun p q hp hq => by simp_all)
    (fun i a => by simp [Polynomial.aeval_monomial])

private lemma root_power_dvd_iff_jets (x : ℂ) (p : Polynomial ℂ) (n : ℕ) :
    (Polynomial.X - Polynomial.C x) ^ n ∣ p ↔
      ∀ k < n, (Polynomial.derivative^[k] p).eval x = 0 := by
  rw [Polynomial.X_sub_C_pow_dvd_iff, Polynomial.X_pow_dvd_iff]
  have h (k : ℕ) : (Polynomial.derivative^[k] p).eval x =
      (k.factorial : ℂ) * (Polynomial.taylor x p).coeff k := by
    rw [← Polynomial.factorial_smul_hasseDeriv]
    simp [Polynomial.taylor_coeff, nsmul_eq_mul]
  simp_rw [h, mul_eq_zero, Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _),
    false_or, Polynomial.taylor_apply]

private lemma local_jets (x : ℂ) (n : ℕ) (a : Fin n → ℂ) :
    ∃ p : Polynomial ℂ, ∀ k : Fin n, (Polynomial.derivative^[k.val] p).eval x = a k := by
  classical
  have hb (i k : ℕ) : (Polynomial.derivative^[k]
      ((Polynomial.X - Polynomial.C x) ^ i)).eval x =
      if k = i then (i.factorial : ℂ) else 0 := by
    rw [Polynomial.iterate_derivative_X_sub_pow]
    by_cases h : k = i
    · subst k
      simp [Nat.descFactorial_self]
    · rw [if_neg h]
      by_cases hi : i < k
      · simp [Nat.descFactorial_eq_zero_iff_lt.mpr hi]
      · simp [Nat.ne_of_gt (show 0 < i - k by omega)]
  refine ⟨∑ i : Fin n, (a i / (i.val.factorial : ℂ)) •
    (Polynomial.X - Polynomial.C x) ^ i.val, ?_⟩
  intro k
  have hs : (Polynomial.derivative^[k.val]
      (∑ i : Fin n, (a i / (i.val.factorial : ℂ)) •
        (Polynomial.X - Polynomial.C x) ^ i.val)).eval x =
      ∑ i : Fin n, (a i / (i.val.factorial : ℂ)) *
        (Polynomial.derivative^[k.val]
          ((Polynomial.X - Polynomial.C x) ^ i.val)).eval x := by
    simpa only [Module.End.pow_apply] using!
      (show (((Polynomial.derivative : Polynomial ℂ →ₗ[ℂ] Polynomial ℂ) ^ k.val)
        (∑ i : Fin n, (a i / (i.val.factorial : ℂ)) •
          (Polynomial.X - Polynomial.C x) ^ i.val)).eval x = _ by
        simp only [map_sum, map_smul]
        simp [Polynomial.smul_eq_C_mul, Polynomial.eval_finsetSum,
          Polynomial.eval_mul, Polynomial.eval_C, Module.End.pow_apply])
  rw [hs]
  simp_rw [hb, ← Fin.ext_iff, mul_ite, mul_zero]
  simp [Nat.factorial_ne_zero]

private lemma hermite_unique {ι : Type*} [Fintype ι] (x : ι → ℂ)
    (hx : Function.Injective x) (n : ι → ℕ) (a : (i : ι) → Fin (n i) → ℂ) :
    ∃! p : Polynomial ℂ, p.degree < (∑ i, n i : ℕ) ∧
      ∀ (i : ι) (k : Fin (n i)), (Polynomial.derivative^[k.val] p).eval (x i) = a i k := by
  classical
  let f : ι → Polynomial ℂ := fun i => (Polynomial.X - Polynomial.C (x i)) ^ n i
  have hcop : Pairwise (fun i j => IsCoprime (f i) (f j)) := by
    intro i j hij
    exact (Polynomial.pairwise_coprime_X_sub_C hx hij).pow
  let I : ι → Ideal (Polynomial ℂ) := fun i => Ideal.span {f i}
  have hI : Pairwise (fun i j => IsCoprime (I i) (I j)) := by
    intro i j hij
    exact (Ideal.isCoprime_span_singleton_iff _ _).mpr (hcop hij)
  choose b hb using fun i => local_jets (x i) (n i) (a i)
  obtain ⟨p, hp⟩ := Ideal.exists_forall_sub_mem_ideal hI b
  let M := ∏ i, f i
  have hmon : M.Monic := Polynomial.monic_prod_of_monic _ _ fun i _ =>
    (Polynomial.monic_X_sub_C (x i)).pow (n i)
  have hdeg : M.degree = (∑ i, n i : ℕ) := by
    simp [M, f, Polynomial.degree_prod, Polynomial.degree_pow]
  let r := p %ₘ M
  have hMr : M ∣ r - p := by
    refine ⟨-(p /ₘ M), ?_⟩
    have h := Polynomial.modByMonic_add_div p M
    dsimp [r]
    linear_combination h
  have hjet : ∀ i (k : Fin (n i)),
      (Polynomial.derivative^[k.val] r).eval (x i) = a i k := by
    intro i k
    have hd : f i ∣ r - b i := by
      have hri := (Finset.dvd_prod_of_mem f (Finset.mem_univ i)).trans hMr
      have hpi : f i ∣ p - b i := Ideal.mem_span_singleton.mp (hp i)
      convert dvd_add hri hpi using 1
      ring
    have h := (root_power_dvd_iff_jets (x i) (r - b i) (n i)).mp hd k.val k.isLt
    have hlin : (((Polynomial.derivative : Polynomial ℂ →ₗ[ℂ] Polynomial ℂ) ^ k.val)
        (r - b i)).eval (x i) = 0 := by simpa only [Module.End.pow_apply] using! h
    simp only [map_sub, Polynomial.eval_sub, Module.End.pow_apply] at hlin
    exact (sub_eq_zero.mp hlin).trans (hb i k)
  refine ⟨r, ⟨hdeg ▸ Polynomial.degree_modByMonic_lt p hmon, hjet⟩, ?_⟩
  intro q hq
  have hdiv : M ∣ q - r := by
    apply Finset.prod_dvd_of_coprime (by simpa [Set.pairwise_univ] using hcop)
    intro i _
    apply (root_power_dvd_iff_jets (x i) (q - r) (n i)).mpr
    intro k hk
    have hqk := hq.2 i ⟨k, hk⟩
    have hrk := hjet i ⟨k, hk⟩
    simpa only [Module.End.pow_apply] using!
      (show (((Polynomial.derivative : Polynomial ℂ →ₗ[ℂ] Polynomial ℂ) ^ k)
        (q - r)).eval (x i) = 0 by
        simp only [map_sub, Polynomial.eval_sub]
        simpa only [Module.End.pow_apply] using! sub_eq_zero.mpr (hqk.trans hrk.symm))
  apply sub_eq_zero.mp
  apply Polynomial.eq_zero_of_dvd_of_degree_lt hdiv
  rw [hdeg]
  exact (Polynomial.degree_sub_le _ _).trans_lt
    (max_lt hq.1 (hdeg ▸ Polynomial.degree_modByMonic_lt p hmon))

theorem solution (g₂ g₃ : ℂ) :
    ∀ (c : Fin 2) (V : Finset (Fin 4 → ℂ)) (n : V → ℕ),
      Function.Injective (fun v : V => v.val 0) →
      ∀ a : (v : V) → Fin (n v) → ℂ, ∃! p : Polynomial ℂ,
        p.degree < (∑ v : V, n v : ℕ) ∧
        ∀ (v : V) (k : Fin (n v)),
          MvPolynomial.eval v.val ((extensionChartDerivation g₂ g₃ c)^[k.val]
            (Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) p)) = a v k := by
  intro c V n hinj a
  simpa only [time_polynomial_jets] using hermite_unique (fun v : V => v.val 0) hinj n a

