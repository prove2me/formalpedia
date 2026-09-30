-- Prove2me | solution 1 for WeierstrassEllipticZeta.elliptic_extension_local_intersection_multiplicities
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T23:22:20.667329+00:00
-- url     : https://prove2.me/submissions/49bceb76-0d1a-4fd6-84c1-4b51f98aaf50

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveContactIdeal
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.Tactic.FinCases

noncomputable section
open WeierstrassEllipticZeta

private lemma split_gcd_multiplicities {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (hx : Function.Injective x) (n : ι → ℕ) (q : Polynomial ℂ) :
    let M := ∏ i, (Polynomial.X - Polynomial.C (x i)) ^ n i
    ∃ e : ι → ℕ,
      (∀ i, e i ≤ n i ∧ ∀ k ≤ n i,
        k ≤ e i ↔ (Polynomial.X - Polynomial.C (x i)) ^ k ∣ q) ∧
      (gcd M q).natDegree = ∑ i, e i := by
  classical
  let M := ∏ i, (Polynomial.X - Polynomial.C (x i)) ^ n i
  have hM : M.Monic := Polynomial.monic_prod_of_monic _ _ fun i _ =>
    (Polynomial.monic_X_sub_C (x i)).pow (n i)
  have hroots : M.roots = Finset.univ.val.bind
      (fun i : ι => n i • ({x i} : Multiset ℂ)) := by
    rw [Polynomial.roots_prod _ _ hM.ne_zero]
    simp only [Polynomial.roots_pow, Polynomial.roots_X_sub_C]
  have hmult (i : ι) : M.rootMultiplicity (x i) = n i := by
    rw [← Polynomial.count_roots, hroots, Multiset.count_bind]
    change (∑ j, (n j • ({x j} : Multiset ℂ)).count (x i)) = n i
    simp [Multiset.count_singleton, hx.eq_iff]
  let G := gcd M q
  have hG : G ≠ 0 := by
    simp only [G, ne_eq, gcd_eq_zero_iff]
    exact fun h => hM.ne_zero h.1
  have hsplit : G.Splits :=
    (Polynomial.Splits.prod (fun i _ => (Polynomial.Splits.X_sub_C (x i)).pow (n i))).of_dvd
      hM.ne_zero (gcd_dvd_left M q)
  refine ⟨fun i => G.rootMultiplicity (x i), ?_, ?_⟩
  · intro i
    refine ⟨?_, ?_⟩
    · exact (Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hM.ne_zero
        (gcd_dvd_left M q) (x i)).trans_eq (hmult i)
    · intro k hk
      rw [Polynomial.le_rootMultiplicity_iff hG, dvd_gcd_iff]
      exact and_iff_right ((Polynomial.le_rootMultiplicity_iff hM.ne_zero).mp
        ((hmult i).symm ▸ hk))
  · rw [hsplit.natDegree_eq_card_roots]
    have hs : ∀ a ∈ G.roots, a ∈ Finset.univ.image x := by
      intro a ha
      have haM := Multiset.mem_of_le
        (Polynomial.roots.le_of_dvd hM.ne_zero (gcd_dvd_left M q)) ha
      rw [hroots, Multiset.mem_bind] at haM
      obtain ⟨i, _, hi⟩ := haM
      simp only [Multiset.mem_nsmul, Multiset.mem_singleton] at hi
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi.2.symm⟩
    rw [← Multiset.sum_count_eq_card hs, Finset.sum_image (fun i _ j _ h => hx h)]
    simp only [Polynomial.count_roots]

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

theorem solution
    (g₂ g₃ : ℂ) (c : Fin 2)
    (hcontact : ∀ (v : Fin 4 → ℂ) (n : ℕ) (p : MvPolynomial (Fin 4) ℂ),
      p ∈ extensionChartContactIdeal g₂ g₃ c v n ↔
        ∀ k < n, MvPolynomial.eval v ((extensionChartDerivation g₂ g₃ c)^[k] p) = 0)
    (V : Finset (Fin 4 → ℂ))
    (hV : Function.Injective (fun v : V => v.val 0)) (n : V → ℕ)
    (r : Fin 3 → Polynomial ℂ)
    (hmem : ∀ p : MvPolynomial (Fin 4) ℂ,
      p ∈ (⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)) ↔
        (∏ v : V, (Polynomial.X - Polynomial.C (v.val 0)) ^ n v) ∣
          MvPolynomial.aeval (Fin.cons Polynomial.X r) p) :
    ∀ p : MvPolynomial (Fin 4) ℂ, ∃ e : V → ℕ,
      (∀ v : V, e v ≤ n v ∧ ∀ k ≤ n v,
        k ≤ e v ↔ ∀ j < k,
          MvPolynomial.eval v.val ((extensionChartDerivation g₂ g₃ c)^[j] p) = 0) ∧
      (gcd (∏ v : V, (Polynomial.X - Polynomial.C (v.val 0)) ^ n v)
        (MvPolynomial.aeval (Fin.cons Polynomial.X r) p)).natDegree = ∑ v : V, e v := by
  classical
  intro p
  let φ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] Polynomial ℂ :=
    MvPolynomial.aeval (Fin.cons Polynomial.X r)
  let E : Polynomial ℂ →ₐ[ℂ] MvPolynomial (Fin 4) ℂ :=
    Polynomial.aeval (MvPolynomial.X (0 : Fin 4))
  have hE : φ.comp E = AlgHom.id ℂ (Polynomial ℂ) := by
    ext
    simp [φ, E]
  have hdiff : p - E (φ p) ∈
      (⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)) := by
    apply (hmem _).mpr
    change _ ∣ φ (p - E (φ p))
    have he : φ (E (φ p)) = φ p := AlgHom.congr_fun hE (φ p)
    rw [map_sub, he, sub_self]
    exact dvd_zero _
  obtain ⟨e, he, hsum⟩ := split_gcd_multiplicities (fun v : V => v.val 0) hV n (φ p)
  refine ⟨e, ?_, hsum⟩
  intro v
  refine ⟨(he v).1, ?_⟩
  have hzero := (hcontact v.val (n v) _).mp
    ((Submodule.mem_iInf _).mp hdiff v)
  have hjet (j : ℕ) (hj : j < n v) :
      MvPolynomial.eval v.val ((extensionChartDerivation g₂ g₃ c)^[j] p) =
        (Polynomial.derivative^[j] (φ p)).eval (v.val 0) := by
    have hz := hzero j hj
    have hsub : (extensionChartDerivation g₂ g₃ c)^[j] (p - E (φ p)) =
        (extensionChartDerivation g₂ g₃ c)^[j] p -
          (extensionChartDerivation g₂ g₃ c)^[j] (E (φ p)) := by
      simpa only [Module.End.pow_apply] using!
        ((extensionChartDerivation g₂ g₃ c).toLinearMap ^ j).map_sub p (E (φ p))
    rw [hsub, map_sub, sub_eq_zero] at hz
    exact hz.trans (time_polynomial_jets g₂ g₃ c v.val (φ p) j)
  intro k hk
  rw [(he v).2 k hk, root_power_dvd_iff_jets]
  exact forall₂_congr fun j hj => by rw [hjet j (hj.trans_le hk)]

