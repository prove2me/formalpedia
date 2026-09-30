-- Prove2me | solution 1 for WeierstrassEllipticZeta.finite_contact_quotient_polynomial_product
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T02:11:15.723264+00:00
-- url     : https://prove2.me/submissions/a51b44f5-7731-41db-a01a-e3c6ad69a40c

import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_contact_ideal_structure
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_bounded_hermite_interpolation
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Tactic.FinCases

noncomputable section
open WeierstrassEllipticZeta

private lemma jet_model_time_jets (g₂ g₃ : ℂ) (c : Fin 2)
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

private lemma jet_model_root_divisibility (x : ℂ) (p : Polynomial ℂ) (n : ℕ) :
    (Polynomial.X - Polynomial.C x) ^ n ∣ p ↔
      ∀ k < n, (Polynomial.derivative^[k] p).eval x = 0 := by
  rw [Polynomial.X_sub_C_pow_dvd_iff, Polynomial.X_pow_dvd_iff]
  have h (k : ℕ) : (Polynomial.derivative^[k] p).eval x =
      (k.factorial : ℂ) * (Polynomial.taylor x p).coeff k := by
    rw [← Polynomial.factorial_smul_hasseDeriv]
    simp [Polynomial.taylor_coeff, nsmul_eq_mul]
  simp_rw [h, mul_eq_zero, Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _),
    false_or, Polynomial.taylor_apply]

private lemma local_contact_polynomial_algebra (g₂ g₃ : ℂ) (c : Fin 2)
    (v : Fin 4 → ℂ) (n : ℕ) :
    Nonempty ((MvPolynomial (Fin 4) ℂ ⧸ extensionChartContactIdeal g₂ g₃ c v n) ≃ₐ[ℂ]
      (Polynomial ℂ ⧸ Ideal.span {(Polynomial.X - Polynomial.C (v 0)) ^ n})) := by
  classical
  have hc := elliptic_extension_contact_ideal_structure g₂ g₃
  let J := extensionChartContactIdeal g₂ g₃ c v n
  let M := (Polynomial.X - Polynomial.C (v 0)) ^ n
  let E : Polynomial ℂ →ₐ[ℂ] MvPolynomial (Fin 4) ℂ :=
    Polynomial.aeval (MvPolynomial.X (0 : Fin 4))
  let ψ := (Ideal.Quotient.mkₐ ℂ J).comp E
  have hker : RingHom.ker ψ.toRingHom = Ideal.span {M} := by
    ext q
    change Ideal.Quotient.mk J (E q) = 0 ↔ q ∈ Ideal.span {M}
    rw [Ideal.Quotient.eq_zero_iff_mem, hc.1 c v n, Ideal.mem_span_singleton]
    simpa only [E, M, jet_model_time_jets] using (jet_model_root_divisibility (v 0) q n).symm
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ J y
    let V : Finset (Fin 4 → ℂ) := {v}
    have hv : v ∈ V := Finset.mem_singleton_self v
    have hinj : Function.Injective (fun w : V => w.val 0) := by
      intro a b _
      exact Subtype.ext ((Finset.mem_singleton.mp a.prop).trans
        (Finset.mem_singleton.mp b.prop).symm)
    obtain ⟨q, hq, _⟩ := elliptic_extension_bounded_hermite_interpolation g₂ g₃ c V
      (fun _ => n) hinj (fun w k =>
        MvPolynomial.eval w.val ((extensionChartDerivation g₂ g₃ c)^[k.val] p))
    refine ⟨q, ?_⟩
    change Ideal.Quotient.mk J (E q) = Ideal.Quotient.mk J p
    apply Ideal.Quotient.eq.mpr
    apply (hc.1 c v n (E q - p)).mpr
    intro j hj
    have hsub : (extensionChartDerivation g₂ g₃ c)^[j] (E q - p) =
        (extensionChartDerivation g₂ g₃ c)^[j] (E q) -
          (extensionChartDerivation g₂ g₃ c)^[j] p := by
      simpa only [Module.End.pow_apply] using!
        ((extensionChartDerivation g₂ g₃ c).toLinearMap ^ j).map_sub (E q) p
    rw [hsub, map_sub, sub_eq_zero]
    exact hq.2 ⟨v, hv⟩ ⟨j, hj⟩
  exact ⟨(Ideal.quotientKerAlgEquivOfSurjective hsurj).symm.trans
    (Ideal.quotientEquivAlgOfEq ℂ hker)⟩

theorem solution (g₂ g₃ : ℂ) (c : Fin 2)
    (V : Finset (Fin 4 → ℂ)) (n : V → ℕ) :
    Nonempty ((MvPolynomial (Fin 4) ℂ ⧸
      (⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v))) ≃ₐ[ℂ]
        ((v : V) → Polynomial ℂ ⧸ Ideal.span {(Polynomial.X - Polynomial.C (v.val 0)) ^ n v})) := by
  classical
  have hc := elliptic_extension_contact_ideal_structure g₂ g₃
  let C : V → Ideal (MvPolynomial (Fin 4) ℂ) := fun v =>
    extensionChartContactIdeal g₂ g₃ c v.val (n v)
  have hcoprime : Pairwise (fun v w => IsCoprime (C v) (C w)) := by
    intro v w hne
    exact Ideal.isCoprime_iff_sup_eq.mpr
      (hc.2.2.2.2.1 c v.val w.val (fun h => hne (Subtype.ext h)) (n v) (n w))
  let crt : (MvPolynomial (Fin 4) ℂ ⧸ ⨅ v : V, C v) ≃ₐ[ℂ]
      ((v : V) → MvPolynomial (Fin 4) ℂ ⧸ C v) :=
    { Ideal.quotientInfRingEquivPiQuotient C hcoprime with
      commutes' := fun z => rfl }
  exact ⟨crt.trans (AlgEquiv.piCongrRight (fun v : V =>
    Classical.choice (local_contact_polynomial_algebra g₂ g₃ c v.val (n v))))⟩

