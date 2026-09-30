-- Prove2me | solution 1 for WeierstrassEllipticZeta.elliptic_extension_contact_quotient_dimension
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T21:56:31.013906+00:00
-- url     : https://prove2.me/submissions/6c671591-8c2d-4371-a027-ba786b03f00f

import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_contact_ideal_structure
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Tactic.FinCases

noncomputable section
open MvPolynomial
open WeierstrassEllipticZeta

private lemma chart_derivation_time (g₂ g₃ : ℂ) (c : Fin 2) :
    extensionChartDerivation g₂ g₃ c (X (0 : Fin 4)) = 1 := by
  fin_cases c <;> simp [extensionChartDerivation]

private lemma time_polynomial_iterate (g₂ g₃ : ℂ) (c : Fin 2)
    (p : Polynomial ℂ) (k : ℕ) :
    (extensionChartDerivation g₂ g₃ c)^[k] (Polynomial.aeval (X (0 : Fin 4)) p) =
      Polynomial.aeval (X (0 : Fin 4)) (Polynomial.derivative^[k] p) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, Derivation.comp_aeval_eq,
      chart_derivation_time, smul_eq_mul, mul_one, Function.iterate_succ_apply']

private lemma time_jet_monomial (g₂ g₃ : ℂ) (c : Fin 2) (v : Fin 4 → ℂ) (i k : ℕ) :
    eval v ((extensionChartDerivation g₂ g₃ c)^[k] ((X (0 : Fin 4) - C (v 0)) ^ i)) =
      if k = i then (i.factorial : ℂ) else 0 := by
  have hp : (X (0 : Fin 4) - C (v 0)) ^ i = Polynomial.aeval (X (0 : Fin 4))
      ((Polynomial.X - Polynomial.C (v 0)) ^ i) := by simp
  rw [hp, time_polynomial_iterate, Polynomial.iterate_derivative_X_sub_pow]
  simp only [map_nsmul, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
    eval_X]
  by_cases h : k = i
  · subst k
    simp [Nat.descFactorial_self]
  · rw [if_neg h]
    by_cases hi : i < k
    · simp [Nat.descFactorial_eq_zero_iff_lt.mpr hi]
    · simp [Nat.ne_of_gt (show 0 < i - k by omega)]

private lemma jets_surjective (g₂ g₃ : ℂ) (c : Fin 2) (v : Fin 4 → ℂ) (n : ℕ) :
    Function.Surjective (fun p : MvPolynomial (Fin 4) ℂ => fun k : Fin n =>
      eval v ((extensionChartDerivation g₂ g₃ c)^[k.val] p)) := by
  classical
  intro a
  refine ⟨∑ i : Fin n, (a i / (i.val.factorial : ℂ)) • (X (0 : Fin 4) - C (v 0)) ^ i.val, ?_⟩
  funext k
  have hs : eval v ((extensionChartDerivation g₂ g₃ c)^[k.val]
      (∑ i : Fin n, (a i / (i.val.factorial : ℂ)) • (X (0 : Fin 4) - C (v 0)) ^ i.val)) =
      ∑ i : Fin n, (a i / (i.val.factorial : ℂ)) *
        eval v ((extensionChartDerivation g₂ g₃ c)^[k.val] ((X (0 : Fin 4) - C (v 0)) ^ i.val)) := by
    simpa only [Module.End.pow_apply] using!
      (show eval v (((extensionChartDerivation g₂ g₃ c).toLinearMap ^ k.val)
        (∑ i : Fin n, (a i / (i.val.factorial : ℂ)) • (X (0 : Fin 4) - C (v 0)) ^ i.val)) =
        ∑ i : Fin n, (a i / (i.val.factorial : ℂ)) *
          eval v (((extensionChartDerivation g₂ g₃ c).toLinearMap ^ k.val)
            ((X (0 : Fin 4) - C (v 0)) ^ i.val)) by
        simp only [map_sum, map_smul]
        simp [smul_eq_C_mul])
  apply hs.trans
  simp_rw [time_jet_monomial, ← Fin.ext_iff, mul_ite, mul_zero]
  simp [Nat.factorial_ne_zero]

theorem solution (g₂ g₃ : ℂ) :
    ∀ (c : Fin 2) (V : Finset (Fin 4 → ℂ)) (n : V → ℕ),
      FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸
        ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸
        ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)) = ∑ v : V, n v ∧
      ∀ a : (v : V) → Fin (n v) → ℂ, ∃ p : MvPolynomial (Fin 4) ℂ,
        ∀ (v : V) (k : Fin (n v)),
          eval v.val ((extensionChartDerivation g₂ g₃ c)^[k.val] p) = a v k := by
  classical
  intro c V n
  have hc := elliptic_extension_contact_ideal_structure g₂ g₃
  let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
    ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)
  let E : MvPolynomial (Fin 4) ℂ →ₗ[ℂ] ((v : V) → Fin (n v) → ℂ) :=
    LinearMap.pi fun v => LinearMap.pi fun k =>
      (MvPolynomial.aeval v.val).toLinearMap.comp
        ((extensionChartDerivation g₂ g₃ c).toLinearMap ^ k.val)
  have hsurj : Function.Surjective E := by
    intro a
    choose p hp using fun v : V => jets_surjective g₂ g₃ c v.val (n v) (a v)
    obtain ⟨q, hq⟩ := hc.2.2.2.2.2.2 c V n p
    refine ⟨q, ?_⟩
    funext v k
    have hz := (hc.1 c v.val (n v) (q - p v)).mp (hq v) k.val k.isLt
    have hlin : eval v.val (((extensionChartDerivation g₂ g₃ c).toLinearMap ^ k.val)
        (q - p v)) = 0 := by simpa only [Module.End.pow_apply] using! hz
    simp only [map_sub] at hlin
    have hpv := congrFun (hp v) k
    exact (sub_eq_zero.mp hlin).trans (by simpa only [Module.End.pow_apply] using! hpv)
  have hker : LinearMap.ker E = I.restrictScalars ℂ := by
    ext p
    change E p = 0 ↔ p ∈ (⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v))
    simp only [Submodule.mem_iInf]
    constructor
    · intro hp v
      apply (hc.1 c v.val (n v) p).mpr
      intro k hk
      have h := congrFun (congrFun hp v) ⟨k, hk⟩
      simpa only [E, LinearMap.pi_apply, LinearMap.comp_apply,
        AlgHom.toLinearMap_apply, Module.End.pow_apply, Pi.zero_apply] using! h
    · intro hp
      funext v k
      have h := (hc.1 c v.val (n v) p).mp (hp v) k.val k.isLt
      simpa only [E, LinearMap.pi_apply, LinearMap.comp_apply,
        AlgHom.toLinearMap_apply, Module.End.pow_apply, Pi.zero_apply] using! h
  let e : (MvPolynomial (Fin 4) ℂ ⧸ I) ≃ₗ[ℂ] ((v : V) → Fin (n v) → ℂ) :=
    (Submodule.quotEquivOfEq (I.restrictScalars ℂ) (LinearMap.ker E) hker.symm).trans
      (E.quotKerEquivOfSurjective hsurj)
  refine ⟨FiniteDimensional.of_injective e.toLinearMap e.injective, ?_, ?_⟩
  · change Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) = _
    rw [e.finrank_eq, Module.finrank_pi_fintype]
    simp
  · intro a
    obtain ⟨p, hp⟩ := hsurj a
    refine ⟨p, fun v k => ?_⟩
    have h := congrFun (congrFun hp v) k
    simpa only [E, LinearMap.pi_apply, LinearMap.comp_apply,
      AlgHom.toLinearMap_apply, Module.End.pow_apply] using! h

