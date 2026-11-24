-- Prove2me | solution 1 for PI.FJMB.deriv_aeval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:41.319796+00:00
-- url     : https://prove2.me/submissions/338c4811-e18a-41c2-912e-9c96b15daa26

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurChain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MvPolynomial
namespace PI.FJMB
variable {R : Type*} [CommRing R] {σ : Type*}
private theorem sum_aeval_pderiv_X_mul_derivation {B : Type*} [CommRing B] [Algebra R B] (D : Derivation R B B)
    (φ : σ → B) (S : Finset σ) (hS : ∀ v, v ∉ S → D (φ v) = 0) (w : σ) :
    ∑ v ∈ S, aeval φ (pderiv v (X w : MvPolynomial σ R)) * D (φ v) = D (φ w) := by
  classical
  have key : ∀ v, aeval φ (pderiv v (X w : MvPolynomial σ R)) * D (φ v) =
      if w = v then D (φ v) else 0 := by
    intro v
    rw [pderiv_X]
    by_cases h : w = v
    · subst h
      simp
    · simp [Pi.single_apply, h]
  rw [Finset.sum_congr rfl (fun v _ => key v), Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · exact (hS w h).symm
end PI.FJMB
end
end

set_option autoImplicit false
noncomputable section
open MvPolynomial
open PI PI.FJMB
variable {R : Type*} [CommRing R] {σ : Type*}
namespace PI.FJMB
theorem _root_.solution {B : Type*} [CommRing B] [Algebra R B] (D : Derivation R B B) (φ : σ → B)
    (S : Finset σ) (hS : ∀ v, v ∉ S → D (φ v) = 0) (f : MvPolynomial σ R) :
    D (aeval φ f) = ∑ v ∈ S, aeval φ (pderiv v f) * D (φ v) := by
  classical
  induction f using MvPolynomial.induction_on
  · rename_i a
    simp [aeval_C]
  · rename_i p q hp hq
    simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  · rename_i p w hp
    have h1 : ∀ v, pderiv v (p * X w) = pderiv v p * X w + p * pderiv v (X w) := by
      intro v
      simp only [Derivation.leibniz, smul_eq_mul]
      ring
    simp only [h1, map_add, map_mul, aeval_X, add_mul, Finset.sum_add_distrib]
    have h2 : ∑ v ∈ S, aeval φ p * aeval φ (pderiv v (X w : MvPolynomial σ R)) * D (φ v) =
        aeval φ p * D (φ w) := by
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, sum_aeval_pderiv_X_mul_derivation D φ S hS w]
    have h3 : ∑ v ∈ S, aeval φ (pderiv v p) * φ w * D (φ v) =
        φ w * ∑ v ∈ S, aeval φ (pderiv v p) * D (φ v) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun v _ => by ring)
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, h2, h3, ← hp]
    ring
end PI.FJMB
