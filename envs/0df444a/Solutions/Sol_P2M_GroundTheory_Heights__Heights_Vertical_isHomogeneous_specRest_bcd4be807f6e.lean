-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_isHomogeneous_specRest_bcd4be807f6e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:36.115432+00:00
-- url     : https://prove2.me/submissions/af3b5e8a-42f3-4746-806d-3e6fc032c9e2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormFormEval
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChowSecDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {n e d : ℕ}
    {g : MvPolynomial (Fin (e + 1) × Fin n) R} (hg : IsMultiHomog d g) (y : Par e n → S) :
    (specRest φ g y).IsHomogeneous d := by
  classical
  rw [specRest, g.as_sum, eval₂_sum]
  refine IsHomogeneous.sum _ _ _ fun m hm => ?_
  rw [eval₂_monomial, Finsupp.prod]
  have hdeg : ∀ ij : Fin (e + 1) × Fin n,
      (Fin.cases (motive := fun _ => MvPolynomial (Fin n) S) (X ij.2)
        (fun i => C (y (.inl (i, ij.2)))) ij.1 : MvPolynomial (Fin n) S).IsHomogeneous
        (groupWeight (e + 1) n ij 0) := by
    rintro ⟨i, j⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa [groupWeight] using isHomogeneous_X (R := S) j
    · have h0 : groupWeight (e + 1) n (i.succ, j) 0 = 0 := by simp [groupWeight]
      rw [h0]
      exact isHomogeneous_C _ _
  have hsum : ∑ ij ∈ m.support, groupWeight (e + 1) n ij 0 * m ij = d := by
    have hw := hg (mem_support_iff.mp hm)
    have h0 := congrFun hw 0
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun ij _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_comm]
  have h := (isHomogeneous_C (σ := Fin n) (φ (coeff m g))).mul
    (IsHomogeneous.prod m.support _ _ fun ij _ => (hdeg ij).pow (m ij))
  rw [zero_add, hsum] at h
  exact h
end GroundTheory.Heights₂.Heights.Vertical
