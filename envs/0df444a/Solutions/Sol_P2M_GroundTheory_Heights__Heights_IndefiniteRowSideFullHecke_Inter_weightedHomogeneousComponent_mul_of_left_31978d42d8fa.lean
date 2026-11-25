-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_weightedHomogeneousComponent_mul_of_left_31978d42d8fa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:58:26.327111+00:00
-- url     : https://prove2.me/submissions/06c1b58d-cd47-425b-ba6a-e0d01471f1bb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleMultiHomogGrad

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial
variable {σ τ R M : Type*} [CommRing R] [AddCommMonoid M]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution {M : Type*} [AddCancelCommMonoid M] {w : σ → M}
    {c : MvPolynomial σ R} {m : M} (hc : IsWeightedHomogeneous w c m) (γ : M) (L : MvPolynomial σ R) :
    weightedHomogeneousComponent w (γ + m) (c * L) = c * weightedHomogeneousComponent w γ L := by
  classical
  induction L using MvPolynomial.induction_on' with
  | monomial d r =>
    have hd := isWeightedHomogeneous_monomial w d r (m := Finsupp.weight w d) rfl
    have hcd := hc.mul hd
    by_cases hdm : Finsupp.weight w d = γ
    · rw [(hdm ▸ hd : IsWeightedHomogeneous w (monomial d r) γ).weightedHomogeneousComponent_same]
      rw [show γ + m = m + Finsupp.weight w d by rw [hdm, add_comm]]
      exact hcd.weightedHomogeneousComponent_same
    · rw [hd.weightedHomogeneousComponent_ne γ (Ne.symm hdm), mul_zero]
      refine hcd.weightedHomogeneousComponent_ne _ fun h => hdm ?_
      rw [add_comm m] at h
      exact (add_right_cancel h).symm
  | add p q hp hq => simp only [mul_add, map_add, hp, hq]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
