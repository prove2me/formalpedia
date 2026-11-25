-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_JacobianAtCurvePoint_exists_mul_mem_of_algebraMap_mem_ad35f2d7d286
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:30:50.982277+00:00
-- url     : https://prove2.me/submissions/42cb042b-04c0-47d0-b348-a74a67445499

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GradientAtPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelPlace
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_SmoothOfRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_JacobianAtCurvePoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial IsLocalRing GradientAtPoint
noncomputable section
open GroundTheory.Heights₂.Heights.JacobianAtCurvePoint
variable {σ : Type}
namespace GroundTheory.Heights₂.Heights.JacobianAtCurvePoint
theorem _root_.solution (w : σ → ℂ) (J : Ideal (MvPolynomial σ ℂ)) (x : MvPolynomial σ ℂ)
    (hx : algebraMap _ (ptLoc w) x ∈ J.map (algebraMap _ (ptLoc w))) :
    ∃ s : MvPolynomial σ ℂ, eval w s ≠ 0 ∧ s * x ∈ J := by
  obtain ⟨⟨y, s⟩, hys⟩ := (IsLocalization.mem_map_algebraMap_iff (ptMax w).primeCompl _).1 hx
  rw [← map_mul] at hys
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (ptMax w).primeCompl _).1 hys
  refine ⟨(c : MvPolynomial σ ℂ) * s, ?_, ?_⟩
  · have h := (ptMax w).primeCompl.mul_mem c.2 s.2
    intro h0
    exact h (RingHom.mem_ker.2 h0)
  · rw [show (c : MvPolynomial σ ℂ) * s * x = c * (x * s) by ring, hc]
    exact J.mul_mem_left _ y.2
end GroundTheory.Heights₂.Heights.JacobianAtCurvePoint
