-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_smoothNear_log_dualNorm_slice_70443648dabb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:58.055792+00:00
-- url     : https://prove2.me/submissions/338cbdae-409d-46dc-ab98-63abb5431d5f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceSectionMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceExhaustion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceSectionMass
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiffOn_log_dualNorm_a92d55d266bf

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
open MvPolynomial Filter Topology Matrix ComplexSets
open scoped ContDiff
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (ℓ : Fin n → ℂ) :
    SmoothNear (zeroSet (J ⊔ Ideal.span {linForm ℓ - 1})) fun x => Real.log (h.dualNorm x) := by
  refine ⟨{0}ᶜ, isOpen_compl_singleton, fun x hx hx0 => ?_, contDiffOn_log_dualNorm h⟩
  have := hx _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  rw [Set.mem_singleton_iff] at hx0
  subst hx0
  simp [linForm] at this
end GroundTheory.Heights₂.Heights
