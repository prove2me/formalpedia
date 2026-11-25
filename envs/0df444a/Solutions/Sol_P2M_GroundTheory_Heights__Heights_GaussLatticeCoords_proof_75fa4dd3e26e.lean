-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GaussLatticeCoords_proof_75fa4dd3e26e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:28:56.063873+00:00
-- url     : https://prove2.me/submissions/d7773c3c-eeca-4e8d-bc64-4e058fa7f9f2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussLatticeCoords
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussLatticeCoords_toLp_mulVec_intVec_383a4d247b59

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
open Matrix
open PGaussLatticeCoords
namespace GroundTheory.Heights₂.Heights
namespace GaussLatticeCoords
theorem _root_.solution : GaussLatticeCoords.Statement := by
  intro g B hB
  refine ⟨fun k => ?_, fun x hx => ?_, fun k k' hkk' => ?_⟩
  · rw [toLp_mulVec_intVec]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
    exact ⟨c, by rw [toLp_mulVec_intVec, hc]⟩
  · have hk : B *ᵥ intVec k = B *ᵥ intVec k' := hkk'
    have hu : IsUnit B.det := isUnit_iff_ne_zero.2 hB
    have hv : intVec k = intVec k' := by
      have := congrArg (fun v => B⁻¹ *ᵥ v) hk
      simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B hu, Matrix.one_mulVec] using this
    funext i
    exact Int.cast_injective (congrFun hv i)
end GaussLatticeCoords
end GroundTheory.Heights₂.Heights
