-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_compAt_restrictTo_3d6cb5d193c4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:39:39.146572+00:00
-- url     : https://prove2.me/submissions/dfdaa2f8-f780-41c8-9854-55351ac399ea

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PTruncation
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_compAt_singleV_same_f213c9cf28ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_compAt_singleV_ne_0b8ca46ce283

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA
open Classical
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]
namespace GroundTheory.Heights₂.Heights.StrongApprox
theorem _root_.solution (S : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F))
    (a : AE F E) : compAt E v (restrictTo E S a) = if v ∈ S then compAt E v a else 0 := by
  rw [restrictTo, map_sum]
  split_ifs with hv
  · rw [Finset.sum_eq_single_of_mem v hv (fun w _ hw => compAt_singleV_ne hw.symm _),
      compAt_singleV_same]
  · exact Finset.sum_eq_zero fun w hw => compAt_singleV_ne (by rintro rfl; exact hv hw) _
end GroundTheory.Heights₂.Heights.StrongApprox
