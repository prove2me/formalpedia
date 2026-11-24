-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ArithVariety_whole_mkF_injective_f0f5f10d0d70
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:51:58.033409+00:00
-- url     : https://prove2.me/submissions/446f0a52-83b2-47b1-aebb-3fc791836122

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mkF_eq_zero_iff_91580b64c057


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
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]
open GroundTheory.Heights₂.Heights.ArithVariety
variable (n : ι → ℕ)
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights.ArithVariety
theorem _root_.solution : Function.Injective (whole n).mkF := by
  refine (injective_iff_map_eq_zero _).mpr fun f hf ↦ ?_
  exact (Submodule.mem_bot _).mp (((whole n).mkF_eq_zero_iff f).mp hf)
end GroundTheory.Heights₂.Heights.ArithVariety
