-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LinesIdealLatticeFG_proof_67d24ec7f127
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:21:10.240959+00:00
-- url     : https://prove2.me/submissions/0aee7221-e8b0-49bf-be3b-1726f648f408

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesIdealLatticeFG
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesIdealLatticeFG_fg_3ea39c9fb6fe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesIdealLatticeFG_single_mem_span_e985f142ac72

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
open NumberField
open scoped nonZeroDivisors
open KLinesIdealLatticeFG
namespace GroundTheory.Heights₂.Heights
namespace LinesIdealLatticeFG
theorem _root_.solution : LinesIdealLatticeFG.Statement := by
  intro K _ _ n a ha
  refine ⟨fg K a, ?_⟩
  refine eq_top_iff.mpr ?_
  rw [← (Pi.basisFun K (Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  rw [Pi.basisFun_apply]
  exact single_mem_span K a x (ha x)
end LinesIdealLatticeFG
end GroundTheory.Heights₂.Heights
