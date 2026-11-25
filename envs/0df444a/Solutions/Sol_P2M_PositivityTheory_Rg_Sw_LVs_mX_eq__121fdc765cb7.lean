-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Sw_LVs_mX_eq__121fdc765cb7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:04:46.533824+00:00
-- url     : https://prove2.me/submissions/61e5d5a2-cbd5-4b65-a6cd-4007920dd123

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContDiffOnSecondCayleyBlockEntries
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_Cm_mul_inv
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_fromBlocks_one_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution (Q R : Matrix (Fin n) (Fin n) ℂ) : mX 1 Q R 1 = 1 + Cm n * fromBlocks 0 Q R 0 * (Cm n)⁻¹ := by
  rw [mX, fromBlocks_one_eq, Matrix.mul_add, Matrix.add_mul, mul_one, Cm_mul_inv]
end PositivityTheory.Rg.Sw.LVs
