-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.WD_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:47:31.027493+00:00
-- url     : https://prove2.me/submissions/d8169427-27a0-415b-b8e3-850b396135e3

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContDiffOnSecondCayleyBlockEntries
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_Cinv_mul_Cm

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
theorem _root_.solution (Q R Q' R' : Matrix (Fin n) (Fin n) ℂ) :
    (Cm n * fromBlocks 0 Q R 0 * (Cm n)⁻¹) * (Cm n * fromBlocks 0 Q' R' 0 * (Cm n)⁻¹) =
      Cm n * fromBlocks (Q * R') 0 0 (R * Q') * (Cm n)⁻¹ := by
  have e : (Cm n * fromBlocks 0 Q R 0 * (Cm n)⁻¹) * (Cm n * fromBlocks 0 Q' R' 0 * (Cm n)⁻¹) =
      Cm n * (fromBlocks 0 Q R 0 * ((Cm n)⁻¹ * Cm n) * fromBlocks 0 Q' R' 0) * (Cm n)⁻¹ := by
    simp only [Matrix.mul_assoc]
  rw [e, Cinv_mul_Cm, mul_one, Matrix.fromBlocks_multiply]
  simp
end PositivityTheory.Rg.Sw.LVs
