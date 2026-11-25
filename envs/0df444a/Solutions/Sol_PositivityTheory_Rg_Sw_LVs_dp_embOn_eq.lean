-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.dp_embOn_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:56:05.507455+00:00
-- url     : https://prove2.me/submissions/646981ac-359c-4f89-9ed0-746b9e616e19

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DpDual
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_incl_mul_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_mul_proj_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ContDiff ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution (s : Finset (Fin n)) (T : Matrix s s ℂ) : embOn s T = dp_incl s * (T * proj s) := by
  ext a b
  rw [incl_mul_apply]
  by_cases ha : a ∈ s
  · rw [dif_pos ha, mul_proj_apply]
    by_cases hb : b ∈ s
    · rw [dif_pos hb, embOn, dif_pos ⟨ha, hb⟩]
    · rw [dif_neg hb, embOn, dif_neg (fun h => hb h.2)]
  · rw [dif_neg ha, embOn, dif_neg (fun h => ha h.1)]
end PositivityTheory.Rg.Sw.LVs
