-- Prove2me | solution 1 for PI.ExistsGaugeMeasureForEachRank.W.col_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:14:29.24301+00:00
-- url     : https://prove2.me/submissions/76b25f85-ce4a-4fc6-9302-c96c40333d41

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExistsGaugeMeasureForEachRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_DglApplyOff

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
open PI PI.ExistsGaugeMeasureForEachRank PI.ExistsGaugeMeasureForEachRank.W
variable {r : ℕ}
namespace PI.ExistsGaugeMeasureForEachRank.W
theorem _root_.solution {g : Mat 0 r} (hg : g ∈ UWb 0 r) (j : Fin (2 * r + 0 + 1)) (hj : j ≠ cI r)
    (i : Fin (2 * r + 0 + 1)) : g i j = if i = j then 1 else 0 := by
  have hjl := j.isLt
  have hcol : g *ᵥ bvec j = bvec j := by
    rcases lt_or_gt_of_ne (show j.val ≠ r from fun h => hj (Fin.ext h)) with h | h
    · have := (hg.2 ⟨j.val, h⟩).1
      have e : eI 0 r ⟨j.val, h⟩ = j := Fin.ext rfl
      rwa [e] at this
    · have := (hg.2 ⟨2 * r - j.val, by omega⟩).2
      have e : esI 0 r ⟨2 * r - j.val, by omega⟩ = j := Fin.ext (by simp [esI]; omega)
      rwa [e] at this
  have := congrFun hcol i
  rw [bvec, Matrix.mulVec_single_one, Pi.single_apply] at this
  simpa [Matrix.col] using this
end PI.ExistsGaugeMeasureForEachRank.W
