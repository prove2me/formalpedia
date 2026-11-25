-- Prove2me | solution 1 for PositivityTheory.CW.AdjointWordFiltration.U_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:22:07.469853+00:00
-- url     : https://prove2.me/submissions/3275a980-f240-4eb4-9a9b-bd941f2ef38e

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_CasimirPowerCommute

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.AdjointWordFiltration
variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace PositivityTheory.CW.AdjointWordFiltration
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ V) {j k : ℕ} (h : j ≤ k) : U E j ≤ U E k := by
  unfold U
  apply Submodule.span_mono
  rintro x ⟨l, hl, rfl⟩
  exact ⟨l, hl.trans h, rfl⟩
end PositivityTheory.CW.AdjointWordFiltration
