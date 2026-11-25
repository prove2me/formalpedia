-- Prove2me | solution 1 for PositivityTheory.CW.AdjointWordFiltration.word_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:25:03.796722+00:00
-- url     : https://prove2.me/submissions/602c4f6b-81fa-4495-b001-599ca709179a

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
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ V) (l : List (Fin n × Fin n)) :
    (l.map fun p => E p.1 p.2).prod ∈ U E l.length :=
  Submodule.subset_span ⟨l, le_rfl, rfl⟩
end PositivityTheory.CW.AdjointWordFiltration
