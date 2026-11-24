-- Prove2me | solution 1 for PositivityTheory.CW.IdentityFiltrationBound.mem_W
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:33.353223+00:00
-- url     : https://prove2.me/submissions/c738c88d-9f8f-477d-b966-70eb17b62e9b

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_EnvelopingAlgebraGrowthBound

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
open PositivityTheory.CW.IdentityFiltrationBound
variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace PositivityTheory.CW.IdentityFiltrationBound
theorem _root_.solution {k : ℕ} {l : List (Fin n × Fin n)} : l ∈ W n k ↔ l.length ≤ k := by
  simp [W]
end PositivityTheory.CW.IdentityFiltrationBound
