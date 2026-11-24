-- Prove2me | solution 1 for PositivityTheory.CW.IdentityFiltrationBound.N_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:38:46.192962+00:00
-- url     : https://prove2.me/submissions/7645ecf6-ae31-4364-a427-43e8582904eb

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
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ V) (k : ℕ) (v : V) : 0 ≤ N E k v :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _
end PositivityTheory.CW.IdentityFiltrationBound
