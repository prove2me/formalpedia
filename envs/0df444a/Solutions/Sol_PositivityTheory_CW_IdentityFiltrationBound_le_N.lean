-- Prove2me | solution 1 for PositivityTheory.CW.IdentityFiltrationBound.le_N
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:44:49.408873+00:00
-- url     : https://prove2.me/submissions/cdef4338-360c-4d3d-b617-a90433fb5e41

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_EnvelopingAlgebraGrowthBound
import Theorems.Thm_PositivityTheory_CW_IdentityFiltrationBound_mem_W

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
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ V) {k : ℕ} {l : List (Fin n × Fin n)} (hl : l.length ≤ k)
    (v : V) : ‖wd E l v‖ ≤ N E k v :=
  Finset.single_le_sum (f := fun l => ‖wd E l v‖) (fun _ _ => norm_nonneg _) (mem_W.2 hl)
end PositivityTheory.CW.IdentityFiltrationBound
