-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_M_mdisc_comp_perm__2bccc6921bd7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:50:13.432176+00:00
-- url     : https://prove2.me/submissions/0156725a-2332-4bf1-8aaf-12418d2b348c

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Filter Topology
open scoped ContDiff ComplexOrder
noncomputable section
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (M : Fin D → Matrix (Fin D) (Fin D) ℂ) (σ : Equiv.Perm (Fin D)) :
    mdisc (M ∘ σ) = mdisc M := by
  unfold mdisc
  congr 1
  exact Fintype.sum_equiv σ.finsetCongr _ _ fun S => by
    simp [Equiv.finsetCongr_apply, Finset.sum_map, Finset.card_map]
end ReciprocityTheory.AnForm.M
