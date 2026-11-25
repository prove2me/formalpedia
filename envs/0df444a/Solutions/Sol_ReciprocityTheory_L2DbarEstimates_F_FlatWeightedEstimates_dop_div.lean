-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates.dop_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:02:40.11717+00:00
-- url     : https://prove2.me/submissions/ed1dd628-c562-4579-93bc-16054b8860bc

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollifierL2LocTendsto
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_IntegrableFd
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_FlatWeightedEstimates_wd_eq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_FlatWeightedEstimates_reindex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
open ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates
namespace ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates
theorem _root_.solution {n : ℕ} (h : Fin n → V n → ℂ) (y : V n) :
    B.Dop (cD n) (vD n) (fun p => h (finProdFinEquiv.symm p).1) y = ∑ j, wd n j (h j) y := by
  have := reindex (n := n) (fun q => ![(1 : ℂ) / 2, -Complex.I / 2] q.2 *
    fderiv ℝ (h q.1) y (![bas n q.1, Complex.I • bas n q.1] q.2))
  exact this.trans (Finset.sum_congr rfl fun j _ => by simp [wd_eq])
end ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates
