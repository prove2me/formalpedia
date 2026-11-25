-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_regChartData_isCompact_univ_e3182ebcff2c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:38:04.12162+00:00
-- url     : https://prove2.me/submissions/13603e02-5f8a-41b4-bd39-1f49860793d3

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_KaehlerBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_PKaehlerBound
import Theorems.Thm_ReciprocityTheory_AnForm_continuousOn_levi
import Theorems.Thm_ReciprocityTheory_AnForm_levi_add_smul
import Theorems.Thm_ReciprocityTheory_AnForm_levi_comp
import Theorems.Thm_ReciprocityTheory_AnForm_levi_congr
import Theorems.Thm_ReciprocityTheory_AnForm_levi_re_analytic
import Theorems.Thm_ReciprocityTheory_AnForm_levi_smul_dir
import Theorems.Thm_ReciprocityTheory_AnForm_levi_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm (levi levi_congr levi_comp levi_zero levi_smul_dir levi_add_smul
  levi_re_analytic continuousOn_levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot chartIdx)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)
noncomputable section
namespace GroundTheory.Heights₂.Heights.AnalyticLimit
theorem _root_.solution {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}
    (R : RegChartData A) : IsCompact (Set.univ : Set X) := by
  have hK : ∀ j, IsCompact ((R.ψ j).symm '' closure (R.W'' j)) := fun j => by
    have hc : IsCompact (closure (R.W'' j)) :=
      (R.isCompact_closure_middle j).of_isClosed_subset isClosed_closure
        ((R.closure_W''_subset j).trans subset_closure)
    refine hc.image_of_continuousOn ((R.ψ j).continuousOn_symm.mono ?_)
    exact (R.closure_W''_subset j).trans (subset_closure.trans
      ((R.closure_W'_subset j).trans (R.W_subset j)))
  refine (isCompact_iUnion hK).of_isClosed_subset isClosed_univ fun x _ => ?_
  obtain ⟨j, hx, hxW⟩ := R.cover x
  exact Set.mem_iUnion.2 ⟨j, R.ψ j x, subset_closure hxW, (R.ψ j).left_inv hx⟩
end GroundTheory.Heights₂.Heights.AnalyticLimit
