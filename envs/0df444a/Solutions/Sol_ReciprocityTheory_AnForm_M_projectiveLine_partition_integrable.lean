-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.projectiveLine_partition_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:45:03.565087+00:00
-- url     : https://prove2.me/submissions/ea2b6d32-f20a-4db7-9f17-30c8e2b9b16f

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegralIoiFsDensRadial
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ProjectiveLinePartitionContinuousCoe
import Theorems.Thm_ReciprocityTheory_AnForm_M_projectiveLine_partition_continuous_coe
import Theorems.Thm_ReciprocityTheory_AnForm_integrable_fsDens


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory OnePoint Filter Topology Set
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (P : ChartPartition p1) (j : Fin p1.n) :
    Integrable fun u : ℂ => P.χ j (u : OnePoint ℂ) * fsDens u := by
  refine integrable_fsDens.bdd_mul (c := 1) (projectiveLine_partition_continuous_coe P j).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (P.nonneg j _), ← P.sum_eq_one (u : OnePoint ℂ)]
  exact Finset.single_le_sum (fun i _ => P.nonneg i _) (Finset.mem_univ j)
end ReciprocityTheory.AnForm.M
