-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.dI_bdd_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:15:14.07316+00:00
-- url     : https://prove2.me/submissions/d445a0d6-07c7-4ce9-90c0-27325b91c5f8

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Degree
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeIntA
import Theorems.Thm_ReciprocityTheory_AnForm_M_dI_chi_le_one
import Theorems.Thm_ReciprocityTheory_AnForm_M_dI_chi_contOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (A : FinHolAtlas e X) (P : ChartPartition A) (j k : Fin A.n)
    {f : (Fin e → ℂ) → ℝ} (hf : IntegrableOn f (A.chart k).target) :
    IntegrableOn (fun y => P.χ j ((A.chart k).symm y) * f y) (A.chart k).target := by
  have hs : MeasurableSet (A.chart k).target := (A.chart k).open_target.measurableSet
  refine Integrable.bdd_mul (c := 1) hf ((dI_chi_contOn A P j k).aestronglyMeasurable hs) ?_
  exact Filter.Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (P.nonneg j _)]
    exact dI_chi_le_one A P j _
end ReciprocityTheory.AnForm.M
