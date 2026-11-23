-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.dI_target_of_weights
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:26.654078+00:00
-- url     : https://prove2.me/submissions/0660fe3a-97ef-4434-a401-49ba45833c34

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Degree
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeIntA
import Theorems.Thm_ReciprocityTheory_AnForm_M_dI_transfer
import Theorems.Thm_ReciprocityTheory_AnForm_M_dI_chi_zero

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
theorem _root_.solution (A : FinHolAtlas e X) (P : ChartPartition A)
    {D : Fin A.n → (Fin e → ℂ) → ℝ} (hD : DIChartDens A D) (g : X → ℝ)
    (hw : ∀ j, IntegrableOn (fun y => P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) *
      D j y) (A.chart j).target) (k : Fin A.n) :
    IntegrableOn (fun y => g ((A.chart k).symm y) * D k y) (A.chart k).target := by
  have hj : ∀ j, IntegrableOn (fun y => P.χ j ((A.chart k).symm y) * g ((A.chart k).symm y) *
      D k y) (A.chart k).target := fun j =>
    (dI_transfer A hD j k (fun x => P.χ j x * g x)
      (fun x hx => by simp [dI_chi_zero A P j hx]) (hw j)).1
  have := integrable_finsetSum Finset.univ
    (f := fun j y => P.χ j ((A.chart k).symm y) * g ((A.chart k).symm y) * D k y)
    (fun j _ => hj j)
  refine IntegrableOn.congr_fun this (fun y _ => ?_) (A.chart k).open_target.measurableSet
  rw [← Finset.sum_mul, ← Finset.sum_mul, P.sum_eq_one, one_mul]
end ReciprocityTheory.AnForm.M
