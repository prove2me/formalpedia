-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.dI_localize
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:23:40.486281+00:00
-- url     : https://prove2.me/submissions/60c8d6ae-c7f2-476e-ad71-e4a331e24dcb

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Degree
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeIntA
import Theorems.Thm_ReciprocityTheory_AnForm_M_dI_transfer
import Theorems.Thm_ReciprocityTheory_AnForm_M_dI_chi_zero
import Theorems.Thm_ReciprocityTheory_AnForm_M_dI_bdd_mul

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
    {D : Fin A.n → (Fin e → ℂ) → ℝ} (hD : DIChartDens A D) (k : Fin A.n) (g : X → ℝ)
    (hg : ∀ x, x ∉ (A.chart k).source → g x = 0)
    (hint : IntegrableOn (fun z => g ((A.chart k).symm z) * D k z) (A.chart k).target) :
    (∀ j, IntegrableOn (fun y => P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * D j y)
      (A.chart j).target) ∧
    ∑ j, ∫ y in (A.chart j).target, P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * D j y =
      ∫ z in (A.chart k).target, g ((A.chart k).symm z) * D k z := by
  have hfk : ∀ j, IntegrableOn (fun z => P.χ j ((A.chart k).symm z) * g ((A.chart k).symm z) *
      D k z) (A.chart k).target := by
    intro j
    have := dI_bdd_mul A P j k hint
    simpa only [mul_assoc] using this
  have hT : ∀ j, IntegrableOn (fun y => P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) *
        D j y) (A.chart j).target ∧
      ∫ y in (A.chart j).target, P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * D j y =
        ∫ z in (A.chart k).target, P.χ j ((A.chart k).symm z) * g ((A.chart k).symm z) *
          D k z := by
    intro j
    obtain ⟨h1, h2⟩ := dI_transfer A hD k j (fun x => P.χ j x * g x)
      (fun x hx => by simp [hg x hx]) (hfk j)
    refine ⟨h1, h2.trans ?_⟩
    symm
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (A.chart k).open_target.measurableSet
      Set.inter_subset_left ?_
    rintro z ⟨hz, hzU⟩
    have : (A.chart k).symm z ∉ (A.chart j).source := fun h => hzU ⟨hz, h⟩
    simp [dI_chi_zero A P j this]
  refine ⟨fun j => (hT j).1, ?_⟩
  rw [Finset.sum_congr rfl (fun j _ => (hT j).2), ← integral_finsetSum _ (fun j _ => hfk j)]
  refine setIntegral_congr_fun (A.chart k).open_target.measurableSet (fun y _ => ?_)
  rw [← Finset.sum_mul, ← Finset.sum_mul, P.sum_eq_one, one_mul]
end ReciprocityTheory.AnForm.M
