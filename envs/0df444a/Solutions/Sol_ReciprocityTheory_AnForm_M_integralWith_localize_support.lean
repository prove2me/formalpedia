-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.integralWith_localize_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:16:04.000846+00:00
-- url     : https://prove2.me/submissions/18c0137e-0c06-42d1-984b-841336b9e7db

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Degree
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeIntB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeInt
import Theorems.Thm_ReciprocityTheory_AnForm_M_dI_chartDens_locDens
import Theorems.Thm_ReciprocityTheory_AnForm_M_dI_chi_contOn
import Theorems.Thm_ReciprocityTheory_AnForm_M_dI_chi_le_one
import Theorems.Thm_ReciprocityTheory_AnForm_M_dI_chi_zero
import Theorems.Thm_ReciprocityTheory_AnForm_M_dI_transfer


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
variable {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (P : ChartPartition A) (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i))
    (k : Fin A.n) (g : X → ℝ) (hg : ∀ x, x ∉ (A.chart k).source → g x = 0)
    (hint : IntegrableOn (fun z => g ((A.chart k).symm z) * locDens A Φ k z)
      (A.chart k).target) :
    (∀ j, IntegrableOn (fun y => P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) *
      locDens A Φ j y) (A.chart j).target) ∧
    integralWith A P Φ g = ∫ z in (A.chart k).target, g ((A.chart k).symm z) * locDens A Φ k z := by
  have hD := dI_chartDens_locDens A Φ hΦ
  have hk : ∀ j, IntegrableOn (fun y => P.χ j ((A.chart k).symm y) * g ((A.chart k).symm y) *
      locDens A Φ k y) (A.chart k).target := by
    intro j
    have hm : AEStronglyMeasurable (fun y => P.χ j ((A.chart k).symm y))
        (volume.restrict (A.chart k).target) :=
      (dI_chi_contOn A P j k).aestronglyMeasurable (A.chart k).open_target.measurableSet
    have hb : IntegrableOn (fun y => P.χ j ((A.chart k).symm y) *
        (g ((A.chart k).symm y) * locDens A Φ k y)) (A.chart k).target := by
      refine hint.norm.mono' (hm.mul hint.aestronglyMeasurable) (ae_of_all _ fun y => ?_)
      rw [norm_mul]
      refine mul_le_of_le_one_left (norm_nonneg _) ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (P.nonneg j _)]
      exact dI_chi_le_one A P j _
    simpa only [mul_assoc] using hb
  have htr := fun j => dI_transfer A hD k j (fun x => P.χ j x * g x)
    (fun x hx => by simp only [hg x hx, mul_zero]) (hk j)
  refine ⟨fun j => (htr j).1, ?_⟩
  have h2 : ∀ j, ∫ y in (A.chart j).target, P.χ j ((A.chart j).symm y) *
      g ((A.chart j).symm y) * locDens A Φ j y =
      ∫ y in (A.chart k).target, P.χ j ((A.chart k).symm y) * g ((A.chart k).symm y) *
        locDens A Φ k y := by
    intro j
    refine (htr j).2.trans ?_
    symm
    refine setIntegral_eq_of_subset_of_forall_diff_eq_zero
      (A.chart k).open_target.measurableSet Set.inter_subset_left ?_
    intro y hy
    have hys : (A.chart k).symm y ∉ (A.chart j).source := fun hs => hy.2 ⟨hy.1, hs⟩
    simp only [dI_chi_zero A P j hys, zero_mul]
  change ∑ j, ∫ y in (A.chart j).target, P.χ j ((A.chart j).symm y) *
      g ((A.chart j).symm y) * locDens A Φ j y = _
  rw [Finset.sum_congr rfl (fun j _ => h2 j),
    ← integral_finset_sum Finset.univ (fun j _ => hk j)]
  congr 1
  funext y
  simp only [← Finset.sum_mul, P.sum_eq_one, one_mul]
end ReciprocityTheory.AnForm.M
