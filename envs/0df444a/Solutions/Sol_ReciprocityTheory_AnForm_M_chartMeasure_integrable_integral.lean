-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.chartMeasure_integrable_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:07:53.302534+00:00
-- url     : https://prove2.me/submissions/1646a8be-160f-4e44-b546-34771385c327

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB
import Theorems.Thm_ReciprocityTheory_AnForm_M_map_withDensity_integrable_integral
import Theorems.Thm_ReciprocityTheory_AnForm_M_integrableOn_target_of_closed
import Theorems.Thm_ReciprocityTheory_AnForm_M_image_closed_compact
import Theorems.Thm_ReciprocityTheory_AnForm_M_chi_comp_continuousOn
import Theorems.Thm_ReciprocityTheory_AnForm_M_locDensCont
import Theorems.Thm_ReciprocityTheory_AnForm_M_locDens_nonneg_of_psh


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Set Filter Topology
open scoped ContDiff ENNReal NNReal
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [T2Space X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (A : FinHolAtlas e X) (P : ChartPartition A)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (hPsh : ∀ i, IsPsh A (Φ i))
    (j : Fin A.n) {g : X → ℝ} (hg : Measurable g) (hgi : MIntegrable A Φ g) :
    Integrable g (chartMeasure A P Φ j) ∧
      ∫ x, g x ∂chartMeasure A P Φ j =
        ∫ y in (A.chart j).target, g ((A.chart j).symm y) *
          (P.χ j ((A.chart j).symm y) * locDens A Φ j y) := by
  have hT := (A.chart j).open_target
  have hw0 : ∀ y ∈ (A.chart j).target, 0 ≤ P.χ j ((A.chart j).symm y) * locDens A Φ j y :=
    fun y hy => mul_nonneg (P.nonneg j _) (locDens_nonneg_of_psh A Φ hΦ hPsh j hy)
  have hw : ContinuousOn (fun y => P.χ j ((A.chart j).symm y) * locDens A Φ j y)
      (A.chart j).target :=
    (chi_comp_continuousOn P j).mul (locDensCont A Φ hΦ j)
  obtain ⟨h1, h2⟩ := map_withDensity_integrable_integral hT (A.chart j).continuousOn_symm hw hw0 hg
  unfold chartMeasure
  refine ⟨h1.2 ?_, h2⟩
  obtain ⟨hK, hKs⟩ := image_closed_compact (A.chart j) (isClosed_tsupport (P.χ j))
    (P.tsupport_subset j)
  refine integrableOn_target_of_closed (A.chart j) (Z := tsupport (P.χ j)) ?_ ?_
  · intro y _ hz
    have h0 : P.χ j ((A.chart j).symm y) = 0 := by
      first
        | exact image_eq_zero_of_notMem_tsupport hz
        | exact image_eq_zero_of_nmem_tsupport hz
    rw [h0]
    ring
  · have hgK := hgi j _ hKs hK
    have hc : ContinuousOn (fun y => P.χ j ((A.chart j).symm y))
        (A.chart j '' tsupport (P.χ j)) := (chi_comp_continuousOn P j).mono hKs
    have hm : IntegrableOn (fun y => P.χ j ((A.chart j).symm y) *
        (g ((A.chart j).symm y) * locDens A Φ j y)) (A.chart j '' tsupport (P.χ j)) := by
      first
        | exact hgK.continuousOn_mul hc hK
        | exact IntegrableOn.continuousOn_mul hc hgK hK
        | exact hgK.continuousOn_mul hc hK.measurableSet
    refine hm.congr_fun (fun y _ => by ring) hK.measurableSet
end ReciprocityTheory.AnForm.M
