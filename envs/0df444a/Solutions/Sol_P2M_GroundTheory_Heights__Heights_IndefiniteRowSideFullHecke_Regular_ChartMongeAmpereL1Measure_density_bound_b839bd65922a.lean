-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartMongeAmpereL1Measure_density_bound_b839bd65922a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:32:02.094272+00:00
-- url     : https://prove2.me/submissions/45803d68-970c-4adf-a9a3-2a2299f39fcb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ChartMongeAmpereL1Hypotheses
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_AestronglyMeasurableMapSymm
import Theorems.Thm_ReciprocityTheory_AnForm_M_chi_le_one
import Theorems.Thm_ReciprocityTheory_AnForm_M_image_closed_compact
import Theorems.Thm_ReciprocityTheory_AnForm_M_locDensCont


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
open MeasureTheory Filter Topology Set
open scoped ENNReal
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot maMeasure ChartPartition locDens)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts)
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartMongeAmpereL1Measure
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartMongeAmpereL1Measure
theorem _root_.solution {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
    (A : FinHolAtlas D X) (Q : ChartPartition A) (Φ : Fin D → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (j : Fin A.n) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ y ∈ (A.chart j).target,
      ENNReal.ofReal (Q.χ j ((A.chart j).symm y) * locDens A Φ j y) ≤
        (tsupport (Q.χ j)).indicator (fun _ => c) ((A.chart j).symm y) := by
  obtain ⟨hKc, hKT⟩ := ReciprocityTheory.AnForm.M.image_closed_compact (A.chart j)
    (isClosed_tsupport (Q.χ j)) (Q.tsupport_subset j)
  obtain ⟨C, hC⟩ :=
    hKc.exists_bound_of_continuousOn ((ReciprocityTheory.AnForm.M.locDensCont A Φ hΦ j).mono hKT)
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, fun y hy => ?_⟩
  by_cases hx : (A.chart j).symm y ∈ tsupport (Q.χ j)
  · rw [indicator_of_mem hx]
    apply ENNReal.ofReal_le_ofReal
    have hyK : y ∈ (A.chart j) '' tsupport (Q.χ j) := ⟨_, hx, (A.chart j).right_inv hy⟩
    have h1 := hC y hyK
    have h0 := Q.nonneg j ((A.chart j).symm y)
    have h2 := ReciprocityTheory.AnForm.M.chi_le_one Q j ((A.chart j).symm y)
    rw [Real.norm_eq_abs] at h1
    calc Q.χ j ((A.chart j).symm y) * locDens A Φ j y
        ≤ Q.χ j ((A.chart j).symm y) * |locDens A Φ j y| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) h0
      _ ≤ 1 * C := mul_le_mul h2 h1 (abs_nonneg _) zero_le_one
      _ = C := one_mul C
  · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx, zero_mul,
      ENNReal.ofReal_zero]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartMongeAmpereL1Measure
