-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.PolynomialGrowthIntegrals.int_abs_rpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:25:18.349834+00:00
-- url     : https://prove2.me/submissions/044065f9-d4b2-40de-bdba-eb88b7a3f7b4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_SlowWeightBound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_PolynomialGrowthIntegrals_int_pos_rpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.PolynomialGrowthIntegrals
namespace ReciprocityTheory.ChartRestriction.DS.Xi.PolynomialGrowthIntegrals
theorem _root_.solution {R κ : ℝ} (hR : 0 < R) (hκ0 : 0 < κ) (hκ : κ < 1) :
    ∫⁻ β in Icc (-R) R, ENNReal.ofReal (|β| ^ (-κ)) ≤ 2 * ENNReal.ofReal (R ^ (1 - κ) / (1 - κ)) := by
  have hpos : ∫⁻ β in Icc 0 R, ENNReal.ofReal (|β| ^ (-κ)) =
      ENNReal.ofReal (R ^ (1 - κ) / (1 - κ)) := by
    rw [setLIntegral_congr Ioc_ae_eq_Icc.symm, ← int_pos_rpow hR hκ]
    exact setLIntegral_congr_fun measurableSet_Ioc fun x hx => by rw [abs_of_pos hx.1]
  have hneg : ∫⁻ β in Icc (-R) 0, ENNReal.ofReal (|β| ^ (-κ)) =
      ∫⁻ β in Icc 0 R, ENNReal.ofReal (|β| ^ (-κ)) := by
    have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage
      (measurableSet_Icc (a := (0 : ℝ)) (b := R))
      (f := fun β : ℝ => ENNReal.ofReal (|β| ^ (-κ))) (by fun_prop)
    have hs : Neg.neg ⁻¹' Icc (0 : ℝ) R = Icc (-R) 0 := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Icc]
      constructor <;> intro hx <;> constructor <;> linarith [hx.1, hx.2]
    simp only [abs_neg] at h
    rw [hs] at h
    exact h
  calc ∫⁻ β in Icc (-R) R, ENNReal.ofReal (|β| ^ (-κ))
      ≤ (∫⁻ β in Icc (-R) 0, ENNReal.ofReal (|β| ^ (-κ))) +
          ∫⁻ β in Icc 0 R, ENNReal.ofReal (|β| ^ (-κ)) := by
        rw [← Icc_union_Icc_eq_Icc (by linarith : -R ≤ 0) hR.le]
        exact lintegral_union_le _ _ _
    _ = 2 * ENNReal.ofReal (R ^ (1 - κ) / (1 - κ)) := by rw [hneg, hpos, two_mul]
end ReciprocityTheory.ChartRestriction.DS.Xi.PolynomialGrowthIntegrals
