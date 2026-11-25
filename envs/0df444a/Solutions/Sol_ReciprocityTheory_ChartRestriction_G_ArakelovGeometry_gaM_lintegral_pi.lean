-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gaM_lintegral_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:02:40.502529+00:00
-- url     : https://prove2.me/submissions/8b4995a7-bc91-4e1c-a0f7-baa46a24ff60

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gaM_lintegral_complex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (D : ℕ) : ∀ (a : ℝ), 0 < a → ∀ j : ℕ,
    ∫⁻ y : Fin D → ℂ, ENNReal.ofReal (((a + ∑ i, ‖y i‖ ^ 2) ^ (D + j + 1))⁻¹) =
      ENNReal.ofReal (Real.pi ^ D * (j.factorial : ℝ) / (((D + j).factorial : ℝ) * a ^ (j + 1))) := by
  induction D with
  | zero =>
    intro a ha j
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, zero_add, pow_zero, one_mul]
    rw [lintegral_const, MeasureTheory.volume_pi, Measure.pi_univ, Finset.univ_eq_empty,
      Finset.prod_empty, mul_one]
    congr 1
    have : (0 : ℝ) < (j.factorial : ℝ) := by positivity
    field_simp
  | succ D ih =>
    intro a ha j
    have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (D + 1) => ℂ) 0
    set F : (Fin (D + 1) → ℂ) → ℝ≥0∞ := fun y =>
      ENNReal.ofReal (((a + ∑ i, ‖y i‖ ^ 2) ^ (D + 1 + j + 1))⁻¹) with hF
    have hFm : Measurable F := by
      have : Continuous fun y : Fin (D + 1) → ℂ => ((a + ∑ i, ‖y i‖ ^ 2) ^ (D + 1 + j + 1))⁻¹ := by
        refine Continuous.inv₀ (by fun_prop) fun y => ?_
        have : 0 < a + ∑ i, ‖y i‖ ^ 2 := by positivity
        positivity
      exact ENNReal.measurable_ofReal.comp this.measurable
    have h1 := hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)
      (fun p => F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (D + 1) => ℂ) 0).symm p))
    simp only [MeasurableEquiv.symm_apply_apply] at h1
    rw [h1, Measure.volume_eq_prod,
      lintegral_prod (fun p => F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (D + 1) => ℂ) 0).symm p))
        ((hFm.comp (MeasurableEquiv.measurable _)).aemeasurable)]
    have h2 : ∀ t : ℂ, ∫⁻ y', F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (D + 1) => ℂ) 0).symm (t, y')) =
        ENNReal.ofReal (Real.pi ^ D * ((j + 1).factorial : ℝ) / (((D + (j + 1)).factorial : ℝ))) *
          ENNReal.ofReal (((a + ‖t‖ ^ 2) ^ (j + 2))⁻¹) := by
      intro t
      have ht : 0 < a + ‖t‖ ^ 2 := by positivity
      have := ih (a + ‖t‖ ^ 2) ht (j + 1)
      have hexp : D + (j + 1) + 1 = D + 1 + j + 1 := by ring
      rw [hexp] at this
      simp only [hF, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Equiv.coe_fn_mk, Fin.insertNth_zero', Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      simp_rw [← add_assoc]
      rw [this, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have : 0 < (a + ‖t‖ ^ 2) ^ (j + 2) := by positivity
      field_simp
      rw [show D + j + 1 = D + (j + 1) by ring]
    simp_rw [h2]
    rw [lintegral_const_mul _ (by fun_prop), gaM_lintegral_complex ha j, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hfj : ((j + 1).factorial : ℝ) = (j + 1) * j.factorial := by push_cast [Nat.factorial_succ]; ring
    have hfD : ((D + 1 + j).factorial : ℝ) = ((D + (j + 1)).factorial : ℝ) := by
      rw [show D + 1 + j = D + (j + 1) by ring]
    rw [hfj, hfD]
    have : (0 : ℝ) < ((D + (j + 1)).factorial : ℝ) := by positivity
    have : (0 : ℝ) < a ^ (j + 1) := by positivity
    field_simp
    ring
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
