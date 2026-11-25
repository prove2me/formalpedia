-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.cut_ptS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:07:09.389808+00:00
-- url     : https://prove2.me/submissions/da4fb499-1117-40ea-89b3-d896c6abf3be

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_two_form_sq_nonneg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_two_form_sq_add_le
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_two_form_sq_smul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_two_form_sq_wedge_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
private lemma norm_ofReal_sq_le_one_of_abs_le_one (c : ℝ) (hc : |c| ≤ 1) : ‖(c : ℂ)‖ ^ 2 ≤ 1 := by
  have h1 : ‖(c : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hc
  nlinarith [norm_nonneg (c : ℂ)]
end
end ReciprocityTheory.L2DbarEstimates.F
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {n : ℕ} (c : ℝ) (hc : |c| ≤ 1) (σx : Fin n → Fin n → ℂ) (a b : Fin n → ℂ)
    (D fx2 ph ψ : ℝ) (ha : ∑ i, ‖a i‖ ^ 2 = D) (hb : ∑ i, ‖b i‖ ^ 2 = fx2)
    (hD : D ≤ Real.exp ψ) :
    sq2 n (fun j k => (c : ℂ) * σx j k + wedge a b j k) * Real.exp (-ph) ≤
      2 * (sq2 n σx * Real.exp (-ph)) + 4 * (fx2 * Real.exp (-(ph - ψ))) := by
  have h1 := two_form_sq_add_le n (fun j k => (c : ℂ) * σx j k) (wedge a b)
  have h2 := two_form_sq_smul n (c : ℂ) σx
  have h3 := two_form_sq_wedge_le n a b
  rw [ha, hb] at h3
  have hc2 := norm_ofReal_sq_le_one_of_abs_le_one c hc
  have hs0 := two_form_sq_nonneg n σx
  have hcs := mul_le_mul_of_nonneg_right hc2 hs0
  have hf0 : 0 ≤ fx2 := by
    rw [← hb]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hD' : D * fx2 ≤ Real.exp ψ * fx2 := mul_le_mul_of_nonneg_right hD hf0
  have hE : 0 < Real.exp (-ph) := Real.exp_pos _
  have hQ : Real.exp (-ph) * Real.exp ψ = Real.exp (-(ph - ψ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hbound : sq2 n (fun j k => (c : ℂ) * σx j k + wedge a b j k) ≤
      2 * sq2 n σx + 4 * (Real.exp ψ * fx2) := by
    linarith
  calc sq2 n (fun j k => (c : ℂ) * σx j k + wedge a b j k) * Real.exp (-ph)
      ≤ (2 * sq2 n σx + 4 * (Real.exp ψ * fx2)) * Real.exp (-ph) :=
        mul_le_mul_of_nonneg_right hbound hE.le
    _ = 2 * (sq2 n σx * Real.exp (-ph)) + 4 * (fx2 * Real.exp (-(ph - ψ))) := by
        rw [← hQ]
        ring
end ReciprocityTheory.L2DbarEstimates.F
