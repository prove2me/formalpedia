-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.norm_exp_frobVG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:26.748802+00:00
-- url     : https://prove2.me/submissions/4f97115a-6ac4-48df-8758-fcfecdc59e30

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_SignedIdentityColumns
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IntegrableOfDecayVG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_sqrt_hs_frobVG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_hs_oneVG


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix Topology Metric
open scoped ENNReal NNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (X : Matrix (Fin n) (Fin n) ℂ) :
    ‖NormedSpace.exp X‖ ≤ Real.sqrt n * Real.exp ‖X‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : NormedSpace.exp X = 0 := Subsingleton.elim _ _
    rw [this]; simp
  have h1 : (1 : ℝ) ≤ Real.sqrt n := by
    rw [Real.one_le_sqrt]; exact_mod_cast hn
  have hsum := NormedSpace.norm_expSeries_summable' (𝕂 := ℂ) X
  have hr : Summable fun k : ℕ => Real.sqrt n * (‖X‖ ^ k / (k.factorial : ℝ)) :=
    (Real.summable_pow_div_factorial ‖X‖).mul_left _
  rw [NormedSpace.exp_eq_tsum ℂ]
  calc ‖∑' k : ℕ, ((k.factorial : ℂ)⁻¹) • X ^ k‖ ≤ ∑' k : ℕ, ‖((k.factorial : ℂ)⁻¹) • X ^ k‖ :=
        norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' k : ℕ, Real.sqrt n * (‖X‖ ^ k / (k.factorial : ℝ)) := by
        refine hsum.tsum_le_tsum (fun k => ?_) hr
        rw [norm_smul, norm_inv, Complex.norm_natCast]
        have hk : ‖X ^ k‖ ≤ Real.sqrt n * ‖X‖ ^ k := by
          rcases Nat.eq_zero_or_pos k with rfl | hk
          · rw [pow_zero, pow_zero, mul_one, ← sqrt_hs_frobVG, hs_oneVG]
          · calc ‖X ^ k‖ ≤ ‖X‖ ^ k := norm_pow_le' X hk
              _ ≤ Real.sqrt n * ‖X‖ ^ k := le_mul_of_one_le_left (by positivity) h1
        calc ((k.factorial : ℝ))⁻¹ * ‖X ^ k‖ ≤ ((k.factorial : ℝ))⁻¹ * (Real.sqrt n * ‖X‖ ^ k) := by gcongr
          _ = _ := by ring
    _ = Real.sqrt n * Real.exp ‖X‖ := by
        rw [tsum_mul_left, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
end ReciprocityTheory.ChartRestriction.DS.S7
