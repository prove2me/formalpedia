-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.formalGroup_pow_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:18:28.503472+00:00
-- url     : https://prove2.me/submissions/91a34e8d-9689-4acc-b755-cbaf7c5f62c8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorChord
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorContr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_formalGroup_nsmul_estimate
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_key
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_formalGroup_param_norm_lt_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)
variable {C : Type} [NormedField C] [IsUltrametricDist C] [CompleteSpace C]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (W : WeierstrassCurve C) (hW : IntegralModel W) (hΔ : ‖W.Δ‖ = 1)
    (D : W.toAffine.Point) (hD : InFormalGroupPoints D) (M : ℕ) (hM : ‖(M : C)‖ < 1) :
    Filter.Tendsto (fun k : ℕ => ‖uOf (M ^ k • D)‖) Filter.atTop (nhds 0) := by
  have hu : ‖uOf D‖ < 1 := formalGroup_param_norm_lt_one W hW D hD
  set c : ℝ := max ‖(M : C)‖ ‖uOf D‖ with hc
  have hc0 : 0 ≤ c := le_max_of_le_left (norm_nonneg _)
  have hc1 : c < 1 := max_lt hM hu
  have key : ∀ k : ℕ, ‖uOf (M ^ k • D)‖ ≤ c ^ k * ‖uOf D‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hk : InFormalGroupPoints (M ^ k • D) := (formalGroup_nsmul_estimate W hW hΔ D hD (M ^ k)).1
      have hest := (formalGroup_nsmul_estimate W hW hΔ (M ^ k • D) hk M).2
      have hle : ‖uOf (M ^ k • D)‖ ≤ ‖uOf D‖ :=
        ih.trans (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hc0 hc1.le))
      have hr0 := norm_nonneg (uOf (M ^ k • D))
      have e0 : M ^ (k + 1) • D = M • (M ^ k • D) := by
        rw [smul_smul, pow_succ, mul_comm]
      have h1 : ‖uOf (M • (M ^ k • D))‖ ≤ c * ‖uOf (M ^ k • D)‖ := by
        have e : uOf (M • (M ^ k • D)) = (uOf (M • (M ^ k • D)) - (M : C) * uOf (M ^ k • D))
            + (M : C) * uOf (M ^ k • D) := by ring
        rw [e]
        refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hest.trans ?_) ?_)
        · rw [sq]
          exact mul_le_mul_of_nonneg_right (hle.trans (le_max_right _ _)) hr0
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hr0
      rw [e0, pow_succ, mul_comm (c ^ k) c, mul_assoc]
      exact h1.trans (mul_le_mul_of_nonneg_left ih hc0)
  have hlim : Filter.Tendsto (fun k : ℕ => c ^ k * ‖uOf D‖) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const ‖uOf D‖
  exact squeeze_zero (fun _ => norm_nonneg _) key hlim
end ReciprocityTheory.ChartRestriction.L1
