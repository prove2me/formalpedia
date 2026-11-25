-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.paPoly_growth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:24:25.204331+00:00
-- url     : https://prove2.me/submissions/54ce256e-6405-41c4-bc07-456906aef54b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CardSupportLeAndSumTwoPowLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paS_deg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paMono_norm_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {c : ℕ} {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v, ‖F v‖ ≤ C * (1 + ‖v‖) ^ c := by
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, hα, rfl⟩ := hx
    refine ⟨1, zero_le_one, fun v => ?_⟩
    rw [one_mul]
    refine (paMono_norm_le α v).trans ?_
    calc ‖v‖ ^ α.degree ≤ (1 + ‖v‖) ^ α.degree := pow_le_pow_left₀ (norm_nonneg _) (by linarith) _
      _ ≤ (1 + ‖v‖) ^ c := pow_le_pow_right₀ (by linarith [norm_nonneg v]) (paS_deg hα)
  | zero => exact ⟨0, le_rfl, fun v => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨C1, h1, hC1⟩ := hx
    obtain ⟨C2, h2, hC2⟩ := hy
    exact ⟨C1 + C2, by positivity, fun v => (norm_add_le _ _).trans (by
      have := hC1 v; have := hC2 v; nlinarith)⟩
  | smul a x _ hx =>
    obtain ⟨C, h, hC⟩ := hx
    refine ⟨‖a‖ * C, by positivity, fun v => ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC v) (norm_nonneg _)
end ReciprocityTheory.ChartRestriction.G.I2
