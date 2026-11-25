-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume.cone_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:26:31.299864+00:00
-- url     : https://prove2.me/submissions/e5f1c1ef-0fe0-4243-8583-6bbc6cf0246a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LintegralIoiOfRealMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Real
open scoped ENNReal Pointwise
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume
namespace ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume
theorem _root_.solution (u : E3) (s : Set ℝ) :
    Ioo (0 : ℝ) 1 • (((↑) : S2 → E3) '' {n : S2 | inner ℝ (n : E3) u ∈ s}) =
      {x : E3 | 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ inner ℝ x u / ‖x‖ ∈ s} := by
  ext x
  constructor
  · rintro ⟨a, ha, _, ⟨n, hn, rfl⟩, rfl⟩
    have hn1 : ‖(n : E3)‖ = 1 := by simp
    have ha0 : 0 < a := ha.1
    simp only [mem_ofPred_eq] at hn ⊢
    rw [norm_smul, hn1, Real.norm_eq_abs, abs_of_pos ha0, mul_one, real_inner_smul_left,
      mul_div_cancel_left₀ _ ha0.ne']
    exact ⟨ha0, ha.2, hn⟩
  · rintro ⟨h0, h1, h2⟩
    refine ⟨‖x‖, ⟨h0, h1⟩, ‖x‖⁻¹ • x, ⟨⟨‖x‖⁻¹ • x, ?_⟩, ?_, rfl⟩, ?_⟩
    · simp [norm_smul, h0.ne']
    · show inner ℝ (‖x‖⁻¹ • x) u ∈ s
      rw [real_inner_smul_left, inv_mul_eq_div]
      exact h2
    · exact smul_inv_smul₀ h0.ne' x
end ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume
