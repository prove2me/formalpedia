-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_birational_yLine_21d746fbd4e1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:40:14.557467+00:00
-- url     : https://prove2.me/submissions/9a86728b-40c3-4fbc-8b3a-284b929a0d5d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_LineField
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_yLine_zero_ca6e34684267
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_yLine_one_da595b259ab5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_isMultiHomog_X_line_5b92169b8b7f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_C_zero_b41b49555e2b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_add_95ee52bfb1b9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_mul_0d39b8f19b1f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_one_0a1e8350c35d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_zero_c322b3967d06


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.Line
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.LowerBoundFree.Line
theorem _root_.solution : Birational yLine := by
  rintro ⟨x, hx⟩
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx
    refine ⟨fun _ => 1, X ⟨(), 1⟩, X ⟨(), 0⟩, isMultiHomog_X_line 1, isMultiHomog_X_line 0, ?_, ?_⟩
    · rw [aeval_X, yLine_zero]; exact one_ne_zero
    · rw [aeval_X, aeval_X, yLine_zero, yLine_one, mul_one]; rfl
  | algebraMap r =>
    refine ⟨0, C r.num, C (r.den : ℤ), isMultiHomog_C_zero _, isMultiHomog_C_zero _, ?_, ?_⟩
    · rw [aeval_C]; simp [r.den_nz]
    · rw [aeval_C, aeval_C]
      have : (⟨algebraMap ℚ L r, IntermediateField.algebraMap_mem _ r⟩ : Ω) = algebraMap ℚ Ω r := rfl
      rw [this, eq_intCast, eq_intCast, ← map_intCast (algebraMap ℚ Ω),
        ← map_intCast (algebraMap ℚ Ω), ← map_mul]
      congr 1
      push_cast
      exact (Rat.mul_den_eq_num r).symm
  | add x y hx hy ihx ihy =>
    obtain ⟨d₁, g₁, h₁, hg₁, hh₁, hy₁, e₁⟩ := ihx
    obtain ⟨d₂, g₂, h₂, hg₂, hh₂, hy₂, e₂⟩ := ihy
    refine ⟨d₁ + d₂, g₁ * h₂ + g₂ * h₁, h₁ * h₂,
      isMultiHomog_add (isMultiHomog_mul hg₁ hh₂) (by rw [add_comm]; exact isMultiHomog_mul hg₂ hh₁),
      isMultiHomog_mul hh₁ hh₂, by rw [map_mul]; exact mul_ne_zero hy₁ hy₂, ?_⟩
    have : (⟨x + y, add_mem hx hy⟩ : Ω) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [this, map_add, map_mul, map_mul, map_mul, e₁, e₂]
    ring
  | inv x hx ih =>
    obtain ⟨d, g, h, hg, hh, hy, e⟩ := ih
    have hinv : (⟨x⁻¹, inv_mem hx⟩ : Ω) = (⟨x, hx⟩ : Ω)⁻¹ := rfl
    by_cases h0 : (⟨x, hx⟩ : Ω) = 0
    · refine ⟨0, 0, 1, isMultiHomog_zero _, isMultiHomog_one, by simp, ?_⟩
      rw [hinv, h0, inv_zero, zero_mul, map_zero]
    · refine ⟨d, h, g, hh, hg, by rw [e]; exact mul_ne_zero h0 hy, ?_⟩
      rw [hinv, e]
      field_simp
  | mul x y hx hy ihx ihy =>
    obtain ⟨d₁, g₁, h₁, hg₁, hh₁, hy₁, e₁⟩ := ihx
    obtain ⟨d₂, g₂, h₂, hg₂, hh₂, hy₂, e₂⟩ := ihy
    refine ⟨d₁ + d₂, g₁ * g₂, h₁ * h₂, isMultiHomog_mul hg₁ hg₂, isMultiHomog_mul hh₁ hh₂,
      by rw [map_mul]; exact mul_ne_zero hy₁ hy₂, ?_⟩
    have : (⟨x * y, mul_mem hx hy⟩ : Ω) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [this, map_mul, map_mul, e₁, e₂]
    ring
end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
