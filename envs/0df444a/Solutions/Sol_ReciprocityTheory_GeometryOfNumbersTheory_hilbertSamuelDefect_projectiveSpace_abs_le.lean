-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.hilbertSamuelDefect_projectiveSpace_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:50:30.338462+00:00
-- url     : https://prove2.me/submissions/42bfd29f-a98d-488c-9541-ffb7b2008a18

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_ChiPSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_AsymptoticSequences_DefectSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_chiP_nonneg
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_exists_chiP_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Filter Topology Asymptotics
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (D : ℕ) (hh : ℝ) :
    ∃ C : ℝ, ∀ n : ℕ, |hsDefect D (chiP D) hh n| ≤ C * (n : ℝ) ^ (D + 1) := by
  obtain ⟨C, hC⟩ := exists_chiP_le D
  refine ⟨|C| + |hh|, fun n => ?_⟩
  have h0 := chiP_nonneg D n
  have h1 := hC n
  have hp : (0:ℝ) ≤ (n:ℝ) ^ (D + 1) := by positivity
  have hFpos : (0:ℝ) < ((D + 1).factorial : ℝ) := by positivity
  have hf : (1:ℝ) ≤ ((D + 1).factorial : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hq : |hh * (n:ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)| ≤ |hh| * (n:ℝ) ^ (D + 1) := by
    rw [abs_div, abs_mul, abs_of_nonneg hp, abs_of_pos hFpos]
    exact div_le_self (by positivity) hf
  have hc : chiP D n ≤ |C| * (n:ℝ) ^ (D + 1) :=
    h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hp)
  have hq' := abs_le.mp hq
  unfold hsDefect
  rw [abs_le]
  constructor <;> nlinarith [abs_nonneg C, abs_nonneg hh]
end ReciprocityTheory.GeometryOfNumbersTheory
