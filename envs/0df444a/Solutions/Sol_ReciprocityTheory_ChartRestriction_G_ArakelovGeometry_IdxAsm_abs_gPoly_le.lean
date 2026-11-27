-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.IdxAsm.abs_gPoly_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:25:30.926026+00:00
-- url     : https://prove2.me/submissions/379bc02f-7ce1-4c4b-b1f6-668649645a30

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_AsymptoticSequences_SimplexSumSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IdxAssembleStA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.IdxAsm
open Filter Asymptotics Finset
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.IdxAsm
theorem _root_.solution (D : ℕ) (c : ℕ → ℝ) (a b : ℕ) :
    |gPoly D c a b| ≤ (∑ i ∈ range (D + 1), |c i|) * (((a + b : ℕ) : ℝ) + 1) ^ D := by
  unfold gPoly
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have hi : i ≤ D := Nat.lt_succ_iff.mp (mem_range.mp hi)
  have hf : (1 : ℝ) ≤ (i.factorial : ℝ) * ((D - i).factorial : ℝ) := by
    have h1 : (1 : ℝ) ≤ i.factorial := by exact_mod_cast Nat.factorial_pos i
    have h2 : (1 : ℝ) ≤ (D - i).factorial := by exact_mod_cast Nat.factorial_pos _
    nlinarith
  have ha : (a : ℝ) ≤ ((a + b : ℕ) : ℝ) + 1 := by
    push_cast; linarith [(b.cast_nonneg : (0 : ℝ) ≤ b)]
  have hb : (b : ℝ) ≤ ((a + b : ℕ) : ℝ) + 1 := by
    push_cast; linarith [(a.cast_nonneg : (0 : ℝ) ≤ a)]
  have hab : (a : ℝ) ^ i * (b : ℝ) ^ (D - i) ≤ (((a + b : ℕ) : ℝ) + 1) ^ D := by
    calc (a : ℝ) ^ i * (b : ℝ) ^ (D - i)
        ≤ (((a + b : ℕ) : ℝ) + 1) ^ i * (((a + b : ℕ) : ℝ) + 1) ^ (D - i) :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) ha _) (pow_le_pow_left₀ (by positivity) hb _)
            (by positivity) (by positivity)
      _ = _ := by rw [← pow_add, Nat.add_sub_cancel' hi]
  rw [abs_of_nonneg (by positivity)]
  calc _ ≤ (a : ℝ) ^ i * (b : ℝ) ^ (D - i) := div_le_self (by positivity) hf
    _ ≤ _ := hab
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.IdxAsm
