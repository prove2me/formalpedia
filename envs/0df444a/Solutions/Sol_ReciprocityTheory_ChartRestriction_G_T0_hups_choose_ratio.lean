-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.hups_choose_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:36:45.525741+00:00
-- url     : https://prove2.me/submissions/1c80eec7-3f4a-4b6d-adcf-87513ee68395

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormLineSectionPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HupsChooseRatio
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (n p : ℕ) (hp : p ≤ n) : ∀ a : ℕ,
    (((n + a).choose a : ℕ) : ℝ) * ((p : ℝ) + 1) ^ a ≤
      (((p + a).choose a : ℕ) : ℝ) * ((n : ℝ) + 1) ^ a := by
  intro a
  induction a with
  | zero => simp
  | succ a ih =>
    have hA := Nat.add_one_mul_choose_eq (n + a) a
    have hB := Nat.add_one_mul_choose_eq (p + a) a
    have eA : n + (a + 1) = (n + a + 1) := by omega
    have eB : p + (a + 1) = (p + a + 1) := by omega
    rw [eA, eB]
    have hA' : (((n + a + 1).choose (a + 1) : ℕ) : ℝ) * ((a : ℝ) + 1) =
        ((n : ℝ) + a + 1) * (((n + a).choose a : ℕ) : ℝ) := by
      have := congrArg (fun t : ℕ => (t : ℝ)) hA
      simp only [Nat.cast_mul, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] at this
      linarith
    have hB' : (((p + a + 1).choose (a + 1) : ℕ) : ℝ) * ((a : ℝ) + 1) =
        ((p : ℝ) + a + 1) * (((p + a).choose a : ℕ) : ℝ) := by
      have := congrArg (fun t : ℕ => (t : ℝ)) hB
      simp only [Nat.cast_mul, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] at this
      linarith
    have ha1 : (0 : ℝ) < (a : ℝ) + 1 := by positivity
    have hpn : (p : ℝ) ≤ n := by exact_mod_cast hp
    have hkey : ((n : ℝ) + a + 1) * ((p : ℝ) + 1) ≤ ((p : ℝ) + a + 1) * ((n : ℝ) + 1) := by
      nlinarith [(Nat.cast_nonneg a : (0:ℝ) ≤ a)]
    have hX : 0 ≤ (((n + a).choose a : ℕ) : ℝ) * ((p : ℝ) + 1) ^ a := by positivity
    have hY : 0 ≤ (((p + a).choose a : ℕ) : ℝ) * ((n : ℝ) + 1) ^ a := by positivity
    rw [← mul_le_mul_iff_of_pos_right ha1]
    calc (((n + a + 1).choose (a + 1) : ℕ) : ℝ) * ((p : ℝ) + 1) ^ (a + 1) * ((a : ℝ) + 1)
        = (((n : ℝ) + a + 1) * ((p : ℝ) + 1)) *
            ((((n + a).choose a : ℕ) : ℝ) * ((p : ℝ) + 1) ^ a) := by
          rw [pow_succ]; linear_combination ((p : ℝ) + 1) ^ a * ((p : ℝ) + 1) * hA'
      _ ≤ (((p : ℝ) + a + 1) * ((n : ℝ) + 1)) *
            ((((p + a).choose a : ℕ) : ℝ) * ((n : ℝ) + 1) ^ a) :=
          mul_le_mul hkey ih hX (by positivity)
      _ = (((p + a + 1).choose (a + 1) : ℕ) : ℝ) * ((n : ℝ) + 1) ^ (a + 1) * ((a : ℝ) + 1) := by
          rw [pow_succ]; linear_combination -(((n : ℝ) + 1) ^ a * ((n : ℝ) + 1)) * hB'
end ReciprocityTheory.ChartRestriction.G.T0
