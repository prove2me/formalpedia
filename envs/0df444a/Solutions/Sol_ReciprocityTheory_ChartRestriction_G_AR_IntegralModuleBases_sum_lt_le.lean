-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases.sum_lt_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:29:58.313722+00:00
-- url     : https://prove2.me/submissions/d0836a78-504b-461a-a911-489e931069bb

import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction
import Definitions.Def_ReciprocityTheory_ReducedBases_TBInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_NormGsoSqLeTwoPowMulOfValEqAdd
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_sum_gs_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
open Finset InnerProductSpace ReciprocityTheory.ReducedBases.T2
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
theorem _root_.solution (b : Fin d → E) (hr : IsRed b) (i : Fin d) :
    ∑ j ∈ univ.filter (fun j : Fin d => j < i), ‖gs b j‖ ^ 2 ≤
      (2 * 2 ^ i.val - 2) * ‖gs b i‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos i.val with h0 | hpos
  · have hE : univ.filter (fun j : Fin d => j < i) = ∅ := by
      rw [Finset.filter_eq_empty_iff]; intro j _; rw [Fin.lt_iff_val_lt_val, h0]; omega
    rw [hE, sum_empty, h0]; simp
  · obtain ⟨n, hn⟩ : ∃ n, i.val = n + 1 := ⟨i.val - 1, by omega⟩
    have hnd : n < d := by have := i.isLt; omega
    have hset : univ.filter (fun j : Fin d => j < i) = univ.filter (fun j : Fin d => j.val ≤ n) := by
      ext j; simp only [mem_filter, mem_univ, true_and, Fin.lt_iff_val_lt_val]; omega
    rw [hset]
    have h1 := sum_gs_le b hr.2.2 n hnd
    have h2 := hr.2.2 i ⟨n, hnd⟩ hn
    have hpow : (2:ℝ) ^ i.val = 2 * 2 ^ n := by rw [hn, pow_succ]; ring
    have hA : (0:ℝ) ≤ 2 ^ (n + 1) - 1 := by
      have : (1:ℝ) ≤ 2 ^ (n + 1) := one_le_pow₀ (by norm_num)
      linarith
    calc _ ≤ (2 ^ (n + 1) - 1) * ‖gs b ⟨n, hnd⟩‖ ^ 2 := h1
      _ ≤ (2 ^ (n + 1) - 1) * (2 * ‖gs b i‖ ^ 2) := mul_le_mul_of_nonneg_left h2 hA
      _ = (2 * 2 ^ i.val - 2) * ‖gs b i‖ ^ 2 := by rw [hpow]; ring
end ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
