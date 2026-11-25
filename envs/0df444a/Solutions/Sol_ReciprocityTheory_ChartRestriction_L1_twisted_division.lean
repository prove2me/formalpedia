-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.twisted_division
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:03:42.2922+00:00
-- url     : https://prove2.me/submissions/fa042036-783e-44cf-9996-89ec9b31b20b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_triSol_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_norm_pow_apply_of_isometric
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_triIter_norm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (τ : K →+* K) (hτ : ∀ x, ‖τ x‖ = ‖x‖) (π : K) (hπ : ‖π‖ < 1)
    (c : ℕ → K) (hc0 : ‖c 0‖ = 1) (hc : ∀ i, ‖c i‖ ≤ 1) :
    ∃ t : ℕ → K, t 0 = 1 ∧ (∀ n, ‖t n‖ ≤ 1) ∧
      ∀ n, 2 ≤ n → π * t n = ∑ i ∈ Finset.range n, t i * (τ ^ i) (c (n - 1 - i)) := by
  set a : ℕ → ℕ → K := fun i m => (τ ^ i) (c (m - i)) with ha_def
  have ha1 : ∀ i m, ‖a i m‖ ≤ 1 := fun i m => by
    rw [ha_def]; simp only; rw [norm_pow_apply_of_isometric τ hτ]; exact hc _
  have ha : ∀ m, ‖a m m‖ = 1 := fun m => by
    rw [ha_def]; simp only; rw [norm_pow_apply_of_isometric τ hτ, Nat.sub_self]; exact hc0
  have ha0 : ∀ m, a m m ≠ 0 := fun m h => by
    have := ha m; rw [h, norm_zero] at this; exact zero_ne_one this
  have hsum : ∀ m, Summable fun k => triIter a π k m := fun m =>
    Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg π) hπ)
      (fun k => triIter_norm a π ha1 ha k m)
  have hz0 : triIter a π 0 0 = 1 := by
    have h := triSol_eq a (fun m => if m = 0 then a 0 0 else 0) ha0 0
    simp only [zero_add, Finset.sum_range_one, if_true] at h
    rw [triIter]
    exact mul_right_cancel₀ (ha0 0) (h.trans (one_mul _).symm)
  have hzs : ∀ k, triIter a π (k + 1) 0 = 0 := fun k => by
    have h := triSol_eq a (fun m => if m = 0 then 0 else π * triIter a π k (m + 1)) ha0 0
    simp only [zero_add, Finset.sum_range_one, if_true] at h
    rw [triIter]
    exact (mul_eq_zero.mp h).resolve_right (ha0 0)
  refine ⟨fun m => ∑' k, triIter a π k m, ?_, fun n => ?_, fun n hn => ?_⟩
  · simp only
    rw [(hsum 0).tsum_eq_zero_add, hz0]
    simp [hzs]
  · refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg zero_le_one fun k => ?_
    exact (triIter_norm a π ha1 ha k n).trans (pow_le_one₀ (norm_nonneg _) hπ.le)
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hterm : ∀ i, (∑' k, triIter a π k i) * (τ ^ i) (c (m + 2 - 1 - i))
        = ∑' k, triIter a π k i * a i (m + 1) := fun i => by
      rw [tsum_mul_right]
      rfl
    simp only [hterm]
    rw [← Summable.tsum_finsetSum (fun i _ => (hsum i).mul_right _)]
    have hS : Summable fun k => ∑ i ∈ Finset.range (m + 2), triIter a π k i * a i (m + 1) :=
      summable_sum fun i _ => (hsum i).mul_right _
    rw [hS.tsum_eq_zero_add, ← tsum_mul_left]
    have h0 : ∑ i ∈ Finset.range (m + 2), triIter a π 0 i * a i (m + 1) = 0 := by
      have h := triSol_eq a (fun m => if m = 0 then a 0 0 else 0) ha0 (m + 1)
      simpa [triIter] using h
    rw [h0, zero_add]
    refine tsum_congr fun k => ?_
    have h := triSol_eq a (fun m => if m = 0 then 0 else π * triIter a π k (m + 1)) ha0 (m + 1)
    simpa [triIter] using h.symm
end ReciprocityTheory.ChartRestriction.L1
