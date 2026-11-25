-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.hon_regroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:53:13.230434+00:00
-- url     : https://prove2.me/submissions/820e9442-2e81-4364-af49-5dd68e0a9fcf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonH

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
variable {K : Type} [Field K]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (τ : K →+* K) (π : K) (c t w : ℕ → K) (M : ℕ) (hM : 1 ≤ M)
    (hw : ∀ m, M ≤ m → w m = 0) (ht0 : t 0 = 1)
    (ht : ∀ n, 2 ≤ n → π * t n = ∑ i ∈ Finset.range n, t i * (τ ^ i) (c (n - 1 - i))) :
    ∑ i ∈ Finset.range M, t i * (π * w i - ∑ j ∈ Finset.range M, (τ ^ i) (c j) * w (i + j + 1))
      = π * w 0 - (c 0 - π * t 1) * w 1 := by
  obtain ⟨K', rfl⟩ : ∃ K', M = K' + 1 := ⟨M - 1, by omega⟩

  have hS : ∑ i ∈ Finset.range (K' + 1), ∑ j ∈ Finset.range (K' + 1), t i * (τ ^ i) (c j) * w (i + j + 1)
      = ∑ n ∈ Finset.range (K' + 1), w (n + 1) * ∑ i ∈ Finset.range (n + 1), t i * (τ ^ i) (c (n - i)) := by
    have hA : ∀ i ∈ Finset.range (K' + 1),
        ∑ j ∈ Finset.range (K' + 1), t i * (τ ^ i) (c j) * w (i + j + 1)
          = ∑ j ∈ Finset.range (K' + 1 - i), t i * (τ ^ i) (c j) * w (i + j + 1) := by
      intro i _
      symm
      refine Finset.sum_subset (fun x hx => by simp only [Finset.mem_range] at hx ⊢; omega)
        fun j _ hj => ?_
      simp only [Finset.mem_range, not_lt] at hj
      rw [hw _ (by omega), mul_zero]
    rw [Finset.sum_congr rfl hA]
    have hflip := Finset.sum_range_diag_flip (K' + 1)
      (fun i j => t i * (τ ^ i) (c j) * w (i + j + 1))
    beta_reduce at hflip
    rw [← hflip]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    have e : i + (n - i) + 1 = n + 1 := by omega
    rw [e]
    ring
  have hsplit : ∀ i, t i * (π * w i - ∑ j ∈ Finset.range (K' + 1), (τ ^ i) (c j) * w (i + j + 1))
      = π * (t i * w i) - ∑ j ∈ Finset.range (K' + 1), t i * (τ ^ i) (c j) * w (i + j + 1) := by
    intro i
    rw [mul_sub, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun j _ => by ring
  have hF : ∀ n ∈ Finset.range K',
      w (n + 1 + 1) * ∑ i ∈ Finset.range (n + 1 + 1), t i * (τ ^ i) (c (n + 1 - i))
        = π * (t (n + 1 + 1) * w (n + 1 + 1)) := by
    intro n _
    have h2 := ht (n + 1 + 1) (by omega)
    simp only [Nat.add_sub_cancel] at h2
    rw [← mul_assoc, h2]
    ring
  have hF0 : w (0 + 1) * ∑ i ∈ Finset.range (0 + 1), t i * (τ ^ i) (c (0 - i)) = c 0 * w 1 := by
    simp [ht0] <;> ring
  have htel := Finset.sum_range_sub' (fun m => t (m + 1) * w (m + 1)) K'
  beta_reduce at htel
  rw [Finset.sum_sub_distrib, zero_add] at htel
  have hwM : w (K' + 1) = 0 := hw _ le_rfl
  rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_sub_distrib, ← Finset.mul_sum, hS,
    Finset.sum_range_succ', Finset.sum_range_succ']
  try beta_reduce
  rw [Finset.sum_congr rfl hF, ← Finset.mul_sum, hF0, ht0]
  linear_combination π * htel - π * t (K' + 1) * hwM
end ReciprocityTheory.ChartRestriction.L1
