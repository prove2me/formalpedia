-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.TelescopingWeightedSums.wsum_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:25:36.279799+00:00
-- url     : https://prove2.me/submissions/1c8bd0f3-ee25-4729-a8b0-8cee198d0037

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TelescopingWeightedSums
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TelescopingWeightedSums_sum_tele
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD.TelescopingWeightedSums
open Finset
private lemma sum_sub_lo_mul_bounds_of_nonneg (S : Finset ℕ) (a d : ℕ → ℝ) (lo hi : ℝ)
    (hd : ∀ i ∈ S, 0 ≤ d i) (ha : ∀ i ∈ S, lo ≤ a i ∧ a i ≤ hi) :
    0 ≤ ∑ i ∈ S, (a i - lo) * d i ∧ ∑ i ∈ S, (a i - lo) * d i ≤ (hi - lo) * ∑ i ∈ S, d i := by
  constructor
  · exact Finset.sum_nonneg fun i hi' => mul_nonneg (by linarith [(ha i hi').1]) (hd i hi')
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi' =>
      mul_le_mul_of_nonneg_right (by linarith [(ha i hi').2]) (hd i hi')
private lemma sum_sub_lo_mul_bounds_of_nonpos (S : Finset ℕ) (a d : ℕ → ℝ) (lo hi : ℝ)
    (hd : ∀ i ∈ S, d i ≤ 0) (ha : ∀ i ∈ S, lo ≤ a i ∧ a i ≤ hi) :
    (hi - lo) * ∑ i ∈ S, d i ≤ ∑ i ∈ S, (a i - lo) * d i ∧ ∑ i ∈ S, (a i - lo) * d i ≤ 0 := by
  constructor
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi' =>
      mul_le_mul_of_nonpos_right (by linarith [(ha i hi').2]) (hd i hi')
  · exact Finset.sum_nonpos fun i hi' =>
      mul_nonpos_of_nonneg_of_nonpos (by linarith [(ha i hi').1]) (hd i hi')
end ReciprocityTheory.ChartRestriction.G.FD.TelescopingWeightedSums
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.TelescopingWeightedSums
open Finset
namespace ReciprocityTheory.ChartRestriction.G.FD.TelescopingWeightedSums
theorem _root_.solution {n p : ℕ} (hp : p ≤ n) (ρ : ℕ → ℝ) (hρ : ∀ i ≤ n, 0 < ρ i) (h0 : ρ 0 = 1)
    (hn : ρ n = 1)
    (hmono : ((∀ i, i < p → ρ i ≤ ρ (i + 1)) ∧ ∀ i, p ≤ i → i < n → ρ (i + 1) ≤ ρ i) ∨
      ((∀ i, i < p → ρ (i + 1) ≤ ρ i) ∧ ∀ i, p ≤ i → i < n → ρ i ≤ ρ (i + 1)))
    (a : ℕ → ℝ) (lo hi : ℝ) (ha : ∀ i < n, lo ≤ a i ∧ a i ≤ hi) :
    |∑ i ∈ range n, a i * (Real.log (ρ (i + 1)) - Real.log (ρ i))| ≤
      (hi - lo) * |Real.log (ρ p)| := by
  have hsplit : ∑ i ∈ range n, a i * (Real.log (ρ (i + 1)) - Real.log (ρ i)) =
      ∑ i ∈ range p, (a i - lo) * (Real.log (ρ (i + 1)) - Real.log (ρ i)) +
      ∑ i ∈ Ico p n, (a i - lo) * (Real.log (ρ (i + 1)) - Real.log (ρ i)) +
      lo * ∑ i ∈ range n, (Real.log (ρ (i + 1)) - Real.log (ρ i)) := by
    rw [Finset.sum_range_add_sum_Ico _ hp, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have htot : ∑ i ∈ range n, (Real.log (ρ (i + 1)) - Real.log (ρ i)) = 0 := by
    rw [Finset.sum_range_sub (fun i => Real.log (ρ i)) n, h0, hn]; simp
  have hL : ∑ i ∈ range p, (Real.log (ρ (i + 1)) - Real.log (ρ i)) = Real.log (ρ p) := by
    rw [Finset.sum_range_sub (fun i => Real.log (ρ i)) p, h0]; simp
  have hR : ∑ i ∈ Ico p n, (Real.log (ρ (i + 1)) - Real.log (ρ i)) = - Real.log (ρ p) := by
    rw [sum_tele (fun i => Real.log (ρ i)) hp, hn]; simp
  have haL : ∀ i ∈ range p, lo ≤ a i ∧ a i ≤ hi := fun i hi' =>
    ha i (lt_of_lt_of_le (Finset.mem_range.mp hi') hp)
  have haR : ∀ i ∈ Ico p n, lo ≤ a i ∧ a i ≤ hi := fun i hi' => ha i (Finset.mem_Ico.mp hi').2
  rw [hsplit, htot, mul_zero, add_zero]
  rcases hmono with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have dL : ∀ i ∈ range p, 0 ≤ Real.log (ρ (i + 1)) - Real.log (ρ i) := by
      intro i hi'
      have hip := Finset.mem_range.mp hi'
      have := Real.log_le_log (hρ i (by omega)) (h1 i hip)
      linarith
    have dR : ∀ i ∈ Ico p n, Real.log (ρ (i + 1)) - Real.log (ρ i) ≤ 0 := by
      intro i hi'
      have hip := Finset.mem_Ico.mp hi'
      have := Real.log_le_log (hρ (i + 1) (by omega)) (h2 i hip.1 hip.2)
      linarith
    obtain ⟨A1, A2⟩ := sum_sub_lo_mul_bounds_of_nonneg _ a _ lo hi dL haL
    obtain ⟨B1, B2⟩ := sum_sub_lo_mul_bounds_of_nonpos _ a _ lo hi dR haR
    rw [hL] at A2
    rw [hR] at B1
    have hLnn : 0 ≤ Real.log (ρ p) := hL ▸ Finset.sum_nonneg dL
    rw [abs_of_nonneg hLnn, abs_le]
    constructor <;> linarith
  · have dL : ∀ i ∈ range p, Real.log (ρ (i + 1)) - Real.log (ρ i) ≤ 0 := by
      intro i hi'
      have hip := Finset.mem_range.mp hi'
      have := Real.log_le_log (hρ (i + 1) (by omega)) (h1 i hip)
      linarith
    have dR : ∀ i ∈ Ico p n, 0 ≤ Real.log (ρ (i + 1)) - Real.log (ρ i) := by
      intro i hi'
      have hip := Finset.mem_Ico.mp hi'
      have := Real.log_le_log (hρ i (by omega)) (h2 i hip.1 hip.2)
      linarith
    obtain ⟨A1, A2⟩ := sum_sub_lo_mul_bounds_of_nonpos _ a _ lo hi dL haL
    obtain ⟨B1, B2⟩ := sum_sub_lo_mul_bounds_of_nonneg _ a _ lo hi dR haR
    rw [hL] at A1
    rw [hR] at B2
    have hLnp : Real.log (ρ p) ≤ 0 := hL ▸ Finset.sum_nonpos dL
    rw [abs_of_nonpos hLnp, abs_le]
    constructor <;> linarith
end ReciprocityTheory.ChartRestriction.G.FD.TelescopingWeightedSums
