-- Prove2me | solution 1 for PowerTwoChoices.Limit.expected_time_identity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:31:32.268645+00:00
-- url     : https://prove2.me/submissions/4c6a9c3d-419a-433e-b866-3dc863bc5527

import Mathlib
import Definitions.Def_PowerTwoChoices_Limit_SupermarketSystem

set_option autoImplicit false
open scoped ENNReal
open Filter Topology PowerTwoChoices.Limit

theorem solution (d : ℕ) (hd : 2 ≤ d) (x : ℕ → ℝ) (hx : IsState x)
    (hlim : Tendsto x atTop (𝓝 0)) :
    expectedTime d x = ∑' i : ℕ, ENNReal.ofReal (x i ^ d) := by
  obtain ⟨h0, hnn, hanti⟩ := hx
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, ∀ i, a i = x i ^ d := ⟨fun i => x i ^ d, fun _ => rfl⟩
  have ha_nn : ∀ i, 0 ≤ a i := fun i => by rw [ha]; exact pow_nonneg (hnn i) d
  have ha_anti : Antitone a := fun i j hij => by
    rw [ha, ha]; exact pow_le_pow_left₀ (hnn j) (hanti hij) d
  have ha_lim : Tendsto a atTop (𝓝 0) := by
    have := hlim.pow d
    have h2 : (fun i => x i ^ d) = a := funext fun i => (ha i).symm
    rw [h2] at this
    simpa [zero_pow (by omega : d ≠ 0)] using this
  have htel : ∀ j, ∑' k : ℕ, ENNReal.ofReal (a (j + k) - a (j + k + 1)) = ENNReal.ofReal (a j) := by
    intro j
    have hnn' : ∀ k, 0 ≤ a (j+k) - a (j+k+1) := fun k => sub_nonneg.2 (ha_anti (by omega))
    have hs : HasSum (fun k => a (j+k) - a (j+k+1)) (a j) := by
      rw [hasSum_iff_tendsto_nat_of_nonneg hnn']
      have : ∀ n, ∑ k ∈ Finset.range n, (a (j+k) - a (j+k+1)) = a j - a (j+n) := by
        intro n
        have e : ∀ k, j + (k+1) = j + k + 1 := fun k => by omega
        have := Finset.sum_range_sub' (fun k => a (j+k)) n
        simp only [e, Nat.add_zero] at this
        exact this
      simp_rw [this]
      have h2 : Tendsto (fun n => a (j+n)) atTop (𝓝 0) := by
        have := (Filter.tendsto_add_atTop_iff_nat (f := a) j).2 ha_lim
        simpa [add_comm] using this
      simpa using (tendsto_const_nhds (x := a j)).sub h2
    rw [← ENNReal.ofReal_tsum_of_nonneg hnn' hs.summable, hs.tsum_eq]
  have hterm : ∀ i : ℕ, ENNReal.ofReal ((i : ℝ) * (x (i - 1) ^ d - x i ^ d)) =
      ∑' j : ℕ, if j < i then ENNReal.ofReal (a (i-1) - a i) else 0 := by
    intro i
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg i), ENNReal.ofReal_natCast, ← ha, ← ha]
    rw [tsum_eq_sum (s := Finset.range i)]
    · rw [Finset.sum_congr rfl (g := fun _ => ENNReal.ofReal (a (i-1) - a i))
        (fun j hj => by simp [Finset.mem_range.1 hj] )]
      simp [mul_comm]
    · intro j hj
      have : ¬ j < i := fun h => hj (Finset.mem_range.2 h)
      simp [this]
  unfold expectedTime
  simp_rw [hterm]
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun j => ?_)
  rw [← ha j, ← htel j]
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℝ≥0∞, ∀ i, F i = if j < i then ENNReal.ofReal (a (i-1) - a i) else 0 :=
    ⟨fun i => if j < i then ENNReal.ofReal (a (i-1) - a i) else 0, fun _ => rfl⟩
  have key : ∑ i ∈ Finset.range (j+1), F i + ∑' i, F (i + (j+1)) = ∑' i, F i :=
    Summable.sum_add_tsum_nat_add' (f := F) (k := j+1) ENNReal.summable
  have h1 : ∑ i ∈ Finset.range (j+1), F i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have : ¬ j < i := by have := Finset.mem_range.1 hi; omega
    simp [hF, this]
  simp_rw [← hF]
  rw [h1, zero_add] at key
  rw [← key]
  refine tsum_congr (fun k => ?_)
  have e1 : k + (j+1) - 1 = j+k := by omega
  have e2 : k + (j+1) = j+k+1 := by omega
  rw [hF, if_pos (show j < k + (j+1) by omega), e1, e2]
