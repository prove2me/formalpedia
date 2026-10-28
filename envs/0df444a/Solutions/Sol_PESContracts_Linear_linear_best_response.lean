-- Prove2me | solution 1 for PESContracts.Linear.linear_best_response
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:00:54.805344+00:00
-- url     : https://prove2.me/submissions/58050093-a3ae-42ac-bbb3-bc3650cb7724

import Mathlib
import Definitions.Def_PESContracts_Linear_Model

open PESContracts.Linear in
theorem solution (M : Params) (hM : M.Standing)
    (p : ℝ) (hp : 0 ≤ p) (θ : ℝ) (hθ : θ ∈ Set.Icc 0 1) :
    linAction M p θ ∈ Set.Icc 0 M.a0 ∧
    (∀ a ∈ Set.Icc 0 M.a0,
      linUtil M p θ a ≤ linUtil M p θ (linAction M p θ)) ∧
    (0 < p → ∀ a ∈ Set.Icc 0 M.a0,
      linUtil M p θ (linAction M p θ) ≤ linUtil M p θ a →
      a = linAction M p θ) := by
  obtain ⟨ha0, hh, -, -, -⟩ := hM
  obtain ⟨w, hw⟩ : ∃ w, w = p / M.h := ⟨_, rfl⟩
  have hla : linAction M p θ = min (θ * M.a0 + w) M.a0 := by unfold linAction; rw [hw]
  have hpw : p = M.h * w := by rw [hw]; field_simp
  rw [hla]; clear hla hw; subst hpw
  have hw0 : 0 ≤ w := by
    by_contra hc; push_neg at hc; nlinarith [mul_pos hh (neg_pos.2 hc)]
  have hU : ∀ a, linUtil M (M.h * w) θ a =
      if 0 ≤ a - θ * M.a0 then M.h * w * a - M.h / 2 * (a - θ * M.a0) ^ 2
      else M.h * w * a := by
    intro a; unfold linUtil cost; split_ifs <;> ring
  set t := θ * M.a0 with htdef
  have ht0 : 0 ≤ t := mul_nonneg hθ.1 ha0.le
  have ht1 : t ≤ M.a0 := by nlinarith [hθ.2]
  have hA : t ≤ min (t + w) M.a0 := le_min (by linarith) ht1
  have hUA : linUtil M (M.h * w) θ (min (t + w) M.a0) =
      M.h * w * min (t + w) M.a0 - M.h / 2 * (min (t + w) M.a0 - t) ^ 2 := by
    rw [hU, if_pos (by linarith)]
  have main : ∀ a ∈ Set.Icc 0 M.a0,
      linUtil M (M.h * w) θ a ≤ linUtil M (M.h * w) θ (min (t + w) M.a0) ∧
      (0 < M.h * w → linUtil M (M.h * w) θ (min (t + w) M.a0) ≤ linUtil M (M.h * w) θ a →
        a = min (t + w) M.a0) := by
    intro a ha
    rw [hUA, hU]
    rcases le_or_gt (t + w) M.a0 with hc | hc
    · rw [min_eq_left hc]
      split_ifs with hat
      · constructor
        · nlinarith [mul_nonneg hh.le (sq_nonneg (a - t - w))]
        · intro _ hle
          have h1 : (a - t - w) ^ 2 ≤ 0 := by
            by_contra hc'; push_neg at hc'; nlinarith [mul_pos hh hc']
          have h2 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm h1 (sq_nonneg _))
          linarith
      · push_neg at hat
        constructor
        · nlinarith [mul_nonneg (mul_nonneg hh.le hw0) (by linarith : (0:ℝ) ≤ t - a),
            mul_nonneg hh.le (sq_nonneg w)]
        · intro hpos hle
          exfalso
          nlinarith [mul_pos hpos (by linarith : (0:ℝ) < t - a), mul_nonneg hh.le (sq_nonneg w)]
    · rw [min_eq_right hc.le]
      split_ifs with hat
      · have hX : 0 ≤ (M.a0 - a) * (2 * w - (M.a0 - t) - (a - t)) :=
          mul_nonneg (by linarith [ha.2]) (by linarith [ha.2])
        constructor
        · nlinarith [mul_nonneg hh.le hX]
        · intro _ hle
          by_contra hne
          have hlt : a < M.a0 := lt_of_le_of_ne ha.2 hne
          have hY : 0 < (M.a0 - a) * (2 * w - (M.a0 - t) - (a - t)) :=
            mul_pos (by linarith) (by linarith)
          nlinarith [mul_pos hh hY]
      · push_neg at hat
        have hX : 0 ≤ (M.a0 - t) * (2 * w - (M.a0 - t)) :=
          mul_nonneg (by linarith) (by linarith)
        constructor
        · nlinarith [mul_nonneg hh.le hX, mul_nonneg (mul_nonneg hh.le hw0) (by linarith : (0:ℝ) ≤ t - a)]
        · intro hpos hle
          exfalso
          nlinarith [mul_nonneg hh.le hX, mul_pos hpos (by linarith : (0:ℝ) < t - a)]
  refine ⟨⟨le_trans ht0 hA, min_le_right _ _⟩, fun a ha => (main a ha).1,
    fun hpos a ha hle => (main a ha).2 hpos hle⟩
