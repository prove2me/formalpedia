-- Prove2me | solution 1 for ReliableFacilityLoc.LevelOrder.prob_pos_of_assigned
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:07:31.767314+00:00
-- url     : https://prove2.me/submissions/77c71b54-6304-400f-bab8-0818895ce50d

import Mathlib
import Definitions.Def_ReliableFacilityLoc_LevelOrder_RUFL

set_option autoImplicit false
open Finset
open ReliableFacilityLoc.LevelOrder

theorem solution {I J R : ℕ} (D : Instance I J R) (hq : ∀ k, 0 < D.q k)
    (X : Fin J → ℝ) (Y P : Fin I → Fin (J + 1) → Fin (R + 1) → ℝ) (hfeas : D.IsFeasible X Y P)
    (i : Fin I) (j : Fin (J + 1)) (r : Fin (R + 1)) (hj : Y i j r = 1) :
    0 < P i j r := by
  have hqe : ∀ j : Fin (J + 1), 0 < 1 - D.qExt j := by
    intro j
    induction j using Fin.lastCases with
    | last => simp [Instance.qExt]
    | cast k =>
      have := D.q_lt_one k
      simp only [Instance.qExt, Fin.lastCases_castSucc]
      linarith
  have hY0 : ∀ j r, 0 ≤ Y i j r := by
    intro j r
    rcases hfeas.Y_binary i j r with h | h <;> rw [h] <;> norm_num
  revert j
  induction r using Fin.induction with
  | zero =>
    intro j _
    rw [hfeas.prob_zero]
    exact hqe j
  | succ s ih =>
    intro j hj
    rw [hfeas.prob_succ]
    refine mul_pos (hqe j) ?_
    have hlev := hfeas.level_one i s.succ
    have hlev0 := hfeas.level_one i s.castSucc
    have hge : Y i j s.succ ≤ ∑ j', Y i j' s.succ :=
      Finset.single_le_sum (fun j' _ => hY0 j' _) (Finset.mem_univ j)
    have hnn : 0 ≤ ∑ s' ∈ Iio s.succ, Y i (Fin.last J) s' :=
      Finset.sum_nonneg (fun s' _ => hY0 _ _)
    have hz : ∑ s' ∈ Iio s.succ, Y i (Fin.last J) s' = 0 := by linarith
    have hzero : ∀ s' ∈ Iio s.succ, Y i (Fin.last J) s' = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun s' _ => hY0 _ _)).mp hz
    have hz0 : ∑ s' ∈ Iio s.castSucc, Y i (Fin.last J) s' = 0 :=
      Finset.sum_eq_zero (fun s' hs' =>
        hzero s' (Finset.mem_Iio.mpr (lt_trans (Finset.mem_Iio.mp hs') Fin.castSucc_lt_succ)))
    have hsum1 : ∑ j', Y i j' s.castSucc = 1 := by linarith
    obtain ⟨j', -, hj'⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (by rw [hsum1]; norm_num : ∑ j', Y i j' s.castSucc ≠ 0)
    have hj'1 : Y i j' s.castSucc = 1 := (hfeas.Y_binary i j' _).resolve_left hj'
    rcases Fin.eq_castSucc_or_eq_last j' with ⟨k0, rfl⟩ | rfl
    · refine Finset.sum_pos' (fun k _ => ?_) ⟨k0, Finset.mem_univ _, ?_⟩
      · rcases hfeas.Y_binary i k.castSucc s.castSucc with h | h
        · rw [h]; simp
        · rw [h]
          have h1 := ih k.castSucc h
          have h2 : 0 < D.q k / (1 - D.q k) := div_pos (hq k) (sub_pos.mpr (D.q_lt_one k))
          have := mul_pos h2 h1
          linarith
      · rw [hj'1]
        have h1 := ih k0.castSucc hj'1
        have h2 : 0 < D.q k0 / (1 - D.q k0) := div_pos (hq k0) (sub_pos.mpr (D.q_lt_one k0))
        have := mul_pos h2 h1
        linarith
    · have := hzero s.castSucc (Finset.mem_Iio.mpr Fin.castSucc_lt_succ)
      rw [this] at hj'1
      norm_num at hj'1
