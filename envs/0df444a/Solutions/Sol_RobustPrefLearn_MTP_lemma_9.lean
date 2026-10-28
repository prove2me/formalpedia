-- Prove2me | solution 1 for RobustPrefLearn.MTP.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:17:53.194983+00:00
-- url     : https://prove2.me/submissions/77ef6b46-f48c-439e-bd8b-1d58d8385e31

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_OA

open scoped ENNReal

namespace Aux_RobustPrefLearn_lemma_9
open RobustPrefLearn.MTP

theorem G_eq (p : ℝ) : ∀ N : ℕ, 1 ≤ N →
    ∑ n ∈ Finset.Icc 2 N, bSeq p n * (1 / aSeq p n - 1 / aSeq p (n + 1)) =
      ∑ m ∈ Finset.Icc 2 (N + 1), muSeq p m - bSeq p (N + 1) / aSeq p (N + 1) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base =>
    have e1 : Finset.Icc 2 1 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by norm_num)
    have e2 : Finset.Icc 2 (1 + 1) = ({2} : Finset ℕ) := Finset.Icc_self 2
    rw [e1, e2, Finset.sum_empty, Finset.sum_singleton, muSeq, if_pos rfl]
    ring
  | succ N hN ih =>
    rw [Finset.sum_Icc_succ_top (show 2 ≤ N + 1 by omega), ih,
      Finset.sum_Icc_succ_top (show 2 ≤ N + 1 + 1 by omega)]
    have hmu : muSeq p (N + 1 + 1) =
        (bSeq p (N + 1 + 1) - bSeq p (N + 1)) / aSeq p (N + 1 + 1) := by
      rw [muSeq, if_neg (by omega), Nat.add_sub_cancel]
    rw [hmu]
    ring

end Aux_RobustPrefLearn_lemma_9

open RobustPrefLearn.MTP in
theorem solution (K : ℕ) (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    uStar K p = lStar K p := by
  obtain ⟨M, rfl⟩ : ∃ M, K = M + 1 := ⟨K - 1, by omega⟩
  unfold uStar lStar
  congr 1
  rw [Finset.sum_Icc_succ_top (show 2 ≤ M + 1 by omega)]
  have h1 : ∑ n ∈ Finset.Icc 2 M, lamStar (M + 1) p n =
      ∑ n ∈ Finset.Icc 2 M, bSeq p n * (1 / aSeq p n - 1 / aSeq p (n + 1)) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    rw [lamStar, if_pos (by omega)]
  rw [h1, Aux_RobustPrefLearn_lemma_9.G_eq p M (by omega), lamStar, if_neg (lt_irrefl _)]
  ring
