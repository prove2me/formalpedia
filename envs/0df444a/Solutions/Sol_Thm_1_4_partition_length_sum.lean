-- Prove2me | solution 1 for Thm_1_4.partition_length_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:49:11.624205+00:00
-- url     : https://prove2.me/submissions/a36bd3ac-5bde-4f2a-839f-f556f383ab07

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped BigOperators Pointwise Interval
noncomputable section

private noncomputable def ptNat {a b : ℝ} (P : Partition a b) (k : ℕ) : ℝ :=
  if hk : k ≤ P.n then
    P.pts ⟨k, Nat.lt_succ_of_le hk⟩
  else
    P.pts (Fin.last P.n)
private lemma ptNat_zero {a b : ℝ} (P : Partition a b) :
    ptNat P 0 = a := by
  unfold ptNat
  rw [dif_pos (Nat.zero_le P.n)]
  simpa using P.pts_start
private lemma ptNat_last {a b : ℝ} (P : Partition a b) :
    ptNat P P.n = b := by
  unfold ptNat
  rw [dif_pos le_rfl]
  have hfin :
      (⟨P.n, Nat.lt_succ_self P.n⟩ : Fin (P.n + 1)) = Fin.last P.n := by
    ext
    simp
  simpa [hfin] using P.pts_end
private lemma ptNat_of_lt {a b : ℝ} (P : Partition a b) {k : ℕ}
    (hk : k < P.n) :
    ptNat P k = P.pts (Fin.castSucc (⟨k, hk⟩ : Fin P.n)) := by
  unfold ptNat
  rw [dif_pos (le_of_lt hk)]
  congr
private lemma ptNat_succ_of_lt {a b : ℝ} (P : Partition a b) {k : ℕ}
    (hk : k < P.n) :
    ptNat P (k + 1) = P.pts (Fin.succ (⟨k, hk⟩ : Fin P.n)) := by
  unfold ptNat
  rw [dif_pos (Nat.succ_le_of_lt hk)]
  congr

theorem solution {a b : ℝ} (P : Partition a b) :
    (∑ i : Fin P.n, (P.pts i.succ - P.pts i.castSucc)) = b - a := by
  classical
  rw [Finset.sum_fin_eq_sum_range]
  have htel0 := Finset.sum_Ico_sub (ptNat P) (Nat.zero_le P.n)
  have hIco : Finset.Ico 0 P.n = Finset.range P.n := by
    ext k
    simp
  rw [hIco] at htel0
  have htel :
      (∑ k ∈ Finset.range P.n, (ptNat P (k + 1) - ptNat P k)) = b - a := by
    simpa [ptNat_zero, ptNat_last] using htel0
  trans (∑ k ∈ Finset.range P.n, (ptNat P (k + 1) - ptNat P k))
  · refine Finset.sum_congr rfl ?_
    intro k hk
    have hklt : k < P.n := Finset.mem_range.mp hk
    rw [ptNat_succ_of_lt P hklt, ptNat_of_lt P hklt]
    simp [hklt]
  · exact htel
