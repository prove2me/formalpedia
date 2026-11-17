-- Prove2me | solution 1 for Thm_1_4.partition_integral_between_lower_upper_id
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:41:23.578286+00:00
-- url     : https://prove2.me/submissions/2d479f6a-482b-4f59-b87c-e2a521f852c6

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_4_F003
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic
import Theorems.Thm_Thm_1_4_cell_integral_between_lower_upper_id
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators Pointwise Interval
open Set MeasureTheory DarbouxRS Thm_1_4
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

private lemma partition_integral_sum {g : ℝ → ℝ} {a b : ℝ}
    (hg : ContinuousOn g (Set.Icc a b))
    (P : Partition a b) :
    (∑ i : Fin P.n,
        ∫ x in P.pts i.castSucc..P.pts i.succ, g x) =
      ∫ x in a..b, g x := by
  classical
  rw [Finset.sum_fin_eq_sum_range]

  have hcellIntNat :
      ∀ k < P.n, IntervalIntegrable g volume (ptNat P k) (ptNat P (k + 1)) := by
    intro k hk
    let i : Fin P.n := ⟨k, hk⟩
    have huv : P.pts i.castSucc ≤ P.pts i.succ :=
      le_of_lt (P.strict_mono Fin.castSucc_lt_succ)
    have hgcell :
        ContinuousOn g (Set.Icc (P.pts i.castSucc) (P.pts i.succ)) :=
      hg.mono (DarbouxRS.subinterval_subset_Icc_core P (i := i))
    have hInt :
        IntervalIntegrable g volume (P.pts i.castSucc) (P.pts i.succ) :=
      ContinuousOn.intervalIntegrable_of_Icc huv hgcell

    have hleft : ptNat P k = P.pts i.castSucc := by
      rw [ptNat_of_lt P hk]

    have hright : ptNat P (k + 1) = P.pts i.succ := by
      rw [ptNat_succ_of_lt P hk]


    simpa [hleft, hright] using hInt

  have hsum0 :=
    intervalIntegral.sum_integral_adjacent_intervals hcellIntNat

  have hsum :
      (∑ k ∈ Finset.range P.n,
          ∫ x in ptNat P k..ptNat P (k + 1), g x) =
        ∫ x in a..b, g x := by
    simpa [ptNat_zero, ptNat_last] using hsum0

  trans
      (∑ k ∈ Finset.range P.n,
          ∫ x in ptNat P k..ptNat P (k + 1), g x)
  · refine Finset.sum_congr rfl ?_
    intro k hk
    have hklt : k < P.n := Finset.mem_range.mp hk
    rw [dif_pos hklt]
    rw [ptNat_of_lt P hklt, ptNat_succ_of_lt P hklt]

  · exact hsum

theorem solution {g : ℝ → ℝ} {a b : ℝ}
    (hg : ContinuousOn g (Set.Icc a b)) (P : Partition a b) :
    lowerSum P g (fun x => x) ≤ ∫ x in a..b, g x ∧
      ∫ x in a..b, g x ≤ upperSum P g (fun x => x) := by
  have hs := partition_integral_sum hg P
  constructor
  · calc
      lowerSum P g (fun x => x) =
          (∑ i : Fin P.n, lowerStep P g i * (P.pts i.succ - P.pts i.castSucc)) := by
        unfold lowerSum
        simp
      _ ≤ (∑ i : Fin P.n, ∫ x in P.pts i.castSucc..P.pts i.succ, g x) := by
        apply Finset.sum_le_sum
        intro i _
        exact (cell_integral_between_lower_upper_id hg P i).1
      _ = ∫ x in a..b, g x := hs
  · calc
      (∫ x in a..b, g x) =
          (∑ i : Fin P.n, ∫ x in P.pts i.castSucc..P.pts i.succ, g x) := hs.symm
      _ ≤ (∑ i : Fin P.n, upperStep P g i * (P.pts i.succ - P.pts i.castSucc)) := by
        apply Finset.sum_le_sum
        intro i _
        exact (cell_integral_between_lower_upper_id hg P i).2
      _ = upperSum P g (fun x => x) := by
        unfold upperSum
        simp
