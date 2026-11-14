-- Prove2me | solution 1 for RvsCert.lemma_3_first_stage
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-13T19:59:55.555329+00:00
-- url     : https://prove2.me/submissions/f0148c16-dc6e-4fa8-8f19-64b33b2a43f0

import Definitions.Def_RvsCert_IsChampion

open RvsCert

namespace RvsCertFirstStage

/-- The claimed positions of a champion sum to (at most) the last card entry. -/
theorem sum_claimedPos_lt (n : ℕ) (hn : 0 < n) (x : Idx n → Bool) (a : Fin (2 * n) × Fin n)
    (ha : IsChampion n x a) : ∑ j : Fin (2 * n - 1), claimedPos n x a j < n := by
  obtain ⟨hmono, hlast, -⟩ := ha
  set Y : Fin (2 * n - 1) → ℕ := fun j => cardEntry n x a j with hY
  -- `F 0 = 0`, `F (k + 1) = Y k` (clamped to the last entry).
  let F : ℕ → ℕ := fun k =>
    if k = 0 then 0 else Y ⟨min (k - 1) (2 * n - 2), by omega⟩
  have hFmono : Monotone F := by
    intro k k' hk
    simp only [F]
    split_ifs with h1 h2
    · exact le_rfl
    · exact Nat.zero_le _
    · omega
    · exact hmono _ _ (by simp only [Fin.le_def]; omega)
  have hpos : ∀ j : Fin (2 * n - 1), claimedPos n x a j = F (j + 1) - F j := by
    intro j
    have hj := j.isLt
    simp only [claimedPos, F]
    congr 1
    · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, Nat.add_sub_cancel]
      congr 1
      ext
      simp only
      omega
    · by_cases h0 : (j : ℕ) = 0
      · simp [h0]
      · rw [dif_neg h0, if_neg h0]
        congr 1
        ext
        simp only
        omega
  have hsum : ∑ j : Fin (2 * n - 1), claimedPos n x a j = F (2 * n - 1) - F 0 := by
    simp only [hpos]
    rw [Fin.sum_univ_eq_sum_range (fun i => F (i + 1) - F i)]
    exact Finset.sum_range_tsub hFmono _
  rw [hsum]
  have hlastj := hlast ⟨2 * n - 2, by omega⟩ (by simp only; omega)
  have hF : F (2 * n - 1) = cardEntry n x a ⟨2 * n - 2, by omega⟩ := by
    simp only [F, Y]
    rw [if_neg (by omega)]
    congr 1
    ext
    simp only
    omega
  rw [hF]
  simp only [F, if_pos]
  omega

end RvsCertFirstStage

open RvsCertFirstStage in
theorem solution (n : ℕ) (hn : 0 < n) (x : Idx n → Bool) (a : Fin (2 * n) × Fin n)
    (ha : IsChampion n x a) :
    2 * (Finset.univ.filter fun j : Fin (2 * n - 1) =>
        raceEntry n x (raceOf a.1 j) ⟨0, hn⟩ = athleteCode n a).card ≥ 2 * n - 1 := by
  set P : Fin (2 * n - 1) → Prop := fun j =>
    raceEntry n x (raceOf a.1 j) ⟨0, hn⟩ = athleteCode n a with hP
  -- In every race where `a` is not first, its claimed position is at least `1`.
  have hnot : ∀ j ∈ Finset.univ.filter (fun j => ¬ P j), 1 ≤ claimedPos n x a j := by
    intro j hj
    rw [Finset.mem_filter] at hj
    by_contra h0
    have h0' : claimedPos n x a j = 0 := by omega
    exact hj.2 ((ha.2.2 j).2 ⟨0, hn⟩ |>.2 h0'.symm)
  have hcard_not : (Finset.univ.filter (fun j => ¬ P j)).card < n := by
    calc (Finset.univ.filter (fun j => ¬ P j)).card
        = ∑ j ∈ Finset.univ.filter (fun j => ¬ P j), 1 := by simp
      _ ≤ ∑ j ∈ Finset.univ.filter (fun j => ¬ P j), claimedPos n x a j :=
          Finset.sum_le_sum hnot
      _ ≤ ∑ j : Fin (2 * n - 1), claimedPos n x a j :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ < n := sum_claimedPos_lt n hn x a ha
  have htot := Finset.card_filter_add_card_filter_not (s := Finset.univ) P
  rw [Finset.card_univ, Fintype.card_fin] at htot
  show 2 * (Finset.univ.filter P).card ≥ 2 * n - 1
  omega
