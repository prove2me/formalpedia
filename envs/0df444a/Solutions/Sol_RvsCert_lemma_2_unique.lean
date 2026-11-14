-- Prove2me | solution 1 for RvsCert.lemma_2_unique
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-13T19:59:54.58359+00:00
-- url     : https://prove2.me/submissions/142436aa-fa7f-401a-ba56-a295aa8e570e

import Definitions.Def_RvsCert_IsChampion

open RvsCert

namespace RvsCertUnique

/-- Two distinct countries `c < c'` meet in a common race. -/
theorem common_race_lt {n : ℕ} (c c' : Fin (2 * n)) (h : c < c') :
    ∃ j j' : Fin (2 * n - 1), raceOf c j = raceOf c' j' := by
  have h1 : (c' : ℕ) < 2 * n := c'.isLt
  have h2 : (c : ℕ) < c' := h
  refine ⟨⟨c' - 1, by omega⟩, ⟨c, by omega⟩, ?_⟩
  have hA : ¬ ((c' : ℕ) - 1 < c) := by omega
  apply Subtype.ext
  simp only [raceOf, opponent, hA, h2, dif_neg, dif_pos, if_neg, if_pos,
    not_false_eq_true]
  ext
  · simp
  · simp; omega

/-- Any two countries share a race. -/
theorem common_race {n : ℕ} (hn : 0 < n) (c c' : Fin (2 * n)) :
    ∃ j j' : Fin (2 * n - 1), raceOf c j = raceOf c' j' := by
  rcases lt_trichotomy c c' with h | h | h
  · exact common_race_lt c c' h
  · subst h
    exact ⟨⟨0, by omega⟩, ⟨0, by omega⟩, rfl⟩
  · obtain ⟨j, j', hj⟩ := common_race_lt c' c h
    exact ⟨j', j, hj.symm⟩

theorem athleteCode_injective (n : ℕ) (a a' : Fin (2 * n) × Fin n)
    (h : athleteCode n a = athleteCode n a') : a = a' := by
  unfold athleteCode at h
  have hb : (a.2 : ℕ) < n := a.2.isLt
  have hb' : (a'.2 : ℕ) < n := a'.2.isLt
  have h' : (a.1 : ℕ) * n + a.2 = (a'.1 : ℕ) * n + a'.2 := by omega
  have hc : (a.1 : ℕ) = a'.1 := by
    have e1 : ((a.1 : ℕ) * n + a.2) / n = a.1 := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hb, zero_add]
    have e2 : ((a'.1 : ℕ) * n + a'.2) / n = a'.1 := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hb', zero_add]
    rw [← e1, ← e2, h']
  have hb2 : (a.2 : ℕ) = a'.2 := by rw [hc] at h'; omega
  exact Prod.ext (Fin.ext hc) (Fin.ext hb2)

end RvsCertUnique

open RvsCertUnique in
theorem solution (n : ℕ) (hn : 0 < n) (x : Idx n → Bool) (a a' : Fin (2 * n) × Fin n)
    (ha : IsChampion n x a) (ha' : IsChampion n x a') : a = a' := by
  obtain ⟨j, j', hjj⟩ := common_race hn a.1 a'.1
  obtain ⟨hp, hpos⟩ := ha.2.2 j
  obtain ⟨hp', hpos'⟩ := ha'.2.2 j'
  set p := claimedPos n x a j
  set p' := claimedPos n x a' j'
  have hcode : 0 < athleteCode n a := by unfold athleteCode; omega
  have hcode' : 0 < athleteCode n a' := by unfold athleteCode; omega
  rcases lt_trichotomy p p' with h | h | h
  · -- position `p` is `⊥` for `a'` but holds `a`
    have e1 := (hpos ⟨p, hp⟩).2 rfl
    have e2 := (hpos' ⟨p, hp⟩).1 h
    rw [← hjj] at e2
    omega
  · have e1 := (hpos ⟨p, hp⟩).2 rfl
    have e2 := (hpos' ⟨p, hp⟩).2 h
    rw [← hjj] at e2
    exact athleteCode_injective n a a' (e1.symm.trans e2)
  · have e1 := (hpos' ⟨p', hp'⟩).2 rfl
    have e2 := (hpos ⟨p', hp'⟩).1 h
    rw [hjj] at e2
    omega
