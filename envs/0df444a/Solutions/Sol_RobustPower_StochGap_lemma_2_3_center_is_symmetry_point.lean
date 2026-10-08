-- Prove2me | solution 1 for RobustPower.StochGap.lemma_2_3_center_is_symmetry_point
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:57:02.016146+00:00
-- url     : https://prove2.me/submissions/510a46de-3a66-4b7b-af3b-2593bb8b9227

import Mathlib
import Definitions.Def_RobustPower_StochGap_SymmetricSets

namespace P2658cc63

open RobustPower.StochGap

theorem refl_mem {n : ℕ} {S : Set (Fin n → ℝ)} {u : Fin n → ℝ}
    (h : IsSymmetricAbout S u) {x : Fin n → ℝ} (hx : x ∈ S) : (2 : ℝ) • u - x ∈ S := by
  have h1 := (h.2 (x - u)).1 (by simpa using hx)
  have h2 : u - (x - u) = (2 : ℝ) • u - x := by rw [two_smul]; abel
  rwa [h2] at h1

theorem coord_bdd {n : ℕ} {S : Set (Fin n → ℝ)} (hbdd : Bornology.IsBounded S) (j : Fin n) :
    BddAbove ((fun x : Fin n → ℝ => x j) '' S) ∧ BddBelow ((fun x : Fin n → ℝ => x j) '' S) := by
  have hmono : Monotone (fun x : Fin n → ℝ => x j) := fun _ _ h => h j
  exact ⟨hmono.map_bddAbove hbdd.bddAbove, hmono.map_bddBelow hbdd.bddBelow⟩

theorem sum_eq {n : ℕ} {S : Set (Fin n → ℝ)} {u : Fin n → ℝ}
    (h : IsSymmetricAbout S u) (hbdd : Bornology.IsBounded S) (j : Fin n) :
    xl S j + xh S j = 2 * u j := by
  obtain ⟨hA, hB⟩ := coord_bdd hbdd j
  have hne : ((fun x : Fin n → ℝ => x j) '' S).Nonempty := ⟨u j, u, h.1, rfl⟩
  have hr : ∀ t ∈ (fun x : Fin n → ℝ => x j) '' S, 2 * u j - t ∈ (fun x : Fin n → ℝ => x j) '' S := by
    rintro t ⟨x, hx, rfl⟩
    exact ⟨_, refl_mem h hx, by simp [two_smul]; ring⟩
  simp only [xl, xh]
  apply le_antisymm
  · have : sSup ((fun x : Fin n → ℝ => x j) '' S) ≤ 2 * u j - sInf ((fun x : Fin n → ℝ => x j) '' S) := by
      apply csSup_le hne
      intro t ht
      have := csInf_le hB (hr t ht)
      linarith
    have : 2 * u j - sSup ((fun x : Fin n → ℝ => x j) '' S) ≤ sInf ((fun x : Fin n → ℝ => x j) '' S) := by
      apply le_csInf hne
      intro t ht
      have := le_csSup hA (hr t ht)
      linarith
    linarith
  · have : 2 * u j - sSup ((fun x : Fin n → ℝ => x j) '' S) ≤ sInf ((fun x : Fin n → ℝ => x j) '' S) := by
      apply le_csInf hne
      intro t ht
      have := le_csSup hA (hr t ht)
      linarith
    linarith

theorem center_eq {n : ℕ} {S : Set (Fin n → ℝ)} {u : Fin n → ℝ}
    (h : IsSymmetricAbout S u) (hbdd : Bornology.IsBounded S) :
    u = (1 / 2 : ℝ) • (xl S + xh S) := by
  funext j
  have := sum_eq h hbdd j
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  linarith

end P2658cc63

open RobustPower.StochGap in
theorem solution {n : ℕ} (S : Set (Fin n → ℝ))
    (hS : IsSymmetric S) (hbdd : Bornology.IsBounded S) :
    IsSymmetricAbout S ((1 / 2 : ℝ) • (xl S + xh S)) ∧
      (∀ u : Fin n → ℝ, IsSymmetricAbout S u → u = (1 / 2 : ℝ) • (xl S + xh S)) ∧
      ((∀ x ∈ S, 0 ≤ x) → ∀ x ∈ S, x ≤ (2 : ℝ) • ((1 / 2 : ℝ) • (xl S + xh S))) := by
  obtain ⟨u, hu⟩ := hS
  have hc := P2658cc63.center_eq hu hbdd
  refine ⟨hc ▸ hu, fun v hv => P2658cc63.center_eq hv hbdd, ?_⟩
  intro hpos x hx j
  obtain ⟨hA, hB⟩ := P2658cc63.coord_bdd hbdd j
  have h1 : x j ≤ xh S j := le_csSup hA ⟨x, hx, rfl⟩
  have h2 : 0 ≤ xl S j := le_csInf ⟨u j, u, hu.1, rfl⟩ (by
    rintro t ⟨y, hy, rfl⟩
    exact hpos y hy j)
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  linarith
