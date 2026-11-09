-- Prove2me | solution 1 for TenChallenges.frankl_singleton_member
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T22:51:55.891027+00:00
-- url     : https://prove2.me/submissions/90f8c502-dec8-4d79-848d-9bcee16ebe09

import Definitions.Def_TenChallenges_Challenge_09
import Mathlib.Tactic.Linarith

open Finset

theorem solution {U : Type*} [DecidableEq U] (F : Finset (Finset U))
    (huc : IsUnionClosed F) {x : U} (hx : ({x} : Finset U) ∈ F) :
    density F x ≥ 1 / 2 := by
  let P := F.filter (fun A => x ∈ A)
  let Q := F.filter (fun A => x ∉ A)
  have hsum : P.card + Q.card = F.card :=
    card_filter_add_card_filter_not (fun A => x ∈ A)
  have hinj : Q.card ≤ P.card := by
    refine card_le_card_of_injOn (fun A => {x} ∪ A) ?_ ?_
    · intro A hA
      rcases mem_filter.mp hA with ⟨hAF, _⟩
      exact mem_filter.mpr ⟨huc hx hAF, by simp⟩
    · intro A₁ hA₁ A₂ hA₂ heq
      have hx₁ : x ∉ A₁ := (mem_filter.mp hA₁).2
      have hx₂ : x ∉ A₂ := (mem_filter.mp hA₂).2
      have herase : (({x} ∪ A₁).erase x) = (({x} ∪ A₂).erase x) := congrArg (fun S => S.erase x) heq
      simpa [singleton_union, erase_insert hx₁, erase_insert hx₂] using herase
  have hF_ne : F.Nonempty := ⟨{x}, hx⟩
  have hF_pos : 1 ≤ F.card := card_pos.mpr hF_ne
  have hmax : max 1 F.card = F.card := max_eq_right hF_pos
  unfold density occurrences
  change (P.card : ℚ) / (max 1 F.card : ℕ) ≥ 1 / 2
  rw [hmax]
  have h2 : (F.card : ℚ) ≤ 2 * (P.card : ℚ) := by
    have hnat : F.card ≤ 2 * P.card := by omega
    exact_mod_cast hnat
  have hF_pos_q : (0 : ℚ) < (F.card : ℚ) := by exact_mod_cast (by omega : 0 < F.card)
  rw [ge_iff_le, div_le_div_iff₀ (by norm_num) hF_pos_q]
  linarith
