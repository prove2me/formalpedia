-- Prove2me | solution 1 for TheoryOfGames.ThreePerson.strategic_equivalence_isomorphism
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:28:42.904689+00:00
-- url     : https://prove2.me/submissions/9037edc7-a336-4928-82a9-fb1227edfcb8

import Mathlib
import Definitions.Def_TheoryOfGames_ThreePerson_Solution
import Definitions.Def_TheoryOfGames_CharFun_StrategicEquivalence

open TheoryOfGames.ThreePerson


theorem solution {n : ℕ} (v v' : Finset (Fin n) → ℝ)
    (hv : TheoryOfGames.CharFun.IsCharFunction v) (hequiv : TheoryOfGames.CharFun.StrategicallyEquivalent v v') :
    ∃ f : (Fin n → ℝ) → (Fin n → ℝ),
      Set.BijOn f {α | IsImputation v α} {α' | IsImputation v' α'} ∧
      (∀ α : Fin n → ℝ, IsImputation v α →
        ∀ S : Finset (Fin n), IsEffective v S α ↔ IsEffective v' S (f α)) ∧
      (∀ α β : Fin n → ℝ, IsImputation v α → IsImputation v β →
        (Dominates v α β ↔ Dominates v' (f α) (f β))) ∧
      (∀ V : Set (Fin n → ℝ), (∀ α ∈ V, IsImputation v α) →
        (IsSolution v V ↔ IsSolution v' (f '' V))) := by
  obtain ⟨c, hc0, hc⟩ := hequiv
  have imp : ∀ β : Fin n → ℝ, IsImputation v β ↔ IsImputation v' (β + c) := by
    intro β
    unfold IsImputation
    simp only [hc, Finset.sum_singleton, Pi.add_apply, Finset.sum_add_distrib, hc0, add_zero,
      add_le_add_iff_right]
  have eff : ∀ (β : Fin n → ℝ) S, IsEffective v S β ↔ IsEffective v' S (β + c) := by
    intro β S
    unfold IsEffective
    simp only [hc, Pi.add_apply, Finset.sum_add_distrib, add_le_add_iff_right]
  have dom : ∀ α β : Fin n → ℝ, Dominates v α β ↔ Dominates v' (α + c) (β + c) := by
    intro α β
    unfold Dominates
    simp only [← eff, Pi.add_apply, add_lt_add_iff_right]
  have finj : Function.Injective (fun β : Fin n → ℝ => β + c) := fun a b h => add_right_cancel h
  refine ⟨fun β => β + c, ⟨fun β hβ => (imp β).mp hβ, finj.injOn, fun α' hα' => ?_⟩,
    fun α _ S => eff α S, fun α β _ _ => dom α β, fun V hV => ?_⟩
  · refine ⟨α' - c, ?_, by simp⟩
    show IsImputation v (α' - c)
    rw [imp]; simpa using hα'
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨α, hα, rfl⟩; exact (imp α).mp (h1 α hα)
    · rintro _ ⟨α, hα, rfl⟩ _ ⟨β, hβ, rfl⟩ hd
      exact h2 α hα β hβ ((dom α β).mpr hd)
    · intro β' hβ' hnot
      have hb : IsImputation v (β' - c) := by rw [imp]; simpa using hβ'
      have hnV : β' - c ∉ V := by
        intro h; exact hnot ⟨β' - c, h, by simp⟩
      obtain ⟨α, hα, hd⟩ := h3 _ hb hnV
      refine ⟨α + c, ⟨α, hα, rfl⟩, ?_⟩
      have := (dom α (β' - c)).mp hd
      simpa using this
  · rintro ⟨h1, h2, h3⟩
    refine ⟨hV, ?_, ?_⟩
    · intro α hα β hβ hd
      exact h2 _ ⟨α, hα, rfl⟩ _ ⟨β, hβ, rfl⟩ ((dom α β).mp hd)
    · intro β hβ hnot
      have hnot' : β + c ∉ (fun β => β + c) '' V := by
        rintro ⟨γ, hγ, he⟩
        exact hnot (finj he ▸ hγ)
      obtain ⟨_, ⟨α, hα, rfl⟩, hd⟩ := h3 _ ((imp β).mp hβ) hnot'
      exact ⟨α, hα, (dom α β).mpr hd⟩
