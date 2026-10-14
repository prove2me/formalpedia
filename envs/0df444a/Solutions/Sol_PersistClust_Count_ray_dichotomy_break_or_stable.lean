-- Prove2me | solution 1 for PersistClust.Count.ray_dichotomy_break_or_stable
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-13T08:30:03.422407+00:00
-- url     : https://prove2.me/submissions/55d066c8-50cc-4409-973a-8ec61d030cad

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal


theorem structMap_comp {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) {s t u : ℝ} (hst : s ≤ t) (htu : t ≤ u)
    (C : comps stage J u) :
    structMap hLaw hst (structMap hLaw htu C) = structMap hLaw (le_trans hst htu) C := by
  have hjoin : J s (compRep stage J t (structMap hLaw htu C)) (compRep stage J u C) := by
    have h1 : (fun x => {y | J t x y}) (compRep stage J t (structMap hLaw htu C)) =
        {y | J t (compRep stage J u C) y} :=
      (compRep_spec stage J t (structMap hLaw htu C)).2.trans (structMap_val hLaw htu C)
    have h2 : J t (compRep stage J t (structMap hLaw htu C)) (compRep stage J u C) := by
      have h3 : compRep stage J u C ∈ {y | J t (compRep stage J u C) y} :=
        hLaw.refl (hLaw.antitone htu (compRep_spec stage J u C).1)
      rw [← h1] at h3
      exact h3
    exact hLaw.compat hst h2
  have hval : (structMap hLaw hst (structMap hLaw htu C)).val =
      (structMap hLaw (le_trans hst htu) C).val := by
    ext y
    exact ⟨fun h => hLaw.trans (hLaw.symm hjoin) h, fun h => hLaw.trans hjoin h⟩
  exact Subtype.ext hval


theorem t3_structMap_id {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (t : ℝ) (C : comps stage J t) :
    structMap hLaw le_rfl C = C :=
  Subtype.ext (compRep_spec stage J t C).2


theorem rungB_bSup_descend_ge {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {t t' : ℝ} (hle : t' ≤ t) (E : comps stage J t) :
    birthSup hLaw t E ≤ birthSup hLaw t' (structMap hLaw hle E) := by
  obtain ⟨s₀, hs₀⟩ := hTame.2.2
  have hBddT : BddAbove (AncSet hLaw t' (structMap hLaw hle E)) := by
    refine ⟨s₀, fun u hu => ?_⟩
    obtain ⟨-, C₂, -⟩ := hu
    have hstage : (stage u).Nonempty := by
      obtain ⟨x, hx, -⟩ := C₂.property
      exact ⟨x, hx⟩
    by_contra hle'
    push_neg at hle'
    exact hstage.ne_empty (hs₀ u hle'.le)
  have hne : (AncSet hLaw t E).Nonempty := ⟨t, le_rfl, E, t3_structMap_id hLaw t E⟩
  refine csSup_le hne ?_
  intro u hu
  obtain ⟨hw', E', hE'⟩ := hu
  exact (rfl : birthSup hLaw t' (structMap hLaw hle E)
      = sSup (AncSet hLaw t' (structMap hLaw hle E))).symm ▸
    (le_csSup hBddT ⟨le_trans hle hw', E', by rw [← hE', structMap_comp hLaw hle hw' E']⟩)


theorem solution {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {w₀ α' b₂ : ℝ} (I : comps stage J w₀) (hI : birthSup hLaw w₀ I = b₂) (hα' : α' ≤ w₀) :
    (∀ (w : ℝ) (hw : w ≤ w₀), α' ≤ w → birthSup hLaw w (structMap hLaw hw I) = b₂)
    ∨ ∃ v : ℝ, α' ≤ v ∧ v ≤ w₀ ∧
      (∀ (ξ : ℝ) (hξ : ξ ≤ w₀), v < ξ → birthSup hLaw ξ (structMap hLaw hξ I) = b₂) ∧
      (∀ (ξ : ℝ) (hξ : ξ ≤ w₀), α' ≤ ξ → ξ < v →
        birthSup hLaw ξ (structMap hLaw hξ I) ≠ b₂) ∧
      (∀ (hvle : α' ≤ w₀), v ≤ α' →
        birthSup hLaw α' (structMap hLaw hvle I) ≠ b₂) := by
  -- descent-value monotonicity: lower level ⇒ weakly larger birth-sup
  have hmono : ∀ (w w' : ℝ) (hw : w ≤ w₀) (hw' : w' ≤ w₀), w ≤ w' →
      birthSup hLaw w' (structMap hLaw hw' I) ≤ birthSup hLaw w (structMap hLaw hw I) := by
    intro w w' hw hw' hww'
    have hr := rungB_bSup_descend_ge hLaw hTame hww' (structMap hLaw hw' I)
    have hDw : structMap hLaw hww' (structMap hLaw hw' I) = structMap hLaw hw I := by
      rw [structMap_comp hLaw hww' hw' I]
    rw [hDw] at hr
    exact hr
  -- floor: every descent's birth-sup is at least `b₂`
  have hfloor : ∀ (w : ℝ) (hw : w ≤ w₀), b₂ ≤ birthSup hLaw w (structMap hLaw hw I) := by
    intro w hw
    have hr := rungB_bSup_descend_ge hLaw hTame hw I
    rw [hI] at hr
    exact hr
  by_cases hC : ∃ (w : ℝ) (hw : w ≤ w₀),
      α' ≤ w ∧ birthSup hLaw w (structMap hLaw hw I) ≠ b₂
  · obtain ⟨w₁, hw₁, hα'w₁, hne⟩ := hC
    set C : Set ℝ := {w : ℝ | ∃ (hw : w ≤ w₀), α' ≤ w ∧
        birthSup hLaw w (structMap hLaw hw I) ≠ b₂} with hCdef
    have hw₁C : w₁ ∈ C := ⟨hw₁, hα'w₁, hne⟩
    have hCne : C.Nonempty := ⟨w₁, hw₁C⟩
    have hCbdd : BddAbove C := ⟨w₀, fun w hw => by obtain ⟨hwle, -⟩ := hw; exact hwle⟩
    have hvw₁ : w₁ ≤ sSup C := le_csSup hCbdd hw₁C
    refine Or.inr ⟨sSup C, le_trans hα'w₁ hvw₁, csSup_le hCne ?_, ?_, ?_, ?_⟩
    · intro w hw
      obtain ⟨hwle, -⟩ := hw
      exact hwle
    · intro ξ hξ hvξ
      by_contra hneξ
      have hα'ξ : α' ≤ ξ := by linarith
      have hξle : ξ ≤ sSup C := le_csSup hCbdd ⟨hξ, hα'ξ, hneξ⟩
      linarith
    · intro ξ hξ hα'ξ hξv
      by_cases heq0 : birthSup hLaw ξ (structMap hLaw hξ I) = b₂
      · -- all levels in `[ξ, w₀]` have value `b₂` — boundary contradiction
        have hall : ∀ (ξ' : ℝ) (hξ' : ξ' ≤ w₀), ξ ≤ ξ' →
            birthSup hLaw ξ' (structMap hLaw hξ' I) = b₂ := by
          intro ξ' hξ' hξξ'
          have h1 := hmono ξ ξ' hξ hξ' hξξ'
          rw [heq0] at h1
          have h2 := hfloor ξ' hξ'
          linarith
        have hsub : ∀ w ∈ C, w < ξ := by
          intro w hw
          obtain ⟨hwle, hα'w, hwne⟩ := hw
          by_cases hlex : ξ ≤ w
          · exact absurd (hall w hwle hlex) hwne
          · exact not_le.mp hlex
        have hCle : sSup C ≤ ξ := csSup_le hCne (fun w hw => le_of_lt (hsub w hw))
        linarith
      · exact heq0
    · -- window-bottom value: if the boundary sits at or below the window bottom, the
      -- descent at the window bottom is off-value (the off-set concentrates there)
      intro hvle hvα'
      have hallC : ∀ w ∈ C, w = α' := by
        intro w hw
        have hwle : w ≤ sSup C := le_csSup hCbdd hw
        obtain ⟨-, hα'w, -⟩ := hw
        exact le_antisymm (by linarith) hα'w
      have hw₁eq : w₁ = α' := hallC w₁ hw₁C
      subst w₁
      exact hne
  · refine Or.inl ?_
    intro w hw hα'w
    by_contra hne
    exact hC ⟨w, hw, hα'w, hne⟩
