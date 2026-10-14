-- Prove2me | solution 1 for PersistClust.Count.sync_comerge_images
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-13T08:22:09.445441+00:00
-- url     : https://prove2.me/submissions/a51db0b5-fc25-4c97-b14c-d1b41657ad90

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal


theorem t5_syncLow {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    {α ε : ℝ}
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x))
    {δ u : ℝ} (hδ : α ≤ δ) (hu : α ≤ u) (hle : δ ≤ u)
    (C : comps stageX JX u) (E : comps stageX JX δ)
    (hmerge : structMap hLawX hle C = E) :
    structMap hLawY (show δ - ε ≤ u - ε by linarith) (φ u hu C) = φ δ hδ E := by
  have h := hSq1 δ u hδ hu hle C
  rw [hmerge] at h
  exact h.symm


theorem solution {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    {α ε : ℝ}
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x))
    {δ u : ℝ} (hδ : α ≤ δ) (hu : α ≤ u) (hle : δ ≤ u)
    (C₁ C₂ : comps stageX JX u) (E : comps stageX JX δ)
    (hm₁ : structMap hLawX hle C₁ = E) (hm₂ : structMap hLawX hle C₂ = E) :
    structMap hLawY (show δ - ε ≤ u - ε by linarith) (φ u hu C₁) = φ δ hδ E ∧
    structMap hLawY (show δ - ε ≤ u - ε by linarith) (φ u hu C₂) = φ δ hδ E := by
  exact ⟨t5_syncLow hLawX hLawY φ hSq1 hδ hu hle C₁ E hm₁,
    t5_syncLow hLawX hLawY φ hSq1 hδ hu hle C₂ E hm₂⟩
