-- Prove2me | solution 1 for PersistClust.Count.image_birth_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-12T18:24:27.483725+00:00
-- url     : https://prove2.me/submissions/e278bf34-c0e7-4b86-98e1-69629aa13eab

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

theorem rungB_level_le_bSup {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {t : ℝ} (E : comps stage J t) :
    t ≤ birthSup hLaw t E := by
  obtain ⟨s₀, hs₀⟩ := hTame.2.2
  have hBdd : BddAbove (AncSet hLaw t E) := by
    refine ⟨s₀, fun u hu => ?_⟩
    obtain ⟨-, C₂, -⟩ := hu
    have hstage : (stage u).Nonempty := by
      obtain ⟨x, hx, -⟩ := C₂.property
      exact ⟨x, hx⟩
    by_contra hle
    push_neg at hle
    exact hstage.ne_empty (hs₀ u hle.le)
  exact (rfl : birthSup hLaw t E = sSup (AncSet hLaw t E)).symm ▸
    (le_csSup hBdd ⟨le_rfl, E, t3_structMap_id hLaw t E⟩)

/-- Image-birth upper bound: under the interleaving squares (ii') and (iv'),
the birth-sup of the image cell phi_beta C is at most b + eps, where b is
the birth-sup of the twice-descended source cell (the crit-free descent
pin). -/
theorem solution {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameX : IsTameModule stageX JX) {α ε : ℝ} (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq2 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (y : comps stageY JY β'),
      ψ β hβ (structMap hLawY hle y) =
        structMap hLawX (show β - ε ≤ β' - ε by linarith) (ψ β' hβ' y))
    (hSq4 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (x : comps stageX JX β),
      ψ (β - ε) hβε (φ β hβ x) =
        structMap hLawX (show (β - ε) - ε ≤ β by linarith) x)
    {β b : ℝ} (hβ : α ≤ β) (hβε : α ≤ β - ε)
    (C : comps stageX JX β)
    (hDesc : birthSup hLawX ((β - ε) - ε)
        (structMap hLawX (show (β - ε) - ε ≤ β by linarith) C) = b) :
    birthSup hLawY (β - ε) (φ β hβ C) ≤ b + ε := by
  have hne : (AncSet hLawY (β - ε) (φ β hβ C)).Nonempty :=
    ⟨β - ε, le_rfl, φ β hβ C, t3_structMap_id hLawY (β - ε) (φ β hβ C)⟩
  refine csSup_le hne ?_
  intro u hu
  obtain ⟨huu, D₁, hD₁⟩ := hu
  have hαu : α ≤ u := le_trans hβε huu
  have hii := hSq2 (β - ε) u hβε hαu huu D₁
  rw [hD₁] at hii
  have hiv := hSq4 β hβ hβε C
  have hEq : structMap hLawX (show (β - ε) - ε ≤ u - ε by linarith) (ψ u hαu D₁)
      = structMap hLawX (show (β - ε) - ε ≤ β by linarith) C :=
    hii.symm.trans hiv
  have h1 : u - ε ≤ birthSup hLawX (u - ε) (ψ u hαu D₁) :=
    rungB_level_le_bSup hLawX hTameX (ψ u hαu D₁)
  have h2 : birthSup hLawX (u - ε) (ψ u hαu D₁)
      ≤ birthSup hLawX ((β - ε) - ε)
          (structMap hLawX (show (β - ε) - ε ≤ u - ε by linarith) (ψ u hαu D₁)) :=
    rungB_bSup_descend_ge hLawX hTameX (show (β - ε) - ε ≤ u - ε by linarith) (ψ u hαu D₁)
  have h4 : u - ε ≤ b :=
    (h1.trans (h2.trans (congrArg (birthSup hLawX ((β - ε) - ε)) hEq).le)).trans
      (le_of_eq hDesc)
  linarith
