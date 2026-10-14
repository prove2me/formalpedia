-- Prove2me | solution 1 for PersistClust.Count.elder_absorb_birth_trap
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-13T08:26:07.370676+00:00
-- url     : https://prove2.me/submissions/3f2daea6-2fab-4849-963c-b5d180f5a2a2

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


theorem t5_hDescPin {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {s₀ b : ℝ} {C₀ : comps stage J s₀} (hb : birthSup hLaw s₀ C₀ = b)
    {β s : ℝ} (hs₀β : s₀ ≤ β) (hβs : s ≤ β) (hs₀s : s₀ ≤ s)
    {A : comps stage J β} (hA : birthSup hLaw β A = b)
    (hP : structMap hLaw hs₀β A = C₀) :
    birthSup hLaw s (structMap hLaw hβs A) = b := by
  have h1 : birthSup hLaw β A ≤ birthSup hLaw s (structMap hLaw hβs A) :=
    rungB_bSup_descend_ge hLaw hTame hβs A
  have h2 : birthSup hLaw s (structMap hLaw hβs A)
      ≤ birthSup hLaw s₀ (structMap hLaw hs₀s (structMap hLaw hβs A)) :=
    rungB_bSup_descend_ge hLaw hTame hs₀s (structMap hLaw hβs A)
  have h3 : structMap hLaw hs₀s (structMap hLaw hβs A) = C₀ := by
    rw [structMap_comp hLaw hs₀s hβs A]
    exact hP
  rw [h3] at h2
  have h4 : birthSup hLaw s (structMap hLaw hβs A) ≤ b := h2.trans_eq hb
  have h5 : b ≤ birthSup hLaw s (structMap hLaw hβs A) := hA ▸ h1
  exact le_antisymm h4 h5


theorem solution {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameX : IsTameModule stageX JX) (hTameY : IsTameModule stageY JY)
    {α ε : ℝ} (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq2 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (y : comps stageY JY β'),
      ψ β hβ (structMap hLawY hle y) =
        structMap hLawX (show β - ε ≤ β' - ε by linarith) (ψ β' hβ' y))
    (hSq4 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (x : comps stageX JX β),
      ψ (β - ε) hβε (φ β hβ x) =
        structMap hLawX (show (β - ε) - ε ≤ β by linarith) x)
    {b d β : ℝ} (hβ : α ≤ β) (hβε : α ≤ β - ε)
    {A : comps stageX JX β} (hA : birthSup hLawX β A = b)
    {s₀ : ℝ} {C₀ : comps stageX JX s₀} (hbC₀ : birthSup hLawX s₀ C₀ = b)
    (hs₀β : s₀ ≤ β) (hP : structMap hLawX hs₀β A = C₀)
    (hd : d + 2 * ε < β) {v : ℝ} (hv : d + ε < v) (hvE : v ≤ β - ε)
    (hvα : α ≤ v) (hvεα : α ≤ v - ε) (hs₀v : s₀ ≤ v - ε)
    {b3 : ℝ} (hM : birthSup hLawY v (structMap hLawY (show v ≤ β - ε by linarith)
        (φ β hβ A)) = b3) :
    b3 ≤ b + ε := by
  have hvεβ : v - ε ≤ β := by linarith
  -- identity (a) at v: ψ_v (descY (E, v)) = descX (A, v − ε).
  have hId : ψ v hvα (structMap hLawY (show v ≤ β - ε by linarith) (φ β hβ A))
      = structMap hLawX hvεβ A :=
    (hSq2 v (β - ε) hvα hβε (show v ≤ β - ε by linarith) (φ β hβ A)).trans
      ((congrArg (structMap hLawX (show v - ε ≤ (β - ε) - ε by linarith))
          (hSq4 β hβ hβε A)).trans
        (structMap_comp hLawX (show v - ε ≤ (β - ε) - ε by linarith)
          (show (β - ε) - ε ≤ β by linarith) A))
  -- the X-thread pin at level v − ε, from the census pin (design §2 / t5_hDescPin).
  have hCvB : birthSup hLawX (v - ε) (structMap hLawX hvεβ A) = b :=
    t5_hDescPin hLawX hTameX hbC₀ hs₀β (show v - ε ≤ β by linarith) hs₀v hA hP
  obtain ⟨stop, hstop⟩ := hTameX.2.2
  have hBddC : BddAbove (AncSet hLawX (v - ε) (structMap hLawX hvεβ A)) := by
    refine ⟨stop, fun w hw => ?_⟩
    obtain ⟨-, C₂, -⟩ := hw
    have hstage : (stageX w).Nonempty := by
      obtain ⟨x, hx, -⟩ := C₂.property
      exact ⟨x, hx⟩
    by_contra hle'
    push_neg at hle'
    exact hstage.ne_empty (hstop w hle'.le)
  rw [← hM]
  have hne : (AncSet hLawY v (structMap hLawY (show v ≤ β - ε by linarith)
      (φ β hβ A))).Nonempty :=
    ⟨v, le_rfl, structMap hLawY (show v ≤ β - ε by linarith) (φ β hβ A),
      t3_structMap_id hLawY v (structMap hLawY (show v ≤ β - ε by linarith)
        (φ β hβ A))⟩
  refine csSup_le hne ?_
  intro u hu
  obtain ⟨huu, D₁, hD₁⟩ := hu
  have hαu : α ≤ u := le_trans hvα huu
  have hii := hSq2 v u hvα hαu huu D₁
  rw [hD₁] at hii
  have hEq : structMap hLawX (show v - ε ≤ u - ε by linarith) (ψ u hαu D₁)
      = structMap hLawX hvεβ A := hii.symm.trans hId
  have hmem : u - ε ∈ AncSet hLawX (v - ε) (structMap hLawX hvεβ A) :=
    ⟨show v - ε ≤ u - ε by linarith, ψ u hαu D₁, hEq⟩
  have hub : u - ε ≤ birthSup hLawX (v - ε) (structMap hLawX hvεβ A) :=
    (rfl : birthSup hLawX (v - ε) (structMap hLawX hvεβ A)
        = sSup (AncSet hLawX (v - ε) (structMap hLawX hvεβ A))).symm ▸
      le_csSup hBddC hmem
  rw [hCvB] at hub
  linarith
