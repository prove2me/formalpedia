-- Prove2me | solution 1 for PersistClust.Count.descent_birth_sup_pin
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-12T19:59:42.467399+00:00
-- url     : https://prove2.me/submissions/455d5eb7-f83d-4fc5-8d45-151130267a4c

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
