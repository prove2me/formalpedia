-- Prove2me | solution 1 for PersistClust.Count.census_band_reduction
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-14T09:11:09.047823+00:00
-- url     : https://prove2.me/submissions/974e1818-04fa-45da-b8c0-bfc2d0bff357

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

theorem t3_fresh_in_critSet {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {τ : ℝ} {C : comps stage J τ} (h : IsFresh hLaw τ C) : τ ∈ critSet hTame := by
  by_contra hτT
  set T := critSet hTame with hTdef
  obtain ⟨hrep, -⟩ := compRep_spec stage J τ C
  obtain ⟨s, hτs, hTfree⟩ : ∃ s : ℝ, τ < s ∧ (∀ u ∈ T, u < τ ∨ s < u) := by
    by_cases hUp : (T.filter (fun u => τ < u)).Nonempty
    · have hminmem : (T.filter (fun u => τ < u)).min' hUp ∈ (T.filter (fun u => τ < u)) :=
        Finset.min'_mem _ hUp
      have hτmin : τ < (T.filter (fun u => τ < u)).min' hUp := (Finset.mem_filter.mp hminmem).2
      refine ⟨(τ + (T.filter (fun u => τ < u)).min' hUp) / 2, by linarith, ?_⟩
      intro u hu
      by_cases huτ : u < τ
      · exact Or.inl huτ
      · right
        have hτu : τ < u := by
          rcases lt_or_eq_of_le (not_lt.mp huτ) with hlt | heq
          · exact hlt
          · exact absurd (heq ▸ hu) hτT
        have huIs : u ∈ (T.filter (fun u => τ < u)) := Finset.mem_filter.mpr ⟨hu, hτu⟩
        have hmin : (T.filter (fun u => τ < u)).min' hUp ≤ u := Finset.min'_le _ u huIs
        linarith
    · refine ⟨τ + 1, by linarith, ?_⟩
      intro u hu
      by_cases huτ : u < τ
      · exact Or.inl huτ
      · right
        have hτu : τ < u := by
          rcases lt_or_eq_of_le (not_lt.mp huτ) with hlt | heq
          · exact hlt
          · exact absurd (heq ▸ hu) hτT
        have : u ∈ (T.filter (fun u => τ < u)) := Finset.mem_filter.mpr ⟨hu, hτu⟩
        exact absurd (Set.nonempty_of_mem this) hUp
  obtain ⟨hdir, -⟩ := critSet_spec hTame τ s (le_of_lt hτs) hTfree
  obtain ⟨y, hy, hjy⟩ := hdir (compRep stage J τ C) hrep
  have hcell : ∃ p : ι, p ∈ stage s ∧ ({w | J s p w} : Set ι) = {z | J s y z} := ⟨y, hy, rfl⟩
  have hmem : ({z | J s y z} : Set ι) ∈ ((fun x => {w | J s x w}) '' stage s) := hcell
  set M : comps stage J s := Subtype.mk {z | J s y z} hmem with hM
  have hJyr : J s y (compRep stage J s M) := by
    have hy' : y ∈ ({z | J s y z} : Set ι) := hLaw.refl hy
    have hsp' : (fun x => {w | J s x w}) (compRep stage J s M) = {z | J s y z} := by
      rw [(compRep_spec stage J s M).2, hM]
    rw [← hsp'] at hy'
    exact hLaw.symm hy'
  have hτr : J τ (compRep stage J s M) y :=
    hLaw.compat (le_of_lt hτs) (hLaw.symm hJyr)
  have hval : (structMap hLaw (le_of_lt hτs) M).val = C.val := by
    rw [← (compRep_spec stage J τ C).2]
    simp only [structMap_val]
    ext z
    exact ⟨fun hz => hLaw.trans hjy (hLaw.trans (hLaw.symm hτr) hz),
           fun hz => hLaw.trans hτr (hLaw.trans (hLaw.symm hjy) hz)⟩
  exact h s hτs M (Subtype.ext hval)

theorem t3_structMap_id {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (t : ℝ) (C : comps stage J t) :
    structMap hLaw le_rfl C = C :=
  Subtype.ext (compRep_spec stage J t C).2

theorem t3_windowEx {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {t β : ℝ} {C : comps stage J t}
    (hBne : (AncSet hLaw t C).Nonempty) (hBdd : BddAbove (AncSet hLaw t C))
    (hβ : β = birthSup hLaw t C) (hβcrit : β ∉ (critSet hTame : Set ℝ))
    (hstrict : ∃ u, u ∈ AncSet hLaw t C ∧ t < u) :
    ∃ u δ : ℝ, 0 < δ ∧ u ∈ AncSet hLaw t C ∧
      (∀ w ∈ critSet hTame, w < u ∨ β + δ < w) := by
  classical
  have hβsup : β = sSup (AncSet hLaw t C) := hβ
  obtain ⟨u₀, hu₀, htu₀⟩ := hstrict
  obtain ⟨u, hu, hup, hub⟩ :
      ∃ u, u ∈ AncSet hLaw t C ∧ (∀ w ∈ critSet hTame, w < β → w < u) ∧ u ≤ β := by
    by_cases hPne : ((critSet hTame).filter (fun w => w < β)).Nonempty
    · have hmaxlt : ((critSet hTame).filter (fun w => w < β)).max' hPne < β :=
        (Finset.mem_filter.mp (Finset.max'_mem _ hPne)).2
      have happ : ∃ u ∈ AncSet hLaw t C,
          ((critSet hTame).filter (fun w => w < β)).max' hPne < u := by
        refine (lt_csSup_iff hBdd hBne).mp ?_
        rw [← hβsup]
        linarith
      obtain ⟨u, hu, hgt⟩ := happ
      refine ⟨u, hu, fun w hw hwβ => ?_, hβsup.symm ▸ le_csSup hBdd hu⟩
      · have hwp : w ≤ ((critSet hTame).filter (fun w => w < β)).max' hPne :=
          Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hw, hwβ⟩)
        linarith
    · refine ⟨u₀, hu₀, fun w hw hwβ => ?_, hβsup.symm ▸ le_csSup hBdd hu₀⟩
      · exact absurd (show ((critSet hTame).filter (fun w => w < β)).Nonempty from
          ⟨w, Finset.mem_filter.mpr ⟨hw, hwβ⟩⟩) hPne
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ w ∈ critSet hTame, w < u ∨ β + δ < w := by
    by_cases hNne : ((critSet hTame).filter (fun w => β < w)).Nonempty
    · have hβlt : β < ((critSet hTame).filter (fun w => β < w)).min' hNne :=
        (Finset.mem_filter.mp (Finset.min'_mem _ hNne)).2
      refine ⟨(((critSet hTame).filter (fun w => β < w)).min' hNne - β) / 2, by linarith, fun w hw => ?_⟩
      by_cases hwu : w < u
      · exact Or.inl hwu
      · right
        have hwβ : β < w := by
          rcases lt_trichotomy w β with hlt | heq | hgt
          · exact absurd (hup w hw hlt) hwu
          · exact absurd (heq ▸ hw) hβcrit
          · exact hgt
        have hmin : ((critSet hTame).filter (fun w => β < w)).min' hNne ≤ w :=
          Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hw, hwβ⟩)
        linarith
    · refine ⟨1, by norm_num, fun w hw => ?_⟩
      by_cases hwu : w < u
      · exact Or.inl hwu
      · right
        have hwβ : β < w := by
          rcases lt_trichotomy w β with hlt | heq | hgt
          · exact absurd (hup w hw hlt) hwu
          · exact absurd (heq ▸ hw) hβcrit
          · exact hgt
        exact (hNne ⟨w, Finset.mem_filter.mpr ⟨hw, hwβ⟩⟩).elim
  exact ⟨u, δ, hδpos, hu, hδ⟩

theorem t3_ancSup_mem {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {t β : ℝ} {C : comps stage J t}
    {u δ : ℝ} (hu : u ∈ AncSet hLaw t C) (hδ : 0 < δ)
    (hav : ∀ w ∈ critSet hTame, w < u ∨ β + δ < w)
    (hule : u ≤ β + δ) :
    β + δ ∈ AncSet hLaw t C := by
  obtain ⟨huu, C', hC'⟩ := hu
  have hdir := (critSet_spec hTame u (β + δ) hule hav).1
  have hspec := compRep_spec stage J u C'
  obtain ⟨y, hy, hJy⟩ := hdir (compRep stage J u C') hspec.1
  have hprop : {z | J (β + δ) y z} ∈ (fun x => {z | J (β + δ) x z}) '' stage (β + δ) :=
    ⟨y, hy, rfl⟩
  have hstep : structMap hLaw hule ⟨{z | J (β + δ) y z}, hprop⟩ = C' := by
    refine Subtype.ext ?_
    rw [structMap_val]
    rw [show C'.val = ((fun x => {z | J u x z}) (compRep stage J u C')) from (compRep_spec stage J u C').2.symm]
    ext zz
    constructor
    · intro hz
      have hspec2 := compRep_spec stage J (β + δ) ⟨{z | J (β + δ) y z}, hprop⟩
      have hyrep : J (β + δ) (compRep stage J (β + δ) ⟨{z | J (β + δ) y z}, hprop⟩) y := by
        have hbot : y ∈ ((fun x => {z | J (β + δ) x z}) (compRep stage J (β + δ) ⟨{z | J (β + δ) y z}, hprop⟩)) := by
          rw [hspec2.2]
          exact hLaw.refl hy
        exact hbot
      have hrepu : J u (compRep stage J (β + δ) ⟨{z | J (β + δ) y z}, hprop⟩) y :=
        hLaw.compat hule hyrep
      have hjoin : J u (compRep stage J (β + δ) ⟨{z | J (β + δ) y z}, hprop⟩)
          (compRep stage J u C') :=
        hLaw.trans hrepu (hLaw.symm hJy)
      exact hLaw.trans (hLaw.symm hjoin) hz
    · intro hz
      have hspec2 := compRep_spec stage J (β + δ) ⟨{z | J (β + δ) y z}, hprop⟩
      have hyrep : J (β + δ) (compRep stage J (β + δ) ⟨{z | J (β + δ) y z}, hprop⟩) y := by
        have hbot : y ∈ ((fun x => {z | J (β + δ) x z}) (compRep stage J (β + δ) ⟨{z | J (β + δ) y z}, hprop⟩)) := by
          rw [hspec2.2]
          exact hLaw.refl hy
        exact hbot
      have hrepu : J u (compRep stage J (β + δ) ⟨{z | J (β + δ) y z}, hprop⟩) y :=
        hLaw.compat hule hyrep
      exact hLaw.trans (hLaw.trans hrepu (hLaw.symm hJy)) hz
  have hfinal : structMap hLaw (le_trans huu hule) ⟨{z | J (β + δ) y z}, hprop⟩ = C := by
    rw [← structMap_comp hLaw huu hule ⟨{z | J (β + δ) y z}, hprop⟩]
    rw [hstep]
    exact hC'
  exact ⟨le_trans huu hule, ⟨{z | J (β + δ) y z}, hprop⟩, hfinal⟩

theorem t3_bSup_self_crit {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {t : ℝ} {C : comps stage J t}
    (h : birthSup hLaw t C = t) : t ∈ critSet hTame := by
  apply t3_fresh_in_critSet hLaw hTame
  intro s hs C' hC'
  obtain ⟨s₀, hs₀⟩ := hTame.2.2
  have hBdd : BddAbove (AncSet hLaw t C) := by
    refine ⟨s₀, fun u hu => ?_⟩
    obtain ⟨-, C₂, -⟩ := hu
    have hstage : (stage u).Nonempty := by
      obtain ⟨x, hx, -⟩ := C₂.property
      exact ⟨x, hx⟩
    by_contra hle
    push_neg at hle
    exact hstage.ne_empty (hs₀ u hle.le)
  have hmem : s ∈ AncSet hLaw t C := ⟨le_of_lt hs, C', hC'⟩
  have h2 : s ≤ birthSup hLaw t C :=
    (rfl : birthSup hLaw t C = sSup (AncSet hLaw t C)).symm ▸ (le_csSup hBdd hmem)
  linarith

theorem t3_birthSup_in_critSet {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    (t : ℝ) (C : comps stage J t) :
    birthSup hLaw t C = t ∨ birthSup hLaw t C ∈ (critSet hTame : Set ℝ) := by
  classical
  obtain ⟨s₀, hs₀⟩ := hTame.2.2
  have hBne : (AncSet hLaw t C).Nonempty := ⟨t, le_refl t, C, t3_structMap_id hLaw t C⟩
  have hBdd : BddAbove (AncSet hLaw t C) := by
    refine ⟨s₀, fun u hu => ?_⟩
    obtain ⟨-, C', -⟩ := hu
    have hstage : (stage u).Nonempty := by
      obtain ⟨x, hx, -⟩ := C'.property
      exact ⟨x, hx⟩
    by_contra hle
    push_neg at hle
    exact hstage.ne_empty (hs₀ u hle.le)
  by_cases hstrict : ∃ u, u ∈ AncSet hLaw t C ∧ t < u
  · right
    by_contra hβcrit
    obtain ⟨u, δ, hδpos, hu, hav⟩ :=
      t3_windowEx hLaw hTame hBne hBdd rfl hβcrit hstrict
    have hule : u ≤ birthSup hLaw t C + δ := by
      have h := le_csSup hBdd hu
      calc u ≤ sSup (AncSet hLaw t C) := h
        _ = birthSup hLaw t C := rfl
        _ ≤ birthSup hLaw t C + δ := by linarith [hδpos]
    have hmem : birthSup hLaw t C + δ ∈ AncSet hLaw t C :=
      t3_ancSup_mem hLaw hTame hu hδpos hav hule
    have h2 : birthSup hLaw t C + δ ≤ sSup (AncSet hLaw t C) := le_csSup hBdd hmem
    have hβeq : sSup (AncSet hLaw t C) = birthSup hLaw t C := rfl
    linarith
  · left
    have hall : ∀ u ∈ AncSet hLaw t C, u ≤ t := by
      intro u hu
      by_contra hgt
      exact hstrict ⟨u, hu, not_le.mp hgt⟩
    exact le_antisymm (csSup_le hBne hall) (le_csSup hBdd ⟨le_refl t, C, t3_structMap_id hLaw t C⟩)

theorem t3_bSup_in_crit {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {v : ℝ} (C : comps stage J v) : birthSup hLaw v C ∈ (critSet hTame : Set ℝ) := by
  rcases t3_birthSup_in_critSet hLaw hTame v C with h | h
  · rw [h]; exact t3_bSup_self_crit hLaw hTame h
  · exact h

theorem t3_win_beta {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {v : ℝ} (C : comps stage J v) (b η : ℝ) (hη0 : 0 < η)
    (hgap : ∀ τ ∈ critSet hTame, τ ≠ b → η < |τ - b|) :
    C ∈ ({C : comps stage J v | b - η < birthSup hLaw v C ∧ birthSup hLaw v C < b + η} :
      Set (comps stage J v)) ↔ birthSup hLaw v C = b := by
  constructor
  · intro h
    have hcrit : birthSup hLaw v C ∈ (critSet hTame : Set ℝ) := t3_bSup_in_crit hLaw hTame C
    by_contra hne
    have hg := hgap (birthSup hLaw v C) hcrit hne
    rcases lt_abs.mp hg with hg | hg <;> linarith [h.1, h.2]
  · intro h
    simp only [Set.mem_ofPred_eq]
    rw [h]
    exact ⟨by linarith [hη0], by linarith [hη0]⟩

theorem solution {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {b η δ₀ v : ℝ}
    (hη : η ∈ Set.Ioo (0 : ℝ) δ₀) (hδ₀b : ∀ τ ∈ critSet hTame, τ ≠ b → δ₀ < |τ - b|) :
    ({C : comps stage J v | b - η < birthSup hLaw v C ∧ birthSup hLaw v C < b + η} :
      Set (comps stage J v))
      = {C : comps stage J v | birthSup hLaw v C = b} := by
  ext C
  exact t3_win_beta hLaw hTame C b η hη.1
    (fun τ hτ hτne => by have := hδ₀b τ hτ hτne; linarith [hη.2])
