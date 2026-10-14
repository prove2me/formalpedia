-- Prove2me | solution 1 for PersistClust.Count.death_pin_mult_zero
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-14T05:28:41.198318+00:00
-- url     : https://prove2.me/submissions/8faa5e74-e5c7-4801-999c-68bfac7684bf

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


theorem t3_rank_meets {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) {s t : ℝ} (hst : t ≤ s) :
    rankFn stage J s t =
      {C : comps stage J t | C.val ∈ ((fun x => {y | J t x y}) '' stage s)}.encard := by
  have hval : ((fun x => {y | J t x y}) '' stage s) =
      Subtype.val '' {C : comps stage J t |
        C.val ∈ ((fun x => {y | J t x y}) '' stage s)} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hmem : {y | J t x y} ∈ ((fun x => {y | J t x y}) '' stage t) :=
        ⟨x, hLaw.antitone hst hx, rfl⟩
      exact ⟨⟨{y | J t x y}, hmem⟩, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨C, hCS, hzC⟩
      subst hzC
      exact hCS
  unfold rankFn
  calc ((fun x => {y | J t x y}) '' stage s).encard
      = (Subtype.val '' {C : comps stage J t |
          C.val ∈ ((fun x => {y | J t x y}) '' stage s)}).encard := congrArg Set.encard hval
    _ = {C : comps stage J t |
          C.val ∈ ((fun x => {y | J t x y}) '' stage s)}.encard :=
        Subtype.val_injective.encard_image _


theorem t3_structMap_id {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (t : ℝ) (C : comps stage J t) :
    structMap hLaw le_rfl C = C :=
  Subtype.ext (compRep_spec stage J t C).2


theorem t3_desc_point {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) {t u : ℝ} (hst : t ≤ u)
    {C : comps stage J t} {C' : comps stage J u} (hC' : structMap hLaw hst C' = C)
    {z : ι} (hz : z ∈ C'.val) :
    ((fun x => {y | J t x y}) z) = C.val ∧ z ∈ stage t := by
  have hspec := compRep_spec stage J u C'
  have hzr : J u (compRep stage J u C') z :=
    (Set.ext_iff.mp hspec.2 z).mpr hz
  have hzrt : J t (compRep stage J u C') z := hLaw.compat hst hzr
  have hfmr : ((fun x => {y | J t x y}) (compRep stage J u C')) = C.val := by
    have hv : (structMap hLaw hst C').val = C.val := congrArg Subtype.val hC'
    rw [structMap_val] at hv
    exact hv
  have hclasses : ((fun x => {y | J t x y}) z) =
      ((fun x => {y | J t x y}) (compRep stage J u C')) := by
    ext y
    constructor
    · intro hy
      exact hLaw.trans hzrt hy
    · intro hy
      exact hLaw.trans (hLaw.symm hzrt) hy
  exact ⟨hclasses.trans hfmr, (hLaw.mem hzrt).2⟩


theorem t3_meets_birthSup {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {s t : ℝ} (hst : t ≤ s)
    (hs : ∀ C : comps stage J t, s ≠ birthSup hLaw t C) (C : comps stage J t) :
    C.val ∈ ((fun x => {y | J t x y}) '' stage s) ↔ s < birthSup hLaw t C := by
  classical
  obtain ⟨-, -, hvol⟩ := hTame
  obtain ⟨s₀, hs₀⟩ := hvol
  set B : Set ℝ := {u : ℝ | ∃ (hu : t ≤ u) (C' : comps stage J u), structMap hLaw hu C' = C}
  have hBne : B.Nonempty := ⟨t, le_refl t, C, t3_structMap_id hLaw t C⟩
  have hBbdd : BddAbove B := by
    refine ⟨s₀, fun u hu => ?_⟩
    obtain ⟨-, C', -⟩ := hu
    have hstage : (stage u).Nonempty := by
      obtain ⟨x, hx, -⟩ := C'.property
      exact ⟨x, hx⟩
    by_contra hle
    push_neg at hle
    exact hstage.ne_empty (hs₀ u hle.le)
  constructor
  · -- (→): a meeting cell has an ancestor level in B at s, then sSup = s meets `hs`
    intro hmem
    obtain ⟨x, hx, hxcls⟩ := hmem
    have hprop : {y | J s x y} ∈ (fun x => {y | J s x y}) '' stage s := ⟨x, hx, rfl⟩
    have hCs : structMap hLaw hst ⟨{y | J s x y}, hprop⟩ = C := by
      have hspec := compRep_spec stage J s ⟨{y | J s x y}, hprop⟩
      have hJsx : J s (compRep stage J s ⟨{y | J s x y}, hprop⟩) x :=
        (Set.ext_iff.mp hspec.2 x).mpr (hLaw.refl hx)
      have hJtx : J t (compRep stage J s ⟨{y | J s x y}, hprop⟩) x := hLaw.compat hst hJsx
      refine Subtype.ext ?_
      rw [structMap_val]
      rw [← hxcls]
      ext y
      exact ⟨fun hy => hLaw.trans (hLaw.symm hJtx) hy, fun hy => hLaw.trans hJtx hy⟩
    have hmemB : s ∈ B := ⟨hst, ⟨{y | J s x y}, hprop⟩, hCs⟩
    have hle : s ≤ birthSup hLaw t C := le_csSup hBbdd hmemB
    by_contra hcon
    push_neg at hcon
    exact (hs C) (le_antisymm hcon hle).symm
  · -- (←): an ancestor level above s has points in stage s whose t-class is C
    intro hlt
    obtain ⟨u, huB, hsu⟩ := (lt_csSup_iff hBbdd hBne).mp hlt
    obtain ⟨hu, C', hC'⟩ := huB
    have hspec := compRep_spec stage J u C'
    have hz : compRep stage J u C' ∈ C'.val := by
      have h1 : compRep stage J u C' ∈
          ((fun x => {y | J u x y}) (compRep stage J u C')) := hLaw.refl hspec.1
      rwa [hspec.2] at h1
    have hzcls := (t3_desc_point hLaw hu hC' hz).1
    have hzstages : compRep stage J u C' ∈ stage s :=
      hLaw.antitone (le_of_lt hsu) hspec.1
    exact ⟨compRep stage J u C', hzstages, hzcls⟩


theorem t3_rank_orig {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {s t : ℝ} (hst : t ≤ s)
    (hs : ∀ C : comps stage J t, s ≠ birthSup hLaw t C) :
    rankFn stage J s t = {C : comps stage J t | s < birthSup hLaw t C}.encard := by
  rw [t3_rank_meets hLaw hst]
  congr 1
  ext C
  exact t3_meets_birthSup hLaw hTame hst hs C


theorem t2_qtame {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) (s t : ℝ) :
    rankFn stage J s t ≠ ⊤ := by
  obtain ⟨hcomp, -, -⟩ := hTame
  have hsub : ((fun x => {y | J t x y}) '' stage s) ⊆
      insert (∅ : Set ι) ((fun x => {y | J t x y}) '' stage t) := by
    rintro S ⟨x, hx, rfl⟩
    by_cases hxt : x ∈ stage t
    · exact Or.inr ⟨x, hxt, rfl⟩
    · exact Or.inl (Set.eq_empty_iff_forall_notMem.mpr
        (fun y hy => absurd (hLaw.mem hy).1 hxt))
  have hfin : ((fun x => {y | J t x y}) '' stage s).Finite :=
    Set.Finite.subset (Set.Finite.insert ∅ (hcomp t)) hsub
  unfold rankFn
  exact ne_of_lt (Set.Finite.encard_lt_top hfin)


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


theorem t3_crit_inj {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {w w' : ℝ} (hww : w ≤ w')
    (hfree : ∀ τ ∈ critSet hTame, τ < w ∨ w' < τ) {C₁ C₂ : comps stage J w'}
    (h : structMap hLaw hww C₁ = structMap hLaw hww C₂) : C₁ = C₂ := by
  have hspec1 := compRep_spec stage J w' C₁
  have hspec2 := compRep_spec stage J w' C₂
  have hv : (structMap hLaw hww C₁).val = (structMap hLaw hww C₂).val :=
    congrArg Subtype.val h
  rw [structMap_val, structMap_val] at hv
  have hJw : J w (compRep stage J w' C₁) (compRep stage J w' C₂) := by
    have hmem : compRep stage J w' C₂ ∈ {z | J w (compRep stage J w' C₁) z} := by
      rw [hv]
      exact hLaw.refl (hLaw.antitone hww hspec2.1)
    exact hmem
  have hclause := (critSet_spec hTame w w' hww hfree).2
  have hJw' : J w' (compRep stage J w' C₁) (compRep stage J w' C₂) :=
    hclause (compRep stage J w' C₁) hspec1.1 (compRep stage J w' C₂) hspec2.1 hJw
  refine Subtype.ext ?_
  rw [← hspec1.2, ← hspec2.2]
  ext z
  exact ⟨fun hz => hLaw.trans (hLaw.symm hJw') hz, fun hz => hLaw.trans hJw' hz⟩


theorem t3_bSupThread {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {w w' : ℝ} (hww : w ≤ w')
    (hfree : ∀ τ ∈ critSet hTame, τ < w ∨ w' < τ)
    {C'' : comps stage J w'} {C : comps stage J w}
    (h : structMap hLaw hww C'' = C) :
    birthSup hLaw w C = birthSup hLaw w' C'' := by
  classical
  obtain ⟨s₀, hs₀⟩ := hTame.2.2
  have hneC : (AncSet hLaw w C).Nonempty := ⟨w, le_rfl, C, t3_structMap_id hLaw w C⟩
  have hneC' : (AncSet hLaw w' C'').Nonempty := ⟨w', le_rfl, C'', t3_structMap_id hLaw w' C''⟩
  have hBddC : BddAbove (AncSet hLaw w C) := by
    refine ⟨s₀, fun u hu => ?_⟩
    obtain ⟨-, C₂, -⟩ := hu
    have hstage : (stage u).Nonempty := by
      obtain ⟨x, hx, -⟩ := C₂.property
      exact ⟨x, hx⟩
    by_contra hle
    push_neg at hle
    exact hstage.ne_empty (hs₀ u hle.le)
  have hBddC' : BddAbove (AncSet hLaw w' C'') := by
    refine ⟨s₀, fun u hu => ?_⟩
    obtain ⟨-, C₂, -⟩ := hu
    have hstage : (stage u).Nonempty := by
      obtain ⟨x, hx, -⟩ := C₂.property
      exact ⟨x, hx⟩
    by_contra hle
    push_neg at hle
    exact hstage.ne_empty (hs₀ u hle.le)
  refine le_antisymm (csSup_le hneC (fun u hu => ?_)) (csSup_le hneC' (fun v hv => ?_))
  · -- u ∈ AncSet(w,C) ⊢ u ≤ birthSup(w',C'')
    obtain ⟨huw, C₂, hC₂⟩ := hu
    by_cases huw' : u ≤ w'
    · have h2 : w' ≤ birthSup hLaw w' C'' :=
        (rfl : birthSup hLaw w' C'' = sSup (AncSet hLaw w' C'')).symm ▸
          (le_csSup hBddC' ⟨le_rfl, C'', t3_structMap_id hLaw w' C''⟩)
      linarith
    · push_neg at huw'
      have hC'₃ : structMap hLaw hww (structMap hLaw (le_of_lt huw') C₂) = C := by
        rw [structMap_comp hLaw hww (le_of_lt huw') C₂]
        exact hC₂
      have hpre : structMap hLaw hww (structMap hLaw (le_of_lt huw') C₂) =
          structMap hLaw hww C'' := hC'₃.trans h.symm
      have hC₃eq : structMap hLaw (le_of_lt huw') C₂ = C'' :=
        t3_crit_inj hLaw hTame hww hfree hpre
      have hmem : u ∈ AncSet hLaw w' C'' := ⟨le_of_lt huw', C₂, hC₃eq⟩
      exact (rfl : birthSup hLaw w' C'' = sSup (AncSet hLaw w' C'')).symm ▸ (le_csSup hBddC' hmem)
  · -- v ∈ AncSet(w',C'') ⊢ v ≤ birthSup(w,C)
    obtain ⟨hw'v, C_v, hC_v⟩ := hv
    have hvC : v ∈ AncSet hLaw w C := by
      refine ⟨le_trans hww hw'v, C_v, ?_⟩
      rw [← structMap_comp hLaw hww hw'v C_v, hC_v]
      exact h
    exact (rfl : birthSup hLaw w C = sSup (AncSet hLaw w C)).symm ▸ (le_csSup hBddC hvC)


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


theorem t3_windowSplit {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {b η w : ℝ} (hη0 : 0 < η) (horder : w ≤ b - η)
    (hgenw : ∀ C : comps stage J w, b - η ≠ birthSup hLaw w C ∧ b + η ≠ birthSup hLaw w C) :
    rankFn stage J (b - η) w = rankFn stage J (b + η) w +
      ({C : comps stage J w | b - η < birthSup hLaw w C ∧ birthSup hLaw w C < b + η} :
        Set (comps stage J w)).encard := by
  rw [t3_rank_orig hLaw hTame horder (fun C => (hgenw C).1),
      t3_rank_orig hLaw hTame (le_trans horder (by linarith)) (fun C => (hgenw C).2)]
  rw [← Set.encard_union_eq]
  · congr 1
    ext C
    simp only [Set.mem_setOf_eq, Set.mem_union]
    constructor
    · intro h
      rcases lt_or_ge (birthSup hLaw w C) (b + η) with hlt | hge
      · exact Or.inr ⟨h, hlt⟩
      · exact Or.inl (by have hne := (hgenw C).2; exact lt_of_le_of_ne hge hne)
    · rintro (h | ⟨h1, h2⟩)
      · linarith
      · exact h1
  · -- disjointness
    rw [Set.disjoint_left]
    intro C h1 h2
    simp only [Set.mem_setOf_eq] at h1 h2
    linarith [h1, h2.1, h2.2]


theorem t3_add_sub {a b : ℕ∞} (hfin : a ≠ ⊤) : (a + b) - a = b := by
  cases a with
  | top => exact absurd rfl hfin
  | coe m =>
      cases b with
      | top => simp
      | coe n => exact_mod_cast Nat.add_sub_cancel_left m n


theorem t3_box_arith {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {b d η : ℝ} (hbd : d < b) (hη0 : 0 < η) (hη : η < (b - d) / 2)
    (hgen : ∀ (t : ℝ) (C : comps stage J t), b - η ≠ birthSup hLaw t C ∧
        b + η ≠ birthSup hLaw t C ∧ d + η ≠ birthSup hLaw t C ∧ d - η ≠ birthSup hLaw t C) :
    (rankFn stage J (b - η) (d + η) - rankFn stage J (b + η) (d + η)) -
        (rankFn stage J (b - η) (d - η) - rankFn stage J (b + η) (d - η)) =
      (({C : comps stage J (d + η) | (b - η < birthSup hLaw (d + η) C) ∧
            (birthSup hLaw (d + η) C < b + η)} : Set (comps stage J (d + η))).encard
        - ({C : comps stage J (d - η) | (b - η < birthSup hLaw (d - η) C) ∧
            (birthSup hLaw (d - η) C < b + η)} : Set (comps stage J (d - η))).encard : ℕ∞) := by
  have hord1 : d + η ≤ b - η := by linarith [hbd, hη0, hη]
  have hord2 : d - η ≤ b - η := by linarith [hbd, hη0, hη]
  rw [t3_windowSplit hLaw hTame hη0 hord1 (fun C => ⟨(hgen (d + η) C).1, (hgen (d + η) C).2.1⟩),
      t3_windowSplit hLaw hTame hη0 hord2 (fun C => ⟨(hgen (d - η) C).1, (hgen (d - η) C).2.1⟩)]
  congr 1
  · exact t3_add_sub (t2_qtame hLaw hTame (b + η) (d + η))
  · exact t3_add_sub (t2_qtame hLaw hTame (b + η) (d - η))


theorem t3_box_identity {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {b d η : ℝ} (hbd : d < b) (hη0 : 0 < η) (hη : η < (b - d) / 2)
    (hgen : ∀ (t : ℝ) (C : comps stage J t), b - η ≠ birthSup hLaw t C ∧
        b + η ≠ birthSup hLaw t C ∧ d + η ≠ birthSup hLaw t C ∧ d - η ≠ birthSup hLaw t C) :
    (rankFn stage J (b - η) (d + η) - rankFn stage J (b + η) (d + η)) -
        (rankFn stage J (b - η) (d - η) - rankFn stage J (b + η) (d - η)) =
      (({C : comps stage J (d + η) | (b - η < birthSup hLaw (d + η) C) ∧
            (birthSup hLaw (d + η) C < b + η)} : Set (comps stage J (d + η))).encard
        - ({C : comps stage J (d - η) | (b - η < birthSup hLaw (d - η) C) ∧
            (birthSup hLaw (d - η) C < b + η)} : Set (comps stage J (d - η))).encard : ℕ∞) :=
  t3_box_arith hLaw hTame hbd hη0 hη hgen


theorem t3_mult_unfold {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) {b d : ℝ} (hbd : d < b) :
    mult (rankFn stage J) ((b : EReal), (d : EReal)) =
      ⨅ (η : ℝ) (_ : η ∈ Set.Ioo (0 : ℝ) ((b - d) / 2)), t3_comb stage J b d η := by
  unfold mult t3_comb
  rw [if_pos ⟨EReal.coe_ne_bot b, EReal.coe_ne_top b⟩,
      if_neg (EReal.coe_ne_bot d), if_pos (EReal.coe_lt_coe_iff.mpr hbd)]
  simp only [EReal.toReal_coe]


theorem t3_gapEx {ε₀ : ℝ} (F : Finset ℝ) (hε : 0 < ε₀) (p : ℝ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ ε₀ ∧ ∀ τ ∈ F, τ ≠ p → δ₀ < |τ - p| := by
  classical
  set G : Finset ℝ := (F.filter (fun τ => τ ≠ p)).image (fun τ => |τ - p|) with hGdef
  by_cases hG : G.Nonempty
  · have hμmem : G.min' hG ∈ G := Finset.min'_mem _ hG
    obtain ⟨τ₀, hτ₀, hμeq⟩ := Finset.mem_image.mp hμmem
    have hτ₀ne : τ₀ ≠ p := (Finset.mem_filter.mp hτ₀).2
    have hμpos : 0 < G.min' hG := by
      rw [← hμeq]
      exact abs_pos.mpr (sub_ne_zero.mpr hτ₀ne)
    refine ⟨min ε₀ (G.min' hG) / 2, by positivity, by
      have h1 : min ε₀ (G.min' hG) ≤ ε₀ := min_le_left _ _
      linarith, fun τ hτ hτne => ?_⟩
    have hτmem : |τ - p| ∈ G :=
      Finset.mem_image.mpr ⟨τ, Finset.mem_filter.mpr ⟨hτ, hτne⟩, rfl⟩
    have hmin_le : G.min' hG ≤ |τ - p| := Finset.min'_le _ _ hτmem
    have h2 : min ε₀ (G.min' hG) ≤ G.min' hG := min_le_right _ _
    linarith [hμpos]
  · refine ⟨ε₀, hε, le_rfl, fun τ hτ hτne => ?_⟩
    exfalso
    exact hG ⟨|τ - p|, Finset.mem_image.mpr ⟨τ, Finset.mem_filter.mpr ⟨hτ, hτne⟩, rfl⟩⟩


theorem t3_stable_delta {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {b d : ℝ} (hbd : d < b) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ (b - d) / 2 ∧
      (∀ τ ∈ critSet hTame, τ ≠ b → δ₀ < |τ - b|) ∧
      (∀ τ ∈ critSet hTame, τ ≠ d → δ₀ < |τ - d|) := by
  obtain ⟨δb, hδb0, hδble, hδb⟩ := t3_gapEx (critSet hTame)
    (show 0 < (b - d) / 4 by linarith) b
  obtain ⟨δd, hδd0, hδdle, hδd⟩ := t3_gapEx (critSet hTame)
    (show 0 < (b - d) / 4 by linarith) d
  refine ⟨min δb δd, lt_min hδb0 hδd0, ?_, ?_, ?_⟩
  · have h1 : min δb δd ≤ δb := min_le_left _ _
    have h2 : min δb δd ≤ δd := min_le_right _ _
    linarith
  · intro τ hτ hτne
    have h1 : min δb δd ≤ δb := min_le_left _ _
    linarith [hδb τ hτ hτne]
  · intro τ hτ hτne
    have h1 : min δb δd ≤ δd := min_le_right _ _
    linarith [hδd τ hτ hτne]


theorem t3_desc_surj {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {w w' : ℝ} (hww : w ≤ w')
    (hfree : ∀ τ ∈ critSet hTame, τ < w ∨ w' < τ) (C : comps stage J w) :
    ∃ C' : comps stage J w', structMap hLaw hww C' = C := by
  have hx := (compRep_spec stage J w C).1
  have hdir := (critSet_spec hTame w w' hww hfree).1
  obtain ⟨y, hy, hJy⟩ := hdir (compRep stage J w C) hx
  have hprop : {z | J w' y z} ∈ (fun x => {z | J w' x z}) '' stage w' := ⟨y, hy, rfl⟩
  refine ⟨⟨{z | J w' y z}, hprop⟩, ?_⟩
  have hspecy := compRep_spec stage J w' ⟨{z | J w' y z}, hprop⟩
  have hJw'rep : J w' (compRep stage J w' ⟨{z | J w' y z}, hprop⟩) y := by
    have hmem : y ∈ ((fun x => {z | J w' x z})
        (compRep stage J w' ⟨{z | J w' y z}, hprop⟩)) := by
      rw [hspecy.2]
      exact hLaw.refl hy
    exact hmem
  have hJwrep : J w (compRep stage J w' ⟨{z | J w' y z}, hprop⟩) (compRep stage J w C) :=
    hLaw.trans (hLaw.compat hww hJw'rep) (hLaw.symm hJy)
  refine Subtype.ext ?_
  rw [structMap_val]
  rw [show C.val = ((fun x => {z | J w x z}) (compRep stage J w C)) from
    (compRep_spec stage J w C).2.symm]
  ext z
  exact ⟨fun hz => hLaw.trans (hLaw.symm hJwrep) hz, fun hz => hLaw.trans hJwrep hz⟩


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


theorem t3_selfTrans {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {v₁ v₂ : ℝ} (hvv : v₁ ≤ v₂)
    (hfree : ∀ τ ∈ critSet hTame, τ < v₁ ∨ v₂ < τ)
    {b : ℝ} (hfb₁ : v₁ ≠ b) (hfb₂ : v₂ ≠ b) :
    {C : comps stage J v₁ | birthSup hLaw v₁ C = b}.encard
      = {C : comps stage J v₂ | birthSup hLaw v₂ C = b}.encard := by
  classical
  have hle₁ : {C : comps stage J v₂ | birthSup hLaw v₂ C = b}.encard
      ≤ {C : comps stage J v₁ | birthSup hLaw v₁ C = b}.encard := by
    refine Set.encard_le_encard_of_injOn (f := fun C => structMap hLaw hvv C)
      (fun C hC => ?_) (fun C₁ hC₁ C₂ hC₂ heq => ?_)
    · exact (t3_bSupThread hLaw hTame hvv hfree (C'' := C) rfl).trans hC
    · exact t3_crit_inj hLaw hTame hvv hfree heq
  have hle₂ : {C : comps stage J v₁ | birthSup hLaw v₁ C = b}.encard
      ≤ {C : comps stage J v₂ | birthSup hLaw v₂ C = b}.encard := by
    let f : comps stage J v₁ → comps stage J v₂ :=
      fun C => Classical.choose (t3_desc_surj hLaw hTame hvv hfree C)
    have hspec : ∀ C, structMap hLaw hvv (f C) = C :=
      fun C => Classical.choose_spec (t3_desc_surj hLaw hTame hvv hfree C)
    refine Set.encard_le_encard_of_injOn (f := f) (fun C hC => ?_)
      (fun C₁ hC₁ C₂ hC₂ heq => ?_)
    · have h := t3_bSupThread hLaw hTame hvv hfree (hspec C)
      exact h.symm.trans hC
    · have h₁ := hspec C₁
      rw [heq, hspec C₂] at h₁
      exact h₁.symm
  exact le_antisymm hle₂ hle₁


theorem t3_win_eq_plus {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {b d δ₀ : ℝ} (hbd : d < b)
    (hgap : (∀ τ ∈ critSet hTame, τ ≠ b → δ₀ < |τ - b|) ∧
      (∀ τ ∈ critSet hTame, τ ≠ d → δ₀ < |τ - d|))
    {η : ℝ} (hη : η ∈ Set.Ioo (0 : ℝ) δ₀) (hηbd : η < (b - d) / 2)
    {η' : ℝ} (hη' : η' ∈ Set.Ioo (0 : ℝ) δ₀) (hη'bd : η' < (b - d) / 2) :
    ({C : comps stage J (d + η) | b - η < birthSup hLaw (d + η) C ∧
        birthSup hLaw (d + η) C < b + η} : Set (comps stage J (d + η))).encard
      = ({C : comps stage J (d + η') | b - η' < birthSup hLaw (d + η') C ∧
        birthSup hLaw (d + η') C < b + η'} : Set (comps stage J (d + η'))).encard := by
  have hsets : ({C : comps stage J (d + η) | b - η < birthSup hLaw (d + η) C ∧
      birthSup hLaw (d + η) C < b + η} : Set (comps stage J (d + η)))
      = {C : comps stage J (d + η) | birthSup hLaw (d + η) C = b} := by
    ext C
    exact t3_win_beta hLaw hTame C b η hη.1
      (fun τ hτ hτne => by have := hgap.1 τ hτ hτne; linarith [hη.2])
  have hsets' : ({C : comps stage J (d + η') | b - η' < birthSup hLaw (d + η') C ∧
      birthSup hLaw (d + η') C < b + η'} : Set (comps stage J (d + η')))
      = {C : comps stage J (d + η') | birthSup hLaw (d + η') C = b} := by
    ext C
    exact t3_win_beta hLaw hTame C b η' hη'.1
      (fun τ hτ hτne => by have := hgap.1 τ hτ hτne; linarith [hη'.2])
  rw [hsets, hsets']
  by_cases hle : η ≤ η'
  · have hfb1 : d + η ≠ b := by intro hne; linarith [hηbd, hbd, hne]
    have hfb2 : d + η' ≠ b := by intro hne; linarith [hη'bd, hbd, hne]
    have hfree : ∀ τ ∈ critSet hTame, τ < d + η ∨ d + η' < τ := by
      intro τ hτ
      rcases lt_trichotomy τ d with hlt | heq | hgt
      · exact Or.inl (by linarith [hη.1])
      · exact Or.inl (by linarith [hη.1])
      · have hτd : τ ≠ d := by linarith
        have hδ := hgap.2 τ hτ hτd
        simp only [abs_of_pos (by linarith : 0 < τ - d)] at hδ
        exact Or.inr (by linarith [hη'.2])
    exact t3_selfTrans hLaw hTame (by linarith) hfree hfb1 hfb2
  · push_neg at hle
    have hfb1 : d + η' ≠ b := by intro hne; linarith [hη'bd, hbd, hne]
    have hfb2 : d + η ≠ b := by intro hne; linarith [hηbd, hbd, hne]
    have hfree : ∀ τ ∈ critSet hTame, τ < d + η' ∨ d + η < τ := by
      intro τ hτ
      rcases lt_trichotomy τ d with hlt | heq | hgt
      · exact Or.inl (by linarith [hη'.1])
      · exact Or.inl (by linarith [hη'.1])
      · have hτd : τ ≠ d := by linarith
        have hδ := hgap.2 τ hτ hτd
        simp only [abs_of_pos (by linarith : 0 < τ - d)] at hδ
        exact Or.inr (by linarith [hη.2])
    exact (t3_selfTrans hLaw hTame (by linarith) hfree hfb1 hfb2).symm


theorem t3_win_eq_minus {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {b d δ₀ : ℝ} (hbd : d < b)
    (hgap : (∀ τ ∈ critSet hTame, τ ≠ b → δ₀ < |τ - b|) ∧
      (∀ τ ∈ critSet hTame, τ ≠ d → δ₀ < |τ - d|))
    {η : ℝ} (hη : η ∈ Set.Ioo (0 : ℝ) δ₀) (hηbd : η < (b - d) / 2)
    {η' : ℝ} (hη' : η' ∈ Set.Ioo (0 : ℝ) δ₀) (hη'bd : η' < (b - d) / 2) :
    ({C : comps stage J (d - η) | b - η < birthSup hLaw (d - η) C ∧
        birthSup hLaw (d - η) C < b + η} : Set (comps stage J (d - η))).encard
      = ({C : comps stage J (d - η') | b - η' < birthSup hLaw (d - η') C ∧
        birthSup hLaw (d - η') C < b + η'} : Set (comps stage J (d - η'))).encard := by
  have hsets : ({C : comps stage J (d - η) | b - η < birthSup hLaw (d - η) C ∧
      birthSup hLaw (d - η) C < b + η} : Set (comps stage J (d - η)))
      = {C : comps stage J (d - η) | birthSup hLaw (d - η) C = b} := by
    ext C
    exact t3_win_beta hLaw hTame C b η hη.1
      (fun τ hτ hτne => by have := hgap.1 τ hτ hτne; linarith [hη.2])
  have hsets' : ({C : comps stage J (d - η') | b - η' < birthSup hLaw (d - η') C ∧
      birthSup hLaw (d - η') C < b + η'} : Set (comps stage J (d - η')))
      = {C : comps stage J (d - η') | birthSup hLaw (d - η') C = b} := by
    ext C
    exact t3_win_beta hLaw hTame C b η' hη'.1
      (fun τ hτ hτne => by have := hgap.1 τ hτ hτne; linarith [hη'.2])
  rw [hsets, hsets']
  by_cases hle : η ≤ η'
  · have hfb1 : d - η' ≠ b := by intro hne; linarith [hne, hbd, hη'.1]
    have hfb2 : d - η ≠ b := by intro hne; linarith [hne, hbd, hη.1]
    have hfree : ∀ τ ∈ critSet hTame, τ < d - η' ∨ d - η < τ := by
      intro τ hτ
      rcases lt_trichotomy τ d with hlt | heq | hgt
      · have hτd : τ ≠ d := by linarith
        have hδ := hgap.2 τ hτ hτd
        simp only [abs_of_neg (by linarith : τ - d < 0)] at hδ
        exact Or.inl (by linarith [hη'.2])
      · exact Or.inr (by linarith [hη.1])
      · have hτd : τ ≠ d := by linarith
        have hδ := hgap.2 τ hτ hτd
        simp only [abs_of_pos (by linarith : 0 < τ - d)] at hδ
        exact Or.inr (by linarith [hη.1])
    exact (t3_selfTrans hLaw hTame (by linarith) hfree hfb1 hfb2).symm
  · push_neg at hle
    have hfb1 : d - η ≠ b := by intro hne; linarith [hne, hbd, hη.1]
    have hfb2 : d - η' ≠ b := by intro hne; linarith [hne, hbd, hη'.1]
    have hfree : ∀ τ ∈ critSet hTame, τ < d - η ∨ d - η' < τ := by
      intro τ hτ
      rcases lt_trichotomy τ d with hlt | heq | hgt
      · have hτd : τ ≠ d := by linarith
        have hδ := hgap.2 τ hτ hτd
        simp only [abs_of_neg (by linarith : τ - d < 0)] at hδ
        exact Or.inl (by linarith [hη.2])
      · exact Or.inr (by linarith [hη'.1])
      · have hτd : τ ≠ d := by linarith
        have hδ := hgap.2 τ hτ hτd
        simp only [abs_of_pos (by linarith : 0 < τ - d)] at hδ
        exact Or.inr (by linarith [hη'.1])
    exact t3_selfTrans hLaw hTame (by linarith) hfree hfb1 hfb2


theorem t3_comb_stable {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {b d : ℝ} (hbd : d < b) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ (b - d) / 2 ∧
      ∀ η ∈ Set.Ioo (0 : ℝ) δ₀, ∀ η' ∈ Set.Ioo (0 : ℝ) δ₀,
        t3_comb stage J b d η = t3_comb stage J b d η' := by
  obtain ⟨δ₀, hδ0, hδle, hgap⟩ := t3_stable_delta hLaw hTame hbd
  refine ⟨δ₀, hδ0, hδle, fun η hη η' hη' => ?_⟩
  have hgenOf : ∀ ζ (hζ : ζ ∈ Set.Ioo (0 : ℝ) δ₀), ∀ (t : ℝ) (C : comps stage J t),
      b - ζ ≠ birthSup hLaw t C ∧ b + ζ ≠ birthSup hLaw t C ∧
      d + ζ ≠ birthSup hLaw t C ∧ d - ζ ≠ birthSup hLaw t C := by
    intro ζ hζ t C
    have hcrit := t3_bSup_in_crit hLaw hTame C
    have hζδ : ζ < δ₀ := hζ.2
    have hζ0 : 0 < ζ := hζ.1
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro heq
      by_cases hb : birthSup hLaw t C = b
      · linarith [heq ▸ hb, hζ0]
      · have hg := hgap.1 _ hcrit hb
        rw [show birthSup hLaw t C = b - ζ from heq.symm] at hg
        rw [show b - ζ - b = -ζ by ring, abs_neg, abs_of_pos hζ0] at hg
        linarith
    · intro heq
      by_cases hb : birthSup hLaw t C = b
      · linarith [heq ▸ hb, hζ0]
      · have hg := hgap.1 _ hcrit hb
        rw [show birthSup hLaw t C = b + ζ from heq.symm] at hg
        rw [show b + ζ - b = ζ by ring, abs_of_pos hζ0] at hg
        linarith
    · intro heq
      by_cases hd : birthSup hLaw t C = d
      · linarith [heq ▸ hd, hζ0]
      · have hg := hgap.2 _ hcrit hd
        rw [show birthSup hLaw t C = d + ζ from heq.symm] at hg
        rw [show d + ζ - d = ζ by ring, abs_of_pos hζ0] at hg
        linarith
    · intro heq
      by_cases hd : birthSup hLaw t C = d
      · linarith [heq ▸ hd, hζ0]
      · have hg := hgap.2 _ hcrit hd
        rw [show birthSup hLaw t C = d - ζ from heq.symm] at hg
        rw [show d - ζ - d = -ζ by ring, abs_neg, abs_of_pos hζ0] at hg
        linarith
  rw [show (t3_comb stage J b d η) = ((rankFn stage J (b - η) (d + η) -
      rankFn stage J (b + η) (d + η)) -
        (rankFn stage J (b - η) (d - η) - rankFn stage J (b + η) (d - η))) from rfl,
      show (t3_comb stage J b d η') = ((rankFn stage J (b - η') (d + η') -
      rankFn stage J (b + η') (d + η')) -
        (rankFn stage J (b - η') (d - η') - rankFn stage J (b + η') (d - η'))) from rfl]
  rw [t3_box_identity hLaw hTame hbd hη.1 (by linarith [hη.2, hδle]) (hgenOf η hη),
      t3_box_identity hLaw hTame hbd hη'.1 (by linarith [hη'.2, hδle]) (hgenOf η' hη')]
  rw [t3_win_eq_plus hLaw hTame hbd hgap hη (by linarith [hη.2, hδle]) hη' (by linarith [hη'.2, hδle]),
      t3_win_eq_minus hLaw hTame hbd hgap hη (by linarith [hη.2, hδle]) hη' (by linarith [hη'.2, hδle])]


theorem t3_comb_ge {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {b d : ℝ} (hbd : d < b)
    {η η' : ℝ} (hη0 : 0 < η) (hle : η ≤ η') (hη'lim : η' < (b - d) / 2) :
    t3_comb stage J b d η ≤ t3_comb stage J b d η' := by
  -- (a) Master thread-lift: a cell at probe `w` counted by the window `(lo, hi]` lifts via
  -- its `lo`-ancestor (the meets→ancestor half of t3_meets_birthSup) to an injective
  -- assignment at the higher probe `w'`, still counted by the same window; the meeting of
  -- every level pulls back along the lift (image point-set ⊆ source point-set by compat),
  -- and injectivity is composing the descent back down to `w` (structMap_comp).
  -- Unconditional — no crit-free window needed.
  have hinj : ∀ (w w' lo hi : ℝ) (hww' : w ≤ w') (hw'lo : w' ≤ lo),
      ∃ F : {C : comps stage J w //
          C.val ∈ ((fun x => {y | J w x y}) '' stage lo) ∧
          C.val ∉ ((fun x => {y | J w x y}) '' stage hi)} →
        {C : comps stage J w' //
          C.val ∈ ((fun x => {y | J w' x y}) '' stage lo) ∧
          C.val ∉ ((fun x => {y | J w' x y}) '' stage hi)},
      Function.Injective F ∧
      ∀ C s'', (F C).val.val ∈ ((fun x => {y | J w' x y}) '' stage s'') →
        C.val.val ∈ ((fun x => {y | J w x y}) '' stage s'') := by
    classical
    intro w w' lo hi hww' hw'lo
    -- class equality: J-related points span the same class
    have hclasseq : ∀ (t : ℝ) (x y : ι) (h : J t x y), {z | J t x z} = {z | J t y z} := by
      intro t x y h
      ext z
      exact ⟨fun hz => hLaw.trans (hLaw.symm h) hz, fun hz => hLaw.trans h hz⟩
    -- meets→ancestor (the (→) half of t3_meets_birthSup, level-renamed): a cell at `a`
    -- meeting stage `c` (a ≤ c) has a `c`-ancestor whose descent is itself
    have hanc : ∀ (a c : ℝ) (hac : a ≤ c) (C : comps stage J a),
        C.val ∈ ((fun x => {y | J a x y}) '' stage c) →
        ∃ C_c : comps stage J c, structMap hLaw hac C_c = C := by
      intro a c hac C hmem
      obtain ⟨x, hx, hxcls⟩ := hmem
      have hprop : {y | J c x y} ∈ (fun x => {y | J c x y}) '' stage c := ⟨x, hx, rfl⟩
      have hCs : structMap hLaw hac ⟨{y | J c x y}, hprop⟩ = C := by
        have h2 : (fun x => {y | J c x y}) (compRep stage J c ⟨{y | J c x y}, hprop⟩) =
            {y | J c x y} := (compRep_spec stage J c ⟨{y | J c x y}, hprop⟩).2
        have h3 : x ∈ (fun x => {y | J c x y}) (compRep stage J c ⟨{y | J c x y}, hprop⟩) := by
          rw [h2]
          exact hLaw.refl hx
        have hJcx : J c (compRep stage J c ⟨{y | J c x y}, hprop⟩) x := h3
        have hJac : J a (compRep stage J c ⟨{y | J c x y}, hprop⟩) x := hLaw.compat hac hJcx
        refine Subtype.ext ?_
        rw [structMap_val]
        rw [← hxcls]
        ext y
        exact ⟨fun hy => hLaw.trans (hLaw.symm hJac) hy, fun hy => hLaw.trans hJac hy⟩
      exact ⟨⟨{y | J c x y}, hprop⟩, hCs⟩
    -- the chosen lo-ancestor of each counted cell at w, and its descent spec
    let anc : {C : comps stage J w //
        C.val ∈ ((fun x => {y | J w x y}) '' stage lo) ∧
        C.val ∉ ((fun x => {y | J w x y}) '' stage hi)} → comps stage J lo :=
      fun C => Classical.choose (hanc w lo (le_trans hww' hw'lo) (C : comps stage J w) C.2.1)
    have hanc1 : ∀ C : {C : comps stage J w //
        C.val ∈ ((fun x => {y | J w x y}) '' stage lo) ∧
        C.val ∉ ((fun x => {y | J w x y}) '' stage hi)},
        structMap hLaw (le_trans hww' hw'lo) (anc C) = (C : comps stage J w) :=
      fun C => Classical.choose_spec
        (hanc w lo (le_trans hww' hw'lo) (C : comps stage J w) C.2.1)
    -- core: the lifted cell still meets `lo`; and any meeting by the lifted cell at level s''
    -- pulls back to the source cell at w (class equality + compat descent)
    have hcore : ∀ (C : comps stage J w) (C_lo : comps stage J lo)
        (hC : structMap hLaw (le_trans hww' hw'lo) C_lo = C),
        (structMap hLaw hw'lo C_lo).val ∈ ((fun x => {y | J w' x y}) '' stage lo) ∧
        ∀ s'' : ℝ, (structMap hLaw hw'lo C_lo).val ∈
            ((fun x => {y | J w' x y}) '' stage s'') →
          C.val ∈ ((fun x => {y | J w x y}) '' stage s'') := by
      intro C C_lo hC
      have hCval : {y | J w (compRep stage J lo C_lo) y} = C.val := by
        have h := congrArg Subtype.val hC
        rw [structMap_val] at h
        exact h
      have hrep : compRep stage J lo C_lo ∈ stage w' :=
        hLaw.antitone hw'lo (compRep_spec stage J lo C_lo).1
      refine ⟨⟨compRep stage J lo C_lo, (compRep_spec stage J lo C_lo).1, rfl⟩, ?_⟩
      intro s'' hmem
      obtain ⟨x, hx, hxcls⟩ := hmem
      have hxcls' : {y | J w' x y} = (structMap hLaw hw'lo C_lo).val := hxcls
      have h2 : compRep stage J lo C_lo ∈ (structMap hLaw hw'lo C_lo).val := by
        show compRep stage J lo C_lo ∈ {y | J w' (compRep stage J lo C_lo) y}
        exact hLaw.refl hrep
      rw [← hxcls'] at h2
      have hw'x : J w' x (compRep stage J lo C_lo) := h2
      have hwx : J w x (compRep stage J lo C_lo) := hLaw.compat hww' hw'x
      exact ⟨x, hx, (hclasseq w x (compRep stage J lo C_lo) hwx).trans hCval⟩
    refine ⟨fun C => ⟨structMap hLaw hw'lo (anc C), ?_, ?_⟩, ?_, ?_⟩
    · exact (hcore (C : comps stage J w) (anc C) (hanc1 C)).1
    · intro hmem
      exact C.2.2 ((hcore (C : comps stage J w) (anc C) (hanc1 C)).2 hi hmem)
    · intro C₁ C₂ hF
      have hval : structMap hLaw hw'lo (anc C₁) = structMap hLaw hw'lo (anc C₂) :=
        congrArg Subtype.val hF
      have hdesc : structMap hLaw hww' (structMap hLaw hw'lo (anc C₁)) =
          structMap hLaw hww' (structMap hLaw hw'lo (anc C₂)) :=
        congrArg (structMap hLaw hww') hval
      rw [structMap_comp hLaw hww' hw'lo (anc C₁),
          structMap_comp hLaw hww' hw'lo (anc C₂), hanc1 C₁, hanc1 C₂] at hdesc
      exact Subtype.ext hdesc
    · intro C s'' hmem
      exact (hcore (C : comps stage J w) (anc C) (hanc1 C)).2 s'' hmem
  -- (b) Counted-side transports — the four hinj instances (plus-/minus-box, and the two
  -- collar transports): plus-box (d+η → d+η' at window (b−η, b+η)); minus-box (d−η' → d−η
  -- at (b−η', b+η')); collar₁ (d−η → d+η' at (b−η', b+η'), pinch ¬(b−η) via pullback);
  -- collar₂ (d−η → d+η' RE-WINDOWED at (b+η, b+η'] — the positive pinch (b+η) must be the
  -- window's lo, since the lifted cell ⊆ the source cell cannot inherit positive meeting;
  -- mem(b−η') then recovers by meeting-monotonicity). Each transport: the subtype-universe
  -- bridge + encard_le_encard_of_injOn with f := Subtype.val ∘ F.
  have hmaps :
      (({C : comps stage J (d + η) | C.val ∈ ((fun x => {y | J (d + η) x y}) '' stage (b - η)) ∧
          C.val ∉ ((fun x => {y | J (d + η) x y}) '' stage (b + η))} :
          Set (comps stage J (d + η))).encard
        ≤ ({C : comps stage J (d + η') | C.val ∈
            ((fun x => {y | J (d + η') x y}) '' stage (b - η)) ∧
          C.val ∉ ((fun x => {y | J (d + η') x y}) '' stage (b + η))} :
          Set (comps stage J (d + η'))).encard) ∧
      (({C : comps stage J (d - η') | C.val ∈ ((fun x => {y | J (d - η') x y}) '' stage (b - η')) ∧
          C.val ∉ ((fun x => {y | J (d - η') x y}) '' stage (b + η'))} :
          Set (comps stage J (d - η'))).encard
        ≤ ({C : comps stage J (d - η) | C.val ∈ ((fun x => {y | J (d - η) x y}) '' stage (b - η')) ∧
          C.val ∉ ((fun x => {y | J (d - η) x y}) '' stage (b + η'))} :
          Set (comps stage J (d - η))).encard) ∧
      (({C : comps stage J (d - η) | C.val ∈ ((fun x => {y | J (d - η) x y}) '' stage (b - η')) ∧
          C.val ∉ ((fun x => {y | J (d - η) x y}) '' stage (b + η')) ∧
          C.val ∉ ((fun x => {y | J (d - η) x y}) '' stage (b - η))} :
          Set (comps stage J (d - η))).encard
        ≤ ({C : comps stage J (d + η') | C.val ∈
            ((fun x => {y | J (d + η') x y}) '' stage (b - η')) ∧
          C.val ∉ ((fun x => {y | J (d + η') x y}) '' stage (b + η')) ∧
          C.val ∉ ((fun x => {y | J (d + η') x y}) '' stage (b - η))} :
          Set (comps stage J (d + η'))).encard) ∧
      (({C : comps stage J (d - η) | C.val ∈ ((fun x => {y | J (d - η) x y}) '' stage (b - η')) ∧
          C.val ∈ ((fun x => {y | J (d - η) x y}) '' stage (b + η)) ∧
          C.val ∉ ((fun x => {y | J (d - η) x y}) '' stage (b + η'))} :
          Set (comps stage J (d - η))).encard
        ≤ ({C : comps stage J (d + η') | C.val ∈
            ((fun x => {y | J (d + η') x y}) '' stage (b - η')) ∧
          C.val ∈ ((fun x => {y | J (d + η') x y}) '' stage (b + η)) ∧
          C.val ∉ ((fun x => {y | J (d + η') x y}) '' stage (b + η'))} :
          Set (comps stage J (d + η'))).encard) := by
    -- (0) Bridge: a cell-set's encard is its subtype-universe's encard.
    have hbr : ∀ (w : ℝ) (P : comps stage J w → Prop),
        ({x | P x} : Set (comps stage J w)).encard =
          (Set.univ : Set {x : comps stage J w // P x}).encard := by
      intro w P
      have himg : ({x | P x} : Set (comps stage J w)) =
          Subtype.val '' (Set.univ : Set {x : comps stage J w // P x}) := by
        ext z
        constructor
        · intro hz
          exact ⟨⟨z, hz⟩, Set.mem_univ _, rfl⟩
        · rintro ⟨C, -, rfl⟩
          exact C.property
      rw [himg]
      exact Subtype.val_injective.encard_image _
    -- (1) Meeting is monotone: a cell meeting stage s meets every stage s' ≤ s.
    have hmono : ∀ (u s s' : ℝ), s' ≤ s → ∀ D : comps stage J u,
        D.val ∈ ((fun x => {y | J u x y}) '' stage s) →
        D.val ∈ ((fun x => {y | J u x y}) '' stage s') := by
      intro u s s' hs's D hmem
      obtain ⟨x, hx, hxcls⟩ := hmem
      exact ⟨x, hLaw.antitone hs's hx, hxcls⟩
    -- (2) Transport: an injective window-lift F yields an encard inequality from any
    -- source predicate inside the window to any target predicate covering the image.
    have htr : ∀ (w w' lo hi : ℝ) (F : {C : comps stage J w //
          C.val ∈ ((fun x => {y | J w x y}) '' stage lo) ∧
          C.val ∉ ((fun x => {y | J w x y}) '' stage hi)} →
        {C : comps stage J w' //
          C.val ∈ ((fun x => {y | J w' x y}) '' stage lo) ∧
          C.val ∉ ((fun x => {y | J w' x y}) '' stage hi)}),
      Function.Injective F →
      ∀ (P : comps stage J w → Prop) (Q : comps stage J w' → Prop),
      (∀ C : comps stage J w, P C →
          C.val ∈ ((fun x => {y | J w x y}) '' stage lo) ∧
          C.val ∉ ((fun x => {y | J w x y}) '' stage hi)) →
      (∀ (C : comps stage J w)
          (hC : C.val ∈ ((fun x => {y | J w x y}) '' stage lo))
          (hC' : C.val ∉ ((fun x => {y | J w x y}) '' stage hi)), P C →
          Q (F ⟨C, hC, hC'⟩).val) →
      ({C : comps stage J w | P C} : Set (comps stage J w)).encard ≤
        ({C : comps stage J w' | Q C} : Set (comps stage J w')).encard := by
      intro w w' lo hi F hFinj P Q hPdom hQimg
      have hS := hbr w P
      rw [hS]
      refine Set.encard_le_encard_of_injOn
        (f := fun C : {C : comps stage J w // P C} =>
          (F ⟨(C : comps stage J w), (hPdom (C : comps stage J w) C.property).1,
            (hPdom (C : comps stage J w) C.property).2⟩).val)
        (fun C hC => ?_) (fun C₁ hC₁ C₂ hC₂ heq => ?_)
      · exact hQimg (C : comps stage J w) (hPdom (C : comps stage J w) C.property).1
          (hPdom (C : comps stage J w) C.property).2 C.property
      · have h1 : F ⟨(C₁ : comps stage J w), (hPdom (C₁ : comps stage J w) C₁.property).1,
              (hPdom (C₁ : comps stage J w) C₁.property).2⟩ =
            F ⟨(C₂ : comps stage J w), (hPdom (C₂ : comps stage J w) C₂.property).1,
              (hPdom (C₂ : comps stage J w) C₂.property).2⟩ := Subtype.ext heq
        have h2 := hFinj h1
        injection h2 with h3
        exact Subtype.ext h3
    -- (3) The four transports.
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- plus-box: fixed window (b−η, b+η], probe d+η ↗ d+η'.
      obtain ⟨Fp, hFpinj, -⟩ := hinj (d + η) (d + η') (b - η) (b + η)
        (by linarith) (by linarith)
      exact htr (d + η) (d + η') (b - η) (b + η) Fp hFpinj
        (fun C => C.val ∈ ((fun x => {y | J (d + η) x y}) '' stage (b - η)) ∧
          C.val ∉ ((fun x => {y | J (d + η) x y}) '' stage (b + η)))
        (fun C => C.val ∈ ((fun x => {y | J (d + η') x y}) '' stage (b - η)) ∧
          C.val ∉ ((fun x => {y | J (d + η') x y}) '' stage (b + η)))
        (fun C hC => hC)
        (fun C hC hC' _ => (Fp ⟨C, hC, hC'⟩).property)
    · -- minus-box: fixed window (b−η', b+η'], probe d−η' ↗ d−η.
      obtain ⟨Fm, hFminj, -⟩ := hinj (d - η') (d - η) (b - η') (b + η')
        (by linarith) (by linarith)
      exact htr (d - η') (d - η) (b - η') (b + η') Fm hFminj
        (fun C => C.val ∈ ((fun x => {y | J (d - η') x y}) '' stage (b - η')) ∧
          C.val ∉ ((fun x => {y | J (d - η') x y}) '' stage (b + η')))
        (fun C => C.val ∈ ((fun x => {y | J (d - η) x y}) '' stage (b - η')) ∧
          C.val ∉ ((fun x => {y | J (d - η) x y}) '' stage (b + η')))
        (fun C hC => hC)
        (fun C hC hC' _ => (Fm ⟨C, hC, hC'⟩).property)
    · -- collar₁: window (b−η', b+η'], probe d−η ↗ d+η', pinch ¬(b−η) via pullback.
      obtain ⟨Fc1, hFc1inj, hFc1pull⟩ := hinj (d - η) (d + η') (b - η') (b + η')
        (by linarith) (by linarith)
      exact htr (d - η) (d + η') (b - η') (b + η') Fc1 hFc1inj
        (fun C => C.val ∈ ((fun x => {y | J (d - η) x y}) '' stage (b - η')) ∧
          C.val ∉ ((fun x => {y | J (d - η) x y}) '' stage (b + η')) ∧
          C.val ∉ ((fun x => {y | J (d - η) x y}) '' stage (b - η)))
        (fun C => C.val ∈ ((fun x => {y | J (d + η') x y}) '' stage (b - η')) ∧
          C.val ∉ ((fun x => {y | J (d + η') x y}) '' stage (b + η')) ∧
          C.val ∉ ((fun x => {y | J (d + η') x y}) '' stage (b - η)))
        (fun C hC => ⟨hC.1, hC.2.1⟩)
        (fun C hC hC' hP => ⟨(Fc1 ⟨C, hC, hC'⟩).property.1,
          (Fc1 ⟨C, hC, hC'⟩).property.2,
          fun hmem => hP.2.2 (hFc1pull ⟨C, hC, hC'⟩ (b - η) hmem)⟩)
    · -- collar₂: re-windowed at (b+η, b+η'] so the positive pinch (b+η) is the window's lo;
      -- mem(b−η') then recovers for free by meeting-monotonicity.
      obtain ⟨Fc2, hFc2inj, -⟩ := hinj (d - η) (d + η') (b + η) (b + η')
        (by linarith) (by linarith)
      exact htr (d - η) (d + η') (b + η) (b + η') Fc2 hFc2inj
        (fun C => C.val ∈ ((fun x => {y | J (d - η) x y}) '' stage (b - η')) ∧
          C.val ∈ ((fun x => {y | J (d - η) x y}) '' stage (b + η)) ∧
          C.val ∉ ((fun x => {y | J (d - η) x y}) '' stage (b + η')))
        (fun C => C.val ∈ ((fun x => {y | J (d + η') x y}) '' stage (b - η')) ∧
          C.val ∈ ((fun x => {y | J (d + η') x y}) '' stage (b + η)) ∧
          C.val ∉ ((fun x => {y | J (d + η') x y}) '' stage (b + η')))
        (fun C hC => ⟨hC.2.1, hC.2.2⟩)
        (fun C hC hC' hP => ⟨hmono (d + η') (b + η) (b - η') (by linarith)
            (Fc2 ⟨C, hC, hC'⟩).val (Fc2 ⟨C, hC, hC'⟩).property.1,
          (Fc2 ⟨C, hC, hC'⟩).property.1,
          (Fc2 ⟨C, hC, hC'⟩).property.2⟩)
  -- (c) Pure ℕ∞ arithmetic consuming hmaps: Δ-reduction of both combs (t3_rank_meets; the
  -- meets-sets nest, union-split + t3_add_sub, finiteness via t2_qtame), the collar splits
  -- at d−η and d+η' (wide box = narrow box ⊔ collar₁ ⊔ collar₂; collars disjoint since
  -- meeting (b+η) forces meeting (b−η)), the bookkeeping |Δu| + |Δv'| ≤ |Δu'| + |Δv|,
  -- then the 4-term tsub closure (ENat case-split per t3_add_sub's pattern).
  have harith : t3_comb stage J b d η ≤ t3_comb stage J b d η' := by
    -- (i) ENat closure: with all four values finite, u + v' ≤ u' + v → u − v ≤ u' − v'.
    have htsub : ∀ u v u' v' : ℕ∞, u + v' ≤ u' + v → u ≠ ⊤ → u' ≠ ⊤ → v ≠ ⊤ → v' ≠ ⊤ →
        u - v ≤ u' - v' := by
      intro u v u' v' h hu hu' hv hv'
      cases u with
      | top => exact absurd rfl hu
      | coe a =>
        cases u' with
        | top => exact absurd rfl hu'
        | coe b =>
          cases v with
          | top => exact absurd rfl hv
          | coe c =>
            cases v' with
            | top => exact absurd rfl hv'
            | coe d =>
              norm_cast at h ⊢
              omega
    -- (ii) Δ-reduction: for w ≤ lo ≤ hi the rankFn difference is the window-set encard.
    have hΔ : ∀ (w lo hi : ℝ) (hwlo : w ≤ lo) (hlohi : lo ≤ hi),
        rankFn stage J lo w - rankFn stage J hi w =
          ({C : comps stage J w | C.val ∈ ((fun x => {y | J w x y}) '' stage lo) ∧
              C.val ∉ ((fun x => {y | J w x y}) '' stage hi)} :
            Set (comps stage J w)).encard := by
      intro w lo hi hwlo hlohi
      have hr1 : rankFn stage J lo w =
          ({C : comps stage J w | C.val ∈ ((fun x => {y | J w x y}) '' stage lo)} :
            Set (comps stage J w)).encard := t3_rank_meets hLaw hwlo
      have hr2 : rankFn stage J hi w =
          ({C : comps stage J w | C.val ∈ ((fun x => {y | J w x y}) '' stage hi)} :
            Set (comps stage J w)).encard :=
        t3_rank_meets hLaw (le_trans hwlo hlohi)
      have hfin : ({C : comps stage J w | C.val ∈ ((fun x => {y | J w x y}) '' stage hi)} :
          Set (comps stage J w)).encard ≠ ⊤ := by
        rw [← hr2]
        exact t2_qtame hLaw hTame hi w
      have hun : ({C : comps stage J w | C.val ∈ ((fun x => {y | J w x y}) '' stage lo)} :
          Set (comps stage J w)) =
          ({C : comps stage J w | C.val ∈ ((fun x => {y | J w x y}) '' stage hi)} :
            Set (comps stage J w)) ∪
          ({C : comps stage J w | C.val ∈ ((fun x => {y | J w x y}) '' stage lo) ∧
              C.val ∉ ((fun x => {y | J w x y}) '' stage hi)} :
            Set (comps stage J w)) := by
        ext C
        simp only [Set.mem_setOf_eq, Set.mem_union]
        constructor
        · intro h
          by_cases hC : C.val ∈ ((fun x => {y | J w x y}) '' stage hi)
          · exact Or.inl hC
          · exact Or.inr ⟨h, hC⟩
        · rintro (h | ⟨h1, h2⟩)
          · obtain ⟨x, hx, hxcls⟩ := h
            exact ⟨x, hLaw.antitone hlohi hx, hxcls⟩
          · exact h1
      have hdis : Disjoint
          ({C : comps stage J w | C.val ∈ ((fun x => {y | J w x y}) '' stage hi)} :
            Set (comps stage J w))
          ({C : comps stage J w | C.val ∈ ((fun x => {y | J w x y}) '' stage lo) ∧
              C.val ∉ ((fun x => {y | J w x y}) '' stage hi)} :
            Set (comps stage J w)) := by
        rw [Set.disjoint_left]
        intro C h1 h2
        simp only [Set.mem_setOf_eq] at h1 h2
        exact h2.2 h1
      rw [hr1, hr2, hun, Set.encard_union_eq hdis, t3_add_sub hfin]
    -- (iii) The two combs as window-encard differences.
    have hcombη : t3_comb stage J b d η =
        ({C : comps stage J (d + η) | C.val ∈ ((fun x => {y | J (d + η) x y}) '' stage (b - η)) ∧
            C.val ∉ ((fun x => {y | J (d + η) x y}) '' stage (b + η))} :
          Set (comps stage J (d + η))).encard
        - ({C : comps stage J (d - η) | C.val ∈ ((fun x => {y | J (d - η) x y}) '' stage (b - η)) ∧
            C.val ∉ ((fun x => {y | J (d - η) x y}) '' stage (b + η))} :
          Set (comps stage J (d - η))).encard := by
      simp only [t3_comb]
      rw [hΔ (d + η) (b - η) (b + η) (by linarith) (by linarith),
          hΔ (d - η) (b - η) (b + η) (by linarith) (by linarith)]
    have hcombη' : t3_comb stage J b d η' =
        ({C : comps stage J (d + η') | C.val ∈ ((fun x => {y | J (d + η') x y}) '' stage (b - η')) ∧
            C.val ∉ ((fun x => {y | J (d + η') x y}) '' stage (b + η'))} :
          Set (comps stage J (d + η'))).encard
        - ({C : comps stage J (d - η') | C.val ∈ ((fun x => {y | J (d - η') x y}) '' stage (b - η')) ∧
            C.val ∉ ((fun x => {y | J (d - η') x y}) '' stage (b + η'))} :
          Set (comps stage J (d - η'))).encard := by
      simp only [t3_comb]
      rw [hΔ (d + η') (b - η') (b + η') (by linarith) (by linarith),
          hΔ (d - η') (b - η') (b + η') (by linarith) (by linarith)]
    -- (iv) Finiteness of every window encard (subset of a meets-set; t2_qtame).
    have hfinW : ∀ (w lo : ℝ) (hwlo : w ≤ lo) (P : comps stage J w → Prop)
        (hP : ∀ C, P C → C.val ∈ ((fun x => {y | J w x y}) '' stage lo)),
        ({C : comps stage J w | P C} : Set (comps stage J w)).encard ≠ ⊤ := by
      intro w lo hwlo P hP
      have hle : ({C : comps stage J w | P C} : Set (comps stage J w)).encard ≤
          rankFn stage J lo w := by
        have hsub : ({C : comps stage J w | P C} : Set (comps stage J w)) ⊆
            ({C : comps stage J w | C.val ∈ ((fun x => {y | J w x y}) '' stage lo)} :
              Set (comps stage J w)) := fun C hC => hP C hC
        have h1 := Set.encard_le_encard hsub
        rwa [← t3_rank_meets hLaw hwlo] at h1
      intro h
      rw [h] at hle
      exact (t2_qtame hLaw hTame lo w) (top_le_iff.mp hle)
    have hUfin : ({C : comps stage J (d + η) | C.val ∈ ((fun x => {y | J (d + η) x y}) '' stage (b - η)) ∧
            C.val ∉ ((fun x => {y | J (d + η) x y}) '' stage (b + η))} :
          Set (comps stage J (d + η))).encard ≠ ⊤ :=
      hfinW (d + η) (b - η) (by linarith)
        (fun C => C.val ∈ ((fun x => {y | J (d + η) x y}) '' stage (b - η)) ∧
          C.val ∉ ((fun x => {y | J (d + η) x y}) '' stage (b + η))) (fun _ hC => hC.1)
    have hVfin : ({C : comps stage J (d - η) | C.val ∈ ((fun x => {y | J (d - η) x y}) '' stage (b - η)) ∧
            C.val ∉ ((fun x => {y | J (d - η) x y}) '' stage (b + η))} :
          Set (comps stage J (d - η))).encard ≠ ⊤ :=
      hfinW (d - η) (b - η) (by linarith)
        (fun C => C.val ∈ ((fun x => {y | J (d - η) x y}) '' stage (b - η)) ∧
          C.val ∉ ((fun x => {y | J (d - η) x y}) '' stage (b + η))) (fun _ hC => hC.1)
    have hU'fin : ({C : comps stage J (d + η') | C.val ∈ ((fun x => {y | J (d + η') x y}) '' stage (b - η')) ∧
            C.val ∉ ((fun x => {y | J (d + η') x y}) '' stage (b + η'))} :
          Set (comps stage J (d + η'))).encard ≠ ⊤ :=
      hfinW (d + η') (b - η') (by linarith)
        (fun C => C.val ∈ ((fun x => {y | J (d + η') x y}) '' stage (b - η')) ∧
          C.val ∉ ((fun x => {y | J (d + η') x y}) '' stage (b + η'))) (fun _ hC => hC.1)
    have hV'fin : ({C : comps stage J (d - η') | C.val ∈ ((fun x => {y | J (d - η') x y}) '' stage (b - η')) ∧
            C.val ∉ ((fun x => {y | J (d - η') x y}) '' stage (b + η'))} :
          Set (comps stage J (d - η'))).encard ≠ ⊤ :=
      hfinW (d - η') (b - η') (by linarith)
        (fun C => C.val ∈ ((fun x => {y | J (d - η') x y}) '' stage (b - η')) ∧
          C.val ∉ ((fun x => {y | J (d - η') x y}) '' stage (b + η'))) (fun _ hC => hC.1)
    -- (v) Generic window split: outer window = inner window ⊔ collar₁ ⊔ collar₂.
    have hsplit : ∀ (w lo lo' hi hi' : ℝ) (hlo'lo : lo' ≤ lo) (hlohi : lo ≤ hi)
        (hhihi' : hi ≤ hi'),
        ({C : comps stage J w | C.val ∈ ((fun x => {y | J w x y}) '' stage lo') ∧
            C.val ∉ ((fun x => {y | J w x y}) '' stage hi')} :
          Set (comps stage J w)).encard =
        ({C : comps stage J w | C.val ∈ ((fun x => {y | J w x y}) '' stage lo) ∧
            C.val ∉ ((fun x => {y | J w x y}) '' stage hi)} :
          Set (comps stage J w)).encard
        + ({C : comps stage J w | C.val ∈ ((fun x => {y | J w x y}) '' stage lo') ∧
            C.val ∉ ((fun x => {y | J w x y}) '' stage hi') ∧
            C.val ∉ ((fun x => {y | J w x y}) '' stage lo)} :
          Set (comps stage J w)).encard
        + ({C : comps stage J w | C.val ∈ ((fun x => {y | J w x y}) '' stage lo') ∧
            C.val ∈ ((fun x => {y | J w x y}) '' stage hi) ∧
            C.val ∉ ((fun x => {y | J w x y}) '' stage hi')} :
          Set (comps stage J w)).encard := by
      intro w lo lo' hi hi' hlo'lo hlohi hhihi'
      have hm1 : ∀ C : comps stage J w, C.val ∈ ((fun x => {y | J w x y}) '' stage lo) →
          C.val ∈ ((fun x => {y | J w x y}) '' stage lo') := by
        intro C hC
        obtain ⟨x, hx, hxcls⟩ := hC
        exact ⟨x, hLaw.antitone hlo'lo hx, hxcls⟩
      have hm2 : ∀ C : comps stage J w, C.val ∈ ((fun x => {y | J w x y}) '' stage hi) →
          C.val ∈ ((fun x => {y | J w x y}) '' stage lo) := by
        intro C hC
        obtain ⟨x, hx, hxcls⟩ := hC
        exact ⟨x, hLaw.antitone hlohi hx, hxcls⟩
      have hm3 : ∀ C : comps stage J w, C.val ∉ ((fun x => {y | J w x y}) '' stage hi) →
          C.val ∉ ((fun x => {y | J w x y}) '' stage hi') := by
        intro C hC hmem
        obtain ⟨x, hx, hxcls⟩ := hmem
        exact hC ⟨x, hLaw.antitone hhihi' hx, hxcls⟩
      have hunion : ({C : comps stage J w | C.val ∈ ((fun x => {y | J w x y}) '' stage lo') ∧
            C.val ∉ ((fun x => {y | J w x y}) '' stage hi')} : Set (comps stage J w)) =
          ({C : comps stage J w | C.val ∈ ((fun x => {y | J w x y}) '' stage lo) ∧
              C.val ∉ ((fun x => {y | J w x y}) '' stage hi)} : Set (comps stage J w)) ∪
          (({C : comps stage J w | C.val ∈ ((fun x => {y | J w x y}) '' stage lo') ∧
              C.val ∉ ((fun x => {y | J w x y}) '' stage hi') ∧
              C.val ∉ ((fun x => {y | J w x y}) '' stage lo)} : Set (comps stage J w)) ∪
          ({C : comps stage J w | C.val ∈ ((fun x => {y | J w x y}) '' stage lo') ∧
              C.val ∈ ((fun x => {y | J w x y}) '' stage hi) ∧
              C.val ∉ ((fun x => {y | J w x y}) '' stage hi')} : Set (comps stage J w))) := by
        ext C
        simp only [Set.mem_setOf_eq, Set.mem_union]
        constructor
        · rintro ⟨h1, h2⟩
          by_cases hC : C.val ∈ ((fun x => {y | J w x y}) '' stage lo)
          · by_cases hH : C.val ∈ ((fun x => {y | J w x y}) '' stage hi)
            · exact Or.inr (Or.inr ⟨h1, hH, h2⟩)
            · exact Or.inl ⟨hC, hH⟩
          · exact Or.inr (Or.inl ⟨h1, h2, hC⟩)
        · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
          · exact ⟨hm1 C h1, hm3 C h2⟩
          · exact ⟨h1, h2⟩
          · exact ⟨h1, h3⟩
      have hdis1 : Disjoint
          ({C : comps stage J w | C.val ∈ ((fun x => {y | J w x y}) '' stage lo) ∧
              C.val ∉ ((fun x => {y | J w x y}) '' stage hi)} : Set (comps stage J w))
          (({C : comps stage J w | C.val ∈ ((fun x => {y | J w x y}) '' stage lo') ∧
              C.val ∉ ((fun x => {y | J w x y}) '' stage hi') ∧
              C.val ∉ ((fun x => {y | J w x y}) '' stage lo)} : Set (comps stage J w)) ∪
          ({C : comps stage J w | C.val ∈ ((fun x => {y | J w x y}) '' stage lo') ∧
              C.val ∈ ((fun x => {y | J w x y}) '' stage hi) ∧
              C.val ∉ ((fun x => {y | J w x y}) '' stage hi')} : Set (comps stage J w))) := by
        rw [Set.disjoint_union_right]
        refine ⟨?_, ?_⟩
        · rw [Set.disjoint_left]
          intro C h1 h2
          simp only [Set.mem_setOf_eq] at h1 h2
          exact h2.2.2 h1.1
        · rw [Set.disjoint_left]
          intro C h1 h2
          simp only [Set.mem_setOf_eq] at h1 h2
          exact h1.2 h2.2.1
      have hdis2 : Disjoint
          ({C : comps stage J w | C.val ∈ ((fun x => {y | J w x y}) '' stage lo') ∧
              C.val ∉ ((fun x => {y | J w x y}) '' stage hi') ∧
              C.val ∉ ((fun x => {y | J w x y}) '' stage lo)} : Set (comps stage J w))
          ({C : comps stage J w | C.val ∈ ((fun x => {y | J w x y}) '' stage lo') ∧
              C.val ∈ ((fun x => {y | J w x y}) '' stage hi) ∧
              C.val ∉ ((fun x => {y | J w x y}) '' stage hi')} : Set (comps stage J w)) := by
        rw [Set.disjoint_left]
        intro C h1 h2
        simp only [Set.mem_setOf_eq] at h1 h2
        exact h1.2.2 (hm2 C h2.2.1)
      rw [hunion, Set.encard_union_eq hdis1, Set.encard_union_eq hdis2]
      abel
    -- (vi) The 4-term bookkeeping: |Δu| + |Δv'| ≤ |Δu'| + |Δv|.
    obtain ⟨h1, h2, h3, h4⟩ := hmaps
    have hkey : ({C : comps stage J (d + η) | C.val ∈ ((fun x => {y | J (d + η) x y}) '' stage (b - η)) ∧
            C.val ∉ ((fun x => {y | J (d + η) x y}) '' stage (b + η))} :
          Set (comps stage J (d + η))).encard
        + ({C : comps stage J (d - η') | C.val ∈ ((fun x => {y | J (d - η') x y}) '' stage (b - η')) ∧
            C.val ∉ ((fun x => {y | J (d - η') x y}) '' stage (b + η'))} :
          Set (comps stage J (d - η'))).encard
        ≤ ({C : comps stage J (d + η') | C.val ∈ ((fun x => {y | J (d + η') x y}) '' stage (b - η')) ∧
            C.val ∉ ((fun x => {y | J (d + η') x y}) '' stage (b + η'))} :
          Set (comps stage J (d + η'))).encard
        + ({C : comps stage J (d - η) | C.val ∈ ((fun x => {y | J (d - η) x y}) '' stage (b - η)) ∧
            C.val ∉ ((fun x => {y | J (d - η) x y}) '' stage (b + η))} :
          Set (comps stage J (d - η))).encard := by
      have hsplitW := hsplit (d - η) (b - η) (b - η') (b + η) (b + η')
        (by linarith) (by linarith) (by linarith)
      have hsplitU' := hsplit (d + η') (b - η) (b - η') (b + η) (b + η')
        (by linarith) (by linarith) (by linarith)
      calc ({C : comps stage J (d + η) | C.val ∈ ((fun x => {y | J (d + η) x y}) '' stage (b - η)) ∧
            C.val ∉ ((fun x => {y | J (d + η) x y}) '' stage (b + η))} :
          Set (comps stage J (d + η))).encard
          + ({C : comps stage J (d - η') | C.val ∈ ((fun x => {y | J (d - η') x y}) '' stage (b - η')) ∧
            C.val ∉ ((fun x => {y | J (d - η') x y}) '' stage (b + η'))} :
          Set (comps stage J (d - η'))).encard
          ≤ ({C : comps stage J (d + η') | C.val ∈
            ((fun x => {y | J (d + η') x y}) '' stage (b - η)) ∧
            C.val ∉ ((fun x => {y | J (d + η') x y}) '' stage (b + η))} :
          Set (comps stage J (d + η'))).encard
          + ({C : comps stage J (d - η) | C.val ∈ ((fun x => {y | J (d - η) x y}) '' stage (b - η')) ∧
            C.val ∉ ((fun x => {y | J (d - η) x y}) '' stage (b + η'))} :
          Set (comps stage J (d - η))).encard := add_le_add h1 h2
        _ = ({C : comps stage J (d + η') | C.val ∈
            ((fun x => {y | J (d + η') x y}) '' stage (b - η)) ∧
            C.val ∉ ((fun x => {y | J (d + η') x y}) '' stage (b + η))} :
          Set (comps stage J (d + η'))).encard
          + (({C : comps stage J (d - η) | C.val ∈ ((fun x => {y | J (d - η) x y}) '' stage (b - η)) ∧
            C.val ∉ ((fun x => {y | J (d - η) x y}) '' stage (b + η))} :
          Set (comps stage J (d - η))).encard
          + ({C : comps stage J (d - η) | C.val ∈ ((fun x => {y | J (d - η) x y}) '' stage (b - η')) ∧
            C.val ∉ ((fun x => {y | J (d - η) x y}) '' stage (b + η')) ∧
            C.val ∉ ((fun x => {y | J (d - η) x y}) '' stage (b - η))} :
          Set (comps stage J (d - η))).encard
          + ({C : comps stage J (d - η) | C.val ∈ ((fun x => {y | J (d - η) x y}) '' stage (b - η')) ∧
            C.val ∈ ((fun x => {y | J (d - η) x y}) '' stage (b + η)) ∧
            C.val ∉ ((fun x => {y | J (d - η) x y}) '' stage (b + η'))} :
          Set (comps stage J (d - η))).encard) := by rw [hsplitW]
        _ ≤ ({C : comps stage J (d + η') | C.val ∈
            ((fun x => {y | J (d + η') x y}) '' stage (b - η)) ∧
            C.val ∉ ((fun x => {y | J (d + η') x y}) '' stage (b + η))} :
          Set (comps stage J (d + η'))).encard
          + (({C : comps stage J (d - η) | C.val ∈ ((fun x => {y | J (d - η) x y}) '' stage (b - η)) ∧
            C.val ∉ ((fun x => {y | J (d - η) x y}) '' stage (b + η))} :
          Set (comps stage J (d - η))).encard
          + ({C : comps stage J (d + η') | C.val ∈
            ((fun x => {y | J (d + η') x y}) '' stage (b - η')) ∧
            C.val ∉ ((fun x => {y | J (d + η') x y}) '' stage (b + η')) ∧
            C.val ∉ ((fun x => {y | J (d + η') x y}) '' stage (b - η))} :
          Set (comps stage J (d + η'))).encard
          + ({C : comps stage J (d + η') | C.val ∈
            ((fun x => {y | J (d + η') x y}) '' stage (b - η')) ∧
            C.val ∈ ((fun x => {y | J (d + η') x y}) '' stage (b + η)) ∧
            C.val ∉ ((fun x => {y | J (d + η') x y}) '' stage (b + η'))} :
          Set (comps stage J (d + η'))).encard) :=
          add_le_add le_rfl (add_le_add (add_le_add le_rfl h3) h4)
        _ = (({C : comps stage J (d + η') | C.val ∈
            ((fun x => {y | J (d + η') x y}) '' stage (b - η)) ∧
            C.val ∉ ((fun x => {y | J (d + η') x y}) '' stage (b + η))} :
          Set (comps stage J (d + η'))).encard
          + ({C : comps stage J (d + η') | C.val ∈
            ((fun x => {y | J (d + η') x y}) '' stage (b - η')) ∧
            C.val ∉ ((fun x => {y | J (d + η') x y}) '' stage (b + η')) ∧
            C.val ∉ ((fun x => {y | J (d + η') x y}) '' stage (b - η))} :
          Set (comps stage J (d + η'))).encard
          + ({C : comps stage J (d + η') | C.val ∈
            ((fun x => {y | J (d + η') x y}) '' stage (b - η')) ∧
            C.val ∈ ((fun x => {y | J (d + η') x y}) '' stage (b + η)) ∧
            C.val ∉ ((fun x => {y | J (d + η') x y}) '' stage (b + η'))} :
          Set (comps stage J (d + η'))).encard)
          + ({C : comps stage J (d - η) | C.val ∈ ((fun x => {y | J (d - η) x y}) '' stage (b - η)) ∧
            C.val ∉ ((fun x => {y | J (d - η) x y}) '' stage (b + η))} :
          Set (comps stage J (d - η))).encard := by abel
        _ = ({C : comps stage J (d + η') | C.val ∈ ((fun x => {y | J (d + η') x y}) '' stage (b - η')) ∧
            C.val ∉ ((fun x => {y | J (d + η') x y}) '' stage (b + η'))} :
          Set (comps stage J (d + η'))).encard
          + ({C : comps stage J (d - η) | C.val ∈ ((fun x => {y | J (d - η) x y}) '' stage (b - η)) ∧
            C.val ∉ ((fun x => {y | J (d - η) x y}) '' stage (b + η))} :
          Set (comps stage J (d - η))).encard := by rw [← hsplitU']
    rw [hcombη, hcombη']
    exact htsub _ _ _ _ hkey hUfin hU'fin hVfin hV'fin
  exact harith


theorem t3_census_red {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {b η δ₀ v : ℝ}
    (hη : η ∈ Set.Ioo (0 : ℝ) δ₀) (hδ₀b : ∀ τ ∈ critSet hTame, τ ≠ b → δ₀ < |τ - b|) :
    ({C : comps stage J v | b - η < birthSup hLaw v C ∧ birthSup hLaw v C < b + η} :
      Set (comps stage J v))
      = {C : comps stage J v | birthSup hLaw v C = b} := by
  ext C
  exact t3_win_beta hLaw hTame C b η hη.1
    (fun τ hτ hτne => by have := hδ₀b τ hτ hτne; linarith [hη.2])


theorem t3_avoidOf {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {b d δ₀ : ℝ}
    (hgap : (∀ τ ∈ critSet hTame, τ ≠ b → δ₀ < |τ - b|) ∧
      (∀ τ ∈ critSet hTame, τ ≠ d → δ₀ < |τ - d|))
    {ζ : ℝ} (hζ : ζ ∈ Set.Ioo (0 : ℝ) δ₀) (t : ℝ) (C : comps stage J t) :
    b - ζ ≠ birthSup hLaw t C ∧ b + ζ ≠ birthSup hLaw t C ∧
      d + ζ ≠ birthSup hLaw t C ∧ d - ζ ≠ birthSup hLaw t C := by
  have hcrit := t3_bSup_in_crit hLaw hTame C
  have hζδ : ζ < δ₀ := hζ.2
  have hζ0 : 0 < ζ := hζ.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro heq
    by_cases hb : birthSup hLaw t C = b
    · linarith [heq, hb, hζ0]
    · have hg := hgap.1 _ hcrit hb
      have habs : |birthSup hLaw t C - b| = ζ := by
        rw [show birthSup hLaw t C = b - ζ from heq.symm]
        rw [show b - ζ - b = -ζ by ring, abs_neg, abs_of_pos hζ0]
      linarith [hg, habs, hζδ]
  · intro heq
    by_cases hb : birthSup hLaw t C = b
    · linarith [heq, hb, hζ0]
    · have hg := hgap.1 _ hcrit hb
      have habs : |birthSup hLaw t C - b| = ζ := by
        rw [show birthSup hLaw t C = b + ζ from heq.symm]
        rw [show b + ζ - b = ζ by ring, abs_of_pos hζ0]
      linarith [hg, habs, hζδ]
  · intro heq
    by_cases hd : birthSup hLaw t C = d
    · linarith [heq, hd, hζ0]
    · have hg := hgap.2 _ hcrit hd
      have habs : |birthSup hLaw t C - d| = ζ := by
        rw [show birthSup hLaw t C = d + ζ from heq.symm]
        rw [show d + ζ - d = ζ by ring, abs_of_pos hζ0]
      linarith [hg, habs, hζδ]
  · intro heq
    by_cases hd : birthSup hLaw t C = d
    · linarith [heq, hd, hζ0]
    · have hg := hgap.2 _ hcrit hd
      have habs : |birthSup hLaw t C - d| = ζ := by
        rw [show birthSup hLaw t C = d - ζ from heq.symm]
        rw [show d - ζ - d = -ζ by ring, abs_neg, abs_of_pos hζ0]
      linarith [hg, habs, hζδ]


theorem t3_comb_small {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {b d δ₀ : ℝ} (hbd : d < b)
    (hgap : (∀ τ ∈ critSet hTame, τ ≠ b → δ₀ < |τ - b|) ∧
      (∀ τ ∈ critSet hTame, τ ≠ d → δ₀ < |τ - d|))
    {η : ℝ} (hη : η ∈ Set.Ioo (0 : ℝ) δ₀) (hηbd : η < (b - d) / 2) :
    t3_comb stage J b d η =
      (({C : comps stage J (d + η) | birthSup hLaw (d + η) C = b} :
          Set (comps stage J (d + η))).encard
        - ({C : comps stage J (d - η) | birthSup hLaw (d - η) C = b} :
          Set (comps stage J (d - η))).encard : ℕ∞) := by
  simp only [t3_comb]
  rw [t3_box_identity hLaw hTame hbd hη.1 (by linarith [hηbd, hbd]) (t3_avoidOf hLaw hTame hgap hη),
      t3_census_red hLaw hTame hη hgap.1, t3_census_red hLaw hTame hη hgap.1]

/-- T3a-ii(a): no bar dies at a non-critical level — the death-pinning. -/
theorem solution {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {b d : ℝ} (hbd : d < b)
    (hd : d ∉ (critSet hTame : Set ℝ)) :
    mult (rankFn stage J) ((b : EReal), (d : EReal)) = 0 := by
  obtain ⟨δ₀, hδ0, hδle, hgap⟩ := t3_stable_delta hLaw hTame hbd
  have hηmem : δ₀ / 2 ∈ Set.Ioo (0 : ℝ) δ₀ := ⟨by linarith, by linarith⟩
  have hηbd : δ₀ / 2 < (b - d) / 2 := by linarith
  have hfree : ∀ τ ∈ critSet hTame, τ < d - δ₀ / 2 ∨ d + δ₀ / 2 < τ := by
    intro τ hτ
    have hne : τ ≠ d := fun heq => hd (heq ▸ hτ)
    have hg := hgap.2 τ hτ hne
    rcases lt_or_ge τ d with hlt | hge
    · left
      rw [abs_of_neg (show τ - d < 0 by linarith)] at hg
      linarith
    · right
      rw [abs_of_nonneg (show 0 ≤ τ - d by linarith)] at hg
      linarith
  have hself : ({C : comps stage J (d - δ₀ / 2) | birthSup hLaw (d - δ₀ / 2) C = b} :
      Set (comps stage J (d - δ₀ / 2))).encard =
      ({C : comps stage J (d + δ₀ / 2) | birthSup hLaw (d + δ₀ / 2) C = b} :
      Set (comps stage J (d + δ₀ / 2))).encard :=
    t3_selfTrans hLaw hTame (by linarith) hfree (by linarith) (by linarith)
  rw [t3_mult_unfold hLaw hbd]
  refine le_antisymm ?_ zero_le
  refine le_trans (iInf₂_le (δ₀ / 2) ⟨by linarith, hηbd⟩) ?_
  rw [t3_comb_small hLaw hTame hbd hgap hηmem hηbd, hself, tsub_self]
