-- Prove2me | solution 1 for PersistClust.Count.qse_demand_injection
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-16T04:21:12.237065+00:00
-- url     : https://prove2.me/submissions/b477da97-636d-4d9c-a6ca-4d814983919e

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus
import Definitions.Def_PersistClust_Count_MatchingGate

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
  · 
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
  · 
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
  · 
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
  · 
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
  · 
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
    
    have hclasseq : ∀ (t : ℝ) (x y : ι) (h : J t x y), {z | J t x z} = {z | J t y z} := by
      intro t x y h
      ext z
      exact ⟨fun hz => hLaw.trans (hLaw.symm h) hz, fun hz => hLaw.trans h hz⟩
    
    
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
    
    have hmono : ∀ (u s s' : ℝ), s' ≤ s → ∀ D : comps stage J u,
        D.val ∈ ((fun x => {y | J u x y}) '' stage s) →
        D.val ∈ ((fun x => {y | J u x y}) '' stage s') := by
      intro u s s' hs's D hmem
      obtain ⟨x, hx, hxcls⟩ := hmem
      exact ⟨x, hLaw.antitone hs's hx, hxcls⟩
    
    
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
    
    refine ⟨?_, ?_, ?_, ?_⟩
    · 
      obtain ⟨Fp, hFpinj, -⟩ := hinj (d + η) (d + η') (b - η) (b + η)
        (by linarith) (by linarith)
      exact htr (d + η) (d + η') (b - η) (b + η) Fp hFpinj
        (fun C => C.val ∈ ((fun x => {y | J (d + η) x y}) '' stage (b - η)) ∧
          C.val ∉ ((fun x => {y | J (d + η) x y}) '' stage (b + η)))
        (fun C => C.val ∈ ((fun x => {y | J (d + η') x y}) '' stage (b - η)) ∧
          C.val ∉ ((fun x => {y | J (d + η') x y}) '' stage (b + η)))
        (fun C hC => hC)
        (fun C hC hC' _ => (Fp ⟨C, hC, hC'⟩).property)
    · 
      obtain ⟨Fm, hFminj, -⟩ := hinj (d - η') (d - η) (b - η') (b + η')
        (by linarith) (by linarith)
      exact htr (d - η') (d - η) (b - η') (b + η') Fm hFminj
        (fun C => C.val ∈ ((fun x => {y | J (d - η') x y}) '' stage (b - η')) ∧
          C.val ∉ ((fun x => {y | J (d - η') x y}) '' stage (b + η')))
        (fun C => C.val ∈ ((fun x => {y | J (d - η) x y}) '' stage (b - η')) ∧
          C.val ∉ ((fun x => {y | J (d - η) x y}) '' stage (b + η')))
        (fun C hC => hC)
        (fun C hC hC' _ => (Fm ⟨C, hC, hC'⟩).property)
    · 
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
    · 
      
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
  
  
  
  
  
  have harith : t3_comb stage J b d η ≤ t3_comb stage J b d η' := by
    
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

theorem t3_death_pin {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
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

theorem t3_birth_pin {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {b d : ℝ} (hbd : d < b)
    (hb : b ∉ (critSet hTame : Set ℝ)) :
    mult (rankFn stage J) ((b : EReal), (d : EReal)) = 0 := by
  by_contra hne
  obtain ⟨δ₀, hδ0, hδle, hgap⟩ := t3_stable_delta hLaw hTame hbd
  have hη0 : 0 < min (δ₀ / 2) ((b - d) / 4) := lt_min (by linarith) (by linarith)
  have hηmem : min (δ₀ / 2) ((b - d) / 4) ∈ Set.Ioo (0 : ℝ) δ₀ :=
    ⟨hη0, (min_le_left _ _).trans_lt (by linarith)⟩
  have hηbd : min (δ₀ / 2) ((b - d) / 4) < (b - d) / 2 :=
    (min_le_right _ _).trans_lt (by linarith)
  have h1 : 1 ≤ mult (rankFn stage J) ((b : EReal), (d : EReal)) :=
    Order.one_le_iff_ne_zero.mpr hne
  rw [t3_mult_unfold hLaw hbd] at h1
  have h2 : 1 ≤ t3_comb stage J b d (min (δ₀ / 2) ((b - d) / 4)) :=
    le_trans h1 (iInf₂_le _ ⟨hη0, hηbd⟩)
  rw [t3_comb_small hLaw hTame hbd hgap hηmem hηbd] at h2
  have hcensus : ({C : comps stage J (d + min (δ₀ / 2) ((b - d) / 4)) |
      birthSup hLaw (d + min (δ₀ / 2) ((b - d) / 4)) C = b} :
      Set (comps stage J (d + min (δ₀ / 2) ((b - d) / 4)))).encard ≠ 0 := by
    intro hzero
    rw [hzero, zero_tsub] at h2
    exact absurd h2 (by simp)
  obtain ⟨C, hC⟩ : ({C : comps stage J (d + min (δ₀ / 2) ((b - d) / 4)) |
      birthSup hLaw (d + min (δ₀ / 2) ((b - d) / 4)) C = b} :
      Set (comps stage J (d + min (δ₀ / 2) ((b - d) / 4)))).Nonempty := by
    by_contra hempty
    refine hcensus ?_
    rw [Set.eq_empty_iff_forall_notMem.mpr (fun C hC => hempty ⟨C, hC⟩), Set.encard_empty]
  simp only [Set.mem_setOf_eq] at hC
  exact hb (by rw [← hC]; exact t3_bSup_in_crit hLaw hTame C)

theorem t3_ess_pin {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {b : ℝ}
    (hb : b ∉ (critSet hTame : Set ℝ)) :
    mult (rankFn stage J) ((b : EReal), (⊥ : EReal)) = 0 := by
  obtain ⟨δ₀, hδ0, hδle, hgap⟩ := t3_gapEx (critSet hTame) (show 0 < (1 : ℝ) by norm_num) b
  have hε0 : 0 < δ₀ / 2 := by linarith
  have hgen : ∀ C : comps stage J (b - 1), b - δ₀ / 2 ≠ birthSup hLaw (b - 1) C ∧
      b + δ₀ / 2 ≠ birthSup hLaw (b - 1) C := by
    intro C
    have hcrit := t3_bSup_in_crit hLaw hTame C
    constructor
    · intro heq
      have hg := hgap (b - δ₀ / 2) (by rw [heq]; exact hcrit) (by linarith)
      have habs : |b - δ₀ / 2 - b| = δ₀ / 2 := by
        have hsub : b - δ₀ / 2 - b = -(δ₀ / 2) := by ring
        rw [hsub, abs_neg, abs_of_pos hε0]
      linarith
    · intro heq
      have hg := hgap (b + δ₀ / 2) (by rw [heq]; exact hcrit) (by linarith)
      have habs : |b + δ₀ / 2 - b| = δ₀ / 2 := by
        have hsub : b + δ₀ / 2 - b = δ₀ / 2 := by ring
        rw [hsub, abs_of_pos hε0]
      linarith
  have hempty : ∀ C : comps stage J (b - 1),
      ¬(b - δ₀ / 2 < birthSup hLaw (b - 1) C ∧ birthSup hLaw (b - 1) C < b + δ₀ / 2) := by
    intro C hC
    have hcrit := t3_bSup_in_crit hLaw hTame C
    by_cases hbeq : birthSup hLaw (b - 1) C = b
    · exact hb (by rw [← hbeq]; exact hcrit)
    · have hg := hgap _ hcrit hbeq
      rcases lt_or_ge (birthSup hLaw (b - 1) C) b with hlt | hge
      · rw [abs_of_neg (show birthSup hLaw (b - 1) C - b < 0 by linarith)] at hg
        linarith
      · rw [abs_of_nonneg (show 0 ≤ birthSup hLaw (b - 1) C - b by linarith)] at hg
        linarith
  have hval : rankFn stage J (b - δ₀ / 2) (b - 1) - rankFn stage J (b + δ₀ / 2) (b - 1) = 0 := by
    have hsplit := t3_windowSplit hLaw hTame hε0 (by linarith) hgen
    rw [hsplit, t3_add_sub (t2_qtame hLaw hTame (b + δ₀ / 2) (b - 1)),
      show ({C : comps stage J (b - 1) | b - δ₀ / 2 < birthSup hLaw (b - 1) C ∧
          birthSup hLaw (b - 1) C < b + δ₀ / 2} : Set (comps stage J (b - 1))) = ∅ from
        Set.eq_empty_iff_forall_notMem.mpr hempty, Set.encard_empty]
  rw [show mult (rankFn stage J) ((b : EReal), (⊥ : EReal)) =
      ⨅ (ε : ℝ) (_ : 0 < ε), ⨅ (t : ℝ) (_ : t ≤ b - ε),
        (rankFn stage J (b - ε) t - rankFn stage J (b + ε) t) from by
      unfold mult
      rw [if_pos ⟨EReal.coe_ne_bot b, EReal.coe_ne_top b⟩, if_pos rfl]
      simp only [EReal.toReal_coe]]
  refine le_antisymm ?_ zero_le
  refine le_trans (le_trans (iInf₂_le (δ₀ / 2) hε0) (iInf₂_le (b - 1) (by linarith))) ?_
  rw [hval]

theorem t3_mult_lt_top {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) (p : EReal × EReal)
    (hp : p.2 = ⊥ ∨ p.2 < p.1) : mult (rankFn stage J) p ≠ ⊤ := by
  have hexcl : ∀ x y : ℕ∞, x ≤ y → y ≠ ⊤ → x ≠ ⊤ := by
    intro x y hle hy htop
    rw [htop] at hle
    exact hy (top_le_iff.mp hle)
  by_cases h1 : p.1 ≠ ⊥ ∧ p.1 ≠ ⊤
  · by_cases h2 : p.2 = ⊥
    · rw [mult, if_pos h1, if_pos h2]
      refine hexcl _ _ ?_ (t2_qtame hLaw hTame (p.1.toReal - 1) (p.1.toReal - 1))
      calc (⨅ (ε : ℝ) (_ : 0 < ε), ⨅ (t : ℝ) (_ : t ≤ p.1.toReal - ε),
            rankFn stage J (p.1.toReal - ε) t - rankFn stage J (p.1.toReal + ε) t)
          ≤ ⨅ (t : ℝ) (_ : t ≤ p.1.toReal - 1),
            rankFn stage J (p.1.toReal - 1) t - rankFn stage J (p.1.toReal + 1) t :=
            iInf₂_le (1 : ℝ) one_pos
        _ ≤ rankFn stage J (p.1.toReal - 1) (p.1.toReal - 1)
              - rankFn stage J (p.1.toReal + 1) (p.1.toReal - 1) :=
            iInf₂_le (p.1.toReal - 1) (by exact le_refl _)
        _ ≤ rankFn stage J (p.1.toReal - 1) (p.1.toReal - 1) := tsub_le_self
    · have h3' : p.2 < p.1 := hp.resolve_left h2
      have h2top : p.2 ≠ ⊤ := by
        intro h
        rw [h] at h3'
        exact absurd (h3'.trans_le le_top) (lt_irrefl ⊤)
      have hdbd : p.2.toReal < p.1.toReal := by
        have hd : p.2 = (p.2.toReal : EReal) := (EReal.coe_toReal h2top h2).symm
        have hb : p.1 = (p.1.toReal : EReal) := (EReal.coe_toReal h1.2 h1.1).symm
        exact EReal.coe_lt_coe_iff.mp (by rw [← hd, ← hb]; exact h3')
      rw [mult, if_pos h1, if_neg h2, if_pos h3']
      refine hexcl _ _ ?_ (t2_qtame hLaw hTame
        (p.1.toReal - (p.1.toReal - p.2.toReal) / 4)
        (p.2.toReal + (p.1.toReal - p.2.toReal) / 4))
      calc (⨅ (ε : ℝ) (_ : ε ∈ Set.Ioo (0 : ℝ) ((p.1.toReal - p.2.toReal) / 2)),
            ((rankFn stage J (p.1.toReal - ε) (p.2.toReal + ε)
                - rankFn stage J (p.1.toReal + ε) (p.2.toReal + ε))
              - (rankFn stage J (p.1.toReal - ε) (p.2.toReal - ε)
                - rankFn stage J (p.1.toReal + ε) (p.2.toReal - ε))))
          ≤ ((rankFn stage J (p.1.toReal - (p.1.toReal - p.2.toReal) / 4)
                  (p.2.toReal + (p.1.toReal - p.2.toReal) / 4)
                - rankFn stage J (p.1.toReal + (p.1.toReal - p.2.toReal) / 4)
                  (p.2.toReal + (p.1.toReal - p.2.toReal) / 4))
              - (rankFn stage J (p.1.toReal - (p.1.toReal - p.2.toReal) / 4)
                  (p.2.toReal - (p.1.toReal - p.2.toReal) / 4)
                - rankFn stage J (p.1.toReal + (p.1.toReal - p.2.toReal) / 4)
                  (p.2.toReal - (p.1.toReal - p.2.toReal) / 4))) :=
            iInf₂_le ((p.1.toReal - p.2.toReal) / 4) ⟨by linarith, by linarith⟩
        _ ≤ rankFn stage J (p.1.toReal - (p.1.toReal - p.2.toReal) / 4)
              (p.2.toReal + (p.1.toReal - p.2.toReal) / 4) :=
            tsub_le_self.trans tsub_le_self
  · rw [mult, if_neg h1]
    exact ENat.coe_ne_top 0

theorem t3a_threadIdentity {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) :
    ∃ tc : EReal × EReal → ℕ,
      {p : EReal × EReal | tc p ≠ 0}.Finite ∧
      (∀ p : EReal × EReal, (p.2 = ⊥ ∨ p.2 < p.1) → mult (rankFn stage J) p = tc p) := by
  classical
  refine ⟨fun p => (mult (rankFn stage J) p).toNat, ?_, ?_⟩
  · 
    have hgrid : {p : EReal × EReal |
        ∃ b ∈ (critSet hTame : Set ℝ), p.1 = (b : EReal) ∧
          ((∃ d ∈ (critSet hTame : Set ℝ), p.2 = (d : EReal)) ∨ p.2 = ⊥)}.Finite := by
      have hfinR : ((critSet hTame : Set ℝ)).Finite := (critSet hTame).finite_toSet
      have himg : {x : EReal | ∃ y ∈ (critSet hTame : Set ℝ), x = (y : EReal)}.Finite := by
        apply Set.Finite.subset (hfinR.image (fun x : ℝ => (x : EReal)))
        rintro x ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
      have hfin2 : ({x : EReal | ∃ y ∈ (critSet hTame : Set ℝ), x = (y : EReal)} ∪
          {(⊥ : EReal)}).Finite := himg.union (Set.finite_singleton _)
      refine Set.Finite.subset (himg.prod hfin2) ?_
      rintro ⟨b', d'⟩ hp
      simp only [Set.mem_setOf_eq] at hp
      obtain ⟨b, hb, heqb, hd⟩ := hp
      have hbmem : b' ∈ {x : EReal | ∃ y ∈ (critSet hTame : Set ℝ), x = (y : EReal)} :=
        ⟨b, hb, heqb⟩
      refine ⟨hbmem, ?_⟩
      rcases hd with ⟨d, hdm, heqd⟩ | hbot
      · exact Or.inl ⟨d, hdm, heqd⟩
      · exact Or.inr hbot
    refine Set.Finite.subset hgrid ?_
    intro p hp
    simp only [Set.mem_setOf_eq] at hp
    have hne0 : mult (rankFn stage J) p ≠ 0 := by
      by_cases htop : mult (rankFn stage J) p = ⊤
      · rw [htop] at hp
        exact (hp rfl).elim
      · intro h0
        rw [h0] at hp
        exact hp rfl
    by_cases h1 : p.1 ≠ ⊥ ∧ p.1 ≠ ⊤
    · by_cases h2 : p.2 = ⊥
      · by_contra hnotin
        apply hne0
        have hb : p.1 = (p.1.toReal : EReal) := (EReal.coe_toReal h1.2 h1.1).symm
        have hpe : p = ((p.1.toReal : EReal), (⊥ : EReal)) := Prod.ext hb h2
        rw [hpe]
        exact t3_ess_pin hLaw hTame
          (fun hmem => hnotin ⟨p.1.toReal, hmem, hb, Or.inr h2⟩)
      · by_cases h3 : p.2 < p.1
        · by_contra hnotin
          have h2top : p.2 ≠ ⊤ := by
            intro h
            rw [h] at h3
            exact absurd (h3.trans_le le_top) (lt_irrefl ⊤)
          have hd : p.2 = (p.2.toReal : EReal) := (EReal.coe_toReal h2top h2).symm
          have hb : p.1 = (p.1.toReal : EReal) := (EReal.coe_toReal h1.2 h1.1).symm
          have hdbd : p.2.toReal < p.1.toReal :=
            EReal.coe_lt_coe_iff.mp (by rw [← hd, ← hb]; exact h3)
          have hpe : p = ((p.1.toReal : EReal), (p.2.toReal : EReal)) := Prod.ext hb hd
          have hbcrit : p.1.toReal ∈ (critSet hTame : Set ℝ) := by
            by_contra hmem
            apply hne0
            rw [hpe]
            exact t3_birth_pin hLaw hTame hdbd hmem
          have hdcrit : p.2.toReal ∈ (critSet hTame : Set ℝ) := by
            by_contra hmem
            apply hne0
            rw [hpe]
            exact t3_death_pin hLaw hTame hdbd hmem
          exact hnotin ⟨p.1.toReal, hbcrit, hb, Or.inl ⟨p.2.toReal, hdcrit, hd⟩⟩
        · exact absurd (show mult (rankFn stage J) p = 0 from by
            rw [mult, if_pos h1, if_neg h2, if_neg h3]) hne0
    · exact absurd (show mult (rankFn stage J) p = 0 from by rw [mult, if_neg h1]) hne0
  · 
    intro p hp
    exact (ENat.natCast_toNat (t3_mult_lt_top hLaw hTame p hp)).symm

theorem t2_finDiag {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) :
    {p : EReal × EReal | mult (rankFn stage J) p ≠ 0}.Finite := by
  obtain ⟨tc, hfin, hid⟩ := t3a_threadIdentity hLaw hTame
  apply Set.Finite.subset hfin
  intro p hp
  have hreg : p.2 = ⊥ ∨ p.2 < p.1 := by
    by_cases h1 : p.1 ≠ ⊥ ∧ p.1 ≠ ⊤
    · by_cases h2 : p.2 = ⊥
      · exact Or.inl h2
      · by_cases h3 : p.2 < p.1
        · exact Or.inr h3
        · exfalso; apply hp; rw [mult, if_pos h1, if_neg h2, if_neg h3]
    · exfalso; apply hp; rw [mult, if_neg h1]
  simp only [Set.mem_setOf_eq]
  show tc p ≠ 0
  intro h0
  apply hp
  rw [hid p hreg, h0]
  simp

theorem t5_offD_fiber_encard {D : EReal × EReal → ℕ∞} (p : EReal × EReal) :
    ({q : offD D | offPt q = p}).encard = D p := by
  classical
  by_cases htop : D p = ⊤
  · 
    have hkltop : ∀ k : ℕ, ((k : ℕ∞) < D p) := by
      intro k
      rw [htop]
      exact lt_of_le_of_ne le_top (ENat.natCast_ne_top k)
    have hinj : Function.Injective (fun k : ℕ => ((⟨(p, k), hkltop k⟩ : offD D))) := by
      intro k₁ k₂ h
      have h' : (p, k₁) = (p, k₂) := congrArg Subtype.val h
      exact congrArg Prod.snd h'
    have hinf : ({q : offD D | offPt q = p}).Infinite := by
      have himg : ((fun k : ℕ => ((⟨(p, k), hkltop k⟩ : offD D))) '' Set.univ).Infinite :=
        Set.Infinite.image (fun k₁ _ k₂ _ h => hinj h) (Set.infinite_univ)
      refine Set.Infinite.mono ?_ himg
      intro q hq
      simp only [Set.mem_image, Set.mem_univ, true_and] at hq
      obtain ⟨k, rfl⟩ := hq
      rfl
    rw [htop]
    exact Set.Infinite.encard_eq hinf
  · 
    have hco : ((D p).toNat : ℕ∞) = D p := ENat.natCast_toNat htop
    have hidx : ∀ q : ↥({q : offD D | offPt q = p} : Set (offD D)),
        q.val.1.2 < (D p).toNat := by
      intro q
      have hp : q.val.1.1 = p := q.property
      have h1 : ((q.val.1.2 : ℕ) : ℕ∞) < D q.val.1.1 := q.val.2
      rw [hp] at h1
      rw [← hco] at h1
      exact ENat.natCast_lt_natCast.mp h1
    have hemb : Function.Injective
        (fun q : ↥({q : offD D | offPt q = p} : Set (offD D)) =>
          (⟨q.val.1.2, hidx q⟩ : Fin ((D p).toNat))) := by
      intro q₁ q₂ h
      have hv : q₁.val.1.2 = q₂.val.1.2 := congrArg Fin.val h
      have hp₁ : (q₁.val.val).1 = p := q₁.property
      have hp₂ : (q₂.val.val).1 = p := q₂.property
      exact Subtype.ext (Subtype.ext (Prod.ext (by rw [hp₁, hp₂]) hv))
    have hfin : ({q : offD D | offPt q = p}).Finite :=
      Set.finite_coe_iff.mpr (Finite.of_injective
        (fun q : ↥({q : offD D | offPt q = p} : Set (offD D)) =>
          (⟨q.val.1.2, hidx q⟩ : Fin ((D p).toNat))) hemb)
    haveI : Fintype ↥({q : offD D | offPt q = p} : Set (offD D)) := hfin.fintype
    have hle1 : Fintype.card ↥({q : offD D | offPt q = p} : Set (offD D))
        ≤ (D p).toNat := by
      have h7 := Fintype.card_le_of_injective
        (fun q : ↥({q : offD D | offPt q = p} : Set (offD D)) =>
          (⟨q.val.1.2, hidx q⟩ : Fin ((D p).toNat))) hemb
      rwa [Fintype.card_fin] at h7
    have hbk : ∀ k : Fin ((D p).toNat), ((k : ℕ) : ℕ∞) < D p := by
      intro k
      have h1 : ((k : ℕ) : ℕ∞) < ((D p).toNat : ℕ∞) := ENat.natCast_lt_natCast.mpr k.isLt
      rw [hco] at h1
      exact h1
    have hemb2 : Function.Injective
        (fun k : Fin ((D p).toNat) =>
          (⟨(⟨(p, (k : ℕ)), hbk k⟩ : offD D), rfl⟩ :
            ↥({q : offD D | offPt q = p} : Set (offD D)))) := by
      intro k₁ k₂ h
      have h1 := congrArg Subtype.val h
      have h2 := congrArg Subtype.val h1
      have h3 : (p, (k₁ : ℕ)) = (p, (k₂ : ℕ)) := h2
      injection h3 with _ hk
      exact Fin.val_injective hk
    have hle2 : (D p).toNat
        ≤ Fintype.card ↥({q : offD D | offPt q = p} : Set (offD D)) := by
      have h7 := Fintype.card_le_of_injective
        (fun k : Fin ((D p).toNat) =>
          (⟨(⟨(p, (k : ℕ)), hbk k⟩ : offD D), rfl⟩ :
            ↥({q : offD D | offPt q = p} : Set (offD D)))) hemb2
      rwa [Fintype.card_fin] at h7
    have hcard : Fintype.card ↥({q : offD D | offPt q = p} : Set (offD D))
        = (D p).toNat := le_antisymm hle1 hle2
    rw [← Set.coe_fintypeCard, hcard]
    exact hco

theorem t5_offD_finite {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) :
    (Set.univ : Set (offD (mult (rankFn stage J)))).Finite := by
  classical
  have hS : {p : EReal × EReal | mult (rankFn stage J) p ≠ 0}.Finite := t2_finDiag hLaw hTame
  have hslice : ∀ p ∈ {p : EReal × EReal | mult (rankFn stage J) p ≠ 0},
      {q : offD (mult (rankFn stage J)) | offPt q = p}.Finite := by
    intro p hp
    have hreg : p.2 = ⊥ ∨ p.2 < p.1 := by
      by_cases h1 : p.1 ≠ ⊥ ∧ p.1 ≠ ⊤
      · by_cases h2 : p.2 = ⊥
        · exact Or.inl h2
        · by_cases h3 : p.2 < p.1
          · exact Or.inr h3
          · exfalso; apply hp; rw [mult, if_pos h1, if_neg h2, if_neg h3]
      · exfalso; apply hp; rw [mult, if_neg h1]
    have htp : mult (rankFn stage J) p ≠ ⊤ := t3_mult_lt_top hLaw hTame p hreg
    have hbound : ∀ q ∈ {q : offD (mult (rankFn stage J)) | offPt q = p},
        q.1.2 < (mult (rankFn stage J) p).toNat := by
      intro q hq
      have hb : ((q.1.2 : ℕ∞) < mult (rankFn stage J) (offPt q)) := q.2
      rw [show offPt q = p from hq] at hb
      have hlt : ((q.1.2 : ℕ∞) < ((mult (rankFn stage J) p).toNat : ℕ∞)) := by
        rw [ENat.natCast_toNat htp]
        exact hb
      exact ENat.natCast_lt_natCast.mp hlt
    have hinj : Set.InjOn (fun q : offD (mult (rankFn stage J)) => q.1.2)
        {q : offD (mult (rankFn stage J)) | offPt q = p} := by
      intro q₁ hq₁ q₂ hq₂ hidx
      have e₁ : offPt q₁ = p := hq₁
      have e₂ : offPt q₂ = p := hq₂
      exact Subtype.ext (Prod.ext (e₁.trans e₂.symm) hidx)
    have hmaps : Set.MapsTo (fun q : offD (mult (rankFn stage J)) => q.1.2)
        {q : offD (mult (rankFn stage J)) | offPt q = p}
        ((Finset.range ((mult (rankFn stage J) p).toNat)) : Set ℕ) := by
      intro q hq
      simp only [Finset.mem_coe, Finset.mem_range]
      exact hbound q hq
    exact Set.Finite.of_injOn hmaps hinj (Finset.finite_toSet _)
  have huniv : (Set.univ : Set (offD (mult (rankFn stage J)))) ⊆
      ⋃ p ∈ {p : EReal × EReal | mult (rankFn stage J) p ≠ 0},
        {q : offD (mult (rankFn stage J)) | offPt q = p} := by
    intro q _
    have hb : ((q.1.2 : ℕ∞) < mult (rankFn stage J) (offPt q)) := q.2
    have hne0 : mult (rankFn stage J) (offPt q) ≠ 0 :=
      pos_iff_ne_zero.mp (lt_of_le_of_lt (ENat.natCast_le_natCast.mpr (Nat.zero_le _)) hb)
    exact Set.mem_biUnion hne0 rfl
  exact (hS.biUnion hslice).subset huniv

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

theorem t5_aliveUp {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {s₀ b : ℝ} {C₀ : comps stage J s₀}
    (hb : birthSup hLaw s₀ C₀ = b) {β : ℝ} (hs₀β : s₀ ≤ β) (hβb : β < b) :
    ∃ A : comps stage J β, birthSup hLaw β A = b ∧ structMap hLaw hs₀β A = C₀ := by
  obtain ⟨s₁, hs₁⟩ := hTame.2.2
  have hBdd : BddAbove (AncSet hLaw s₀ C₀) := by
    refine ⟨s₁, fun u hu => ?_⟩
    obtain ⟨-, C₂, -⟩ := hu
    have hstage : (stage u).Nonempty := by
      obtain ⟨x, hx, -⟩ := C₂.property
      exact ⟨x, hx⟩
    by_contra hle
    push_neg at hle
    exact hstage.ne_empty (hs₁ u hle.le)
  have hne : (AncSet hLaw s₀ C₀).Nonempty := ⟨s₀, le_rfl, C₀, t3_structMap_id hLaw s₀ C₀⟩
  have happrox : ∀ t : ℝ, t < b → ∃ u ∈ AncSet hLaw s₀ C₀, t < u := by
    intro t ht
    by_contra hcon
    push_neg at hcon
    have hle : sSup (AncSet hLaw s₀ C₀) ≤ t := csSup_le hne (fun u hu => hcon u hu)
    have hbr : sSup (AncSet hLaw s₀ C₀) = birthSup hLaw s₀ C₀ := rfl
    rw [hbr] at hle
    linarith
  obtain ⟨u₀, hu₀mem, hu₀lt⟩ := happrox β hβb
  obtain ⟨hu₀, A_u₀, hA_u₀⟩ := hu₀mem
  have hβu₀ : β ≤ u₀ := by linarith
  have hex : ∃ A : comps stage J β, structMap hLaw hs₀β A = C₀ :=
    ⟨structMap hLaw hβu₀ A_u₀, by rw [structMap_comp hLaw hs₀β hβu₀ A_u₀]; exact hA_u₀⟩
  haveI hcompsFin : Finite (comps stage J β) := (hTame.1 β).to_subtype
  obtain ⟨A_wit, hA_wit⟩ := hex
  haveI hPne : Nonempty {A : comps stage J β // structMap hLaw hs₀β A = C₀} :=
    ⟨⟨A_wit, hA_wit⟩⟩
  obtain ⟨Amax, hAmax⟩ := Finite.exists_max
    (fun A : {A : comps stage J β // structMap hLaw hs₀β A = C₀} => birthSup hLaw β A.val)
  refine ⟨Amax.val, ?_, Amax.property⟩
  have hle : birthSup hLaw β Amax.val ≤ b := by
    have h1 := rungB_bSup_descend_ge hLaw hTame hs₀β Amax.val
    rw [Amax.property] at h1
    exact h1.trans_eq hb
  have hge : b ≤ birthSup hLaw β Amax.val := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨u, humem, hut⟩ := happrox (birthSup hLaw β Amax.val) (by linarith)
    obtain ⟨huu, A_u, hA_u⟩ := humem
    have hmβ : β ≤ birthSup hLaw β Amax.val :=
      rungB_level_le_bSup hLaw hTame Amax.val
    have hβu : β ≤ u := by linarith
    have h1 : birthSup hLaw β (structMap hLaw hβu A_u) ≤ birthSup hLaw β Amax.val :=
      hAmax ⟨structMap hLaw hβu A_u, by rw [structMap_comp hLaw hs₀β hβu A_u]; exact hA_u⟩
    have h2 : birthSup hLaw u A_u ≤ birthSup hLaw β (structMap hLaw hβu A_u) :=
      rungB_bSup_descend_ge hLaw hTame hβu A_u
    have h3 : u ≤ birthSup hLaw u A_u :=
      rungB_level_le_bSup hLaw hTame A_u
    linarith
  exact le_antisymm hle hge

def imCls {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop} (t : ℝ) (x : ι)
    (hx : x ∈ stage t) : comps stage J t :=
  ⟨{y | J t x y}, ⟨x, hx, rfl⟩⟩

theorem structMap_imCls {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) {s t : ℝ} (hst : s ≤ t) (x : ι) (hx : x ∈ stage t) :
    structMap hLaw hst (imCls (J := J) t x hx) = imCls s x (hLaw.antitone hst hx) := by
  apply Subtype.ext
  have hr := compRep_spec stage J t (imCls (J := J) t x hx)
  have hJ : J t (compRep stage J t (imCls (J := J) t x hx)) x :=
    (Set.ext_iff.mp hr.2 x).mpr (hLaw.refl hx)
  have hJs : J s (compRep stage J t (imCls (J := J) t x hx)) x := hLaw.compat hst hJ
  ext y
  constructor
  · intro hy
    exact hLaw.trans (hLaw.symm hJs) hy
  · intro hy
    exact hLaw.trans hJs hy

def trS {ι : Type*} (stage : ℝ → Set ι) (α : ℝ) : ℝ → Set ι := fun t => stage (max t α)

def imJ {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop} {α ε : ℝ}
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε)) :
    ℝ → ιX → ιX → Prop :=
  fun t x y => ∃ (hx : x ∈ stageX (max t α)) (hy : y ∈ stageX (max t α)),
    φ (max t α) (le_max_right t α) (imCls (J := JX) (max t α) x hx) =
      φ (max t α) (le_max_right t α) (imCls (J := JX) (max t α) y hy)

theorem imLaw {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY) {α ε : ℝ}
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x)) :
    FiltrationLaw (trS stageX α) (imJ φ) where
  antitone := fun _ _ hst => hLawX.antitone (max_le_max hst le_rfl)
  mem := fun _ _ _ h => ⟨h.1, h.2.1⟩
  refl := fun _ _ hx => ⟨hx, hx, rfl⟩
  symm := fun _ _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩
  trans := fun _ _ _ _ h1 h2 => ⟨h1.1, h2.2.1, h1.2.2.trans h2.2.2⟩
  compat := by
    intro s t hst x y h
    obtain ⟨hx, hy, heq⟩ := h
    have hle : max s α ≤ max t α := max_le_max hst le_rfl
    refine ⟨hLawX.antitone hle hx, hLawX.antitone hle hy, ?_⟩
    have h1 := hSq1 (max s α) (max t α) (le_max_right s α) (le_max_right t α) hle
      (imCls (J := JX) (max t α) x hx)
    have h2 := hSq1 (max s α) (max t α) (le_max_right s α) (le_max_right t α) hle
      (imCls (J := JX) (max t α) y hy)
    rw [structMap_imCls hLawX hle x hx] at h1
    rw [structMap_imCls hLawX hle y hy] at h2
    rw [h1, h2, heq]


noncomputable def imToY {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop} {α ε : ℝ}
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε)) (t : ℝ)
    (C : comps (trS stageX α) (imJ φ) t) : comps stageY JY (max t α - ε) :=
  φ (max t α) (le_max_right t α)
    (imCls (J := JX) (max t α) (compRep (trS stageX α) (imJ φ) t C)
      (compRep_spec (trS stageX α) (imJ φ) t C).1)

theorem imToY_injective {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY) {α ε : ℝ}
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x)) (t : ℝ) :
    Function.Injective (imToY φ t) := by
  intro C₁ C₂ h
  have hL := imLaw hLawX hLawY φ hSq1
  have s₁ := compRep_spec (trS stageX α) (imJ φ) t C₁
  have s₂ := compRep_spec (trS stageX α) (imJ φ) t C₂
  have hJ : imJ φ t (compRep (trS stageX α) (imJ φ) t C₁)
      (compRep (trS stageX α) (imJ φ) t C₂) := ⟨s₁.1, s₂.1, h⟩
  apply Subtype.ext
  rw [← s₁.2, ← s₂.2]
  exact Set.ext fun y =>
    ⟨fun hy => hL.trans (hL.symm hJ) hy, fun hy => hL.trans hJ hy⟩

theorem imToY_of_mem {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop} {α ε : ℝ}
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε)) (t : ℝ)
    (C : comps (trS stageX α) (imJ φ) t) {x : ιX} (hxC : x ∈ C.val) :
    ∃ hx : x ∈ stageX (max t α),
      φ (max t α) (le_max_right t α) (imCls (J := JX) (max t α) x hx) = imToY φ t C := by
  have s := compRep_spec (trS stageX α) (imJ φ) t C
  have hJ : imJ φ t (compRep (trS stageX α) (imJ φ) t C) x :=
    (Set.ext_iff.mp s.2 x).mpr hxC
  obtain ⟨_hx0, hx, hE⟩ := hJ
  exact ⟨hx, hE.symm⟩

theorem imToY_structMap {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY) {α ε : ℝ}
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x))
    {s t : ℝ} (hst : s ≤ t) (C : comps (trS stageX α) (imJ φ) t) :
    imToY φ s (structMap (imLaw hLawX hLawY φ hSq1) hst C) =
      structMap hLawY (show max s α - ε ≤ max t α - ε by
        linarith [max_le_max hst (le_refl α)]) (imToY φ t C) := by
  have hle : max s α ≤ max t α := max_le_max hst le_rfl
  
  set r := compRep (trS stageX α) (imJ φ) t C with hr
  have hrC : r ∈ C.val := by
    have s0 := compRep_spec (trS stageX α) (imJ φ) t C
    exact (Set.ext_iff.mp s0.2 r).mp ((imLaw hLawX hLawY φ hSq1).refl s0.1)
  have hrD : r ∈ (structMap (imLaw hLawX hLawY φ hSq1) hst C).val :=
    (imLaw hLawX hLawY φ hSq1).compat hst
      ((imLaw hLawX hLawY φ hSq1).refl (compRep_spec (trS stageX α) (imJ φ) t C).1)
  obtain ⟨hx1, h1⟩ := imToY_of_mem φ s (structMap (imLaw hLawX hLawY φ hSq1) hst C) hrD
  obtain ⟨hx2, h2⟩ := imToY_of_mem φ t C hrC
  rw [← h1, ← h2]
  have hq := hSq1 (max s α) (max t α) (le_max_right s α) (le_max_right t α) hle
    (imCls (J := JX) (max t α) r hx2)
  rw [structMap_imCls hLawX hle r hx2] at hq
  exact hq


theorem mergeCount_mono {U W : Type*} (g : U → W) {S S' : Set U} (h : S ⊆ S') :
    S.encard + (g '' S').encard ≤ S'.encard + (g '' S).encard := by
  have hsplit : S' = S ∪ (S' \ S) := (Set.union_diff_cancel h).symm
  have himg : g '' S' ⊆ g '' S ∪ g '' (S' \ S) := by
    rw [← Set.image_union, ← hsplit]
  have h1 : (g '' S').encard ≤ (g '' S).encard + (S' \ S).encard :=
    (Set.encard_le_encard himg).trans
      ((Set.encard_union_le _ _).trans (add_le_add le_rfl (Set.encard_image_le g _)))
  have h2 : S'.encard = S.encard + (S' \ S).encard := by
    rw [add_comm]
    exact (Set.encard_diff_add_encard_of_subset h).symm
  calc S.encard + (g '' S').encard
      ≤ S.encard + ((g '' S).encard + (S' \ S).encard) := add_le_add le_rfl h1
    _ = (S.encard + (S' \ S).encard) + (g '' S).encard := by ac_rfl
    _ = S'.encard + (g '' S).encard := by rw [← h2]

theorem mergeCount_transport {U W U' W' : Type*} (g : U → W) (g' : U' → W')
    (e : U → U') (e' : W → W') (he : Function.Injective e) (he' : Function.Injective e')
    (hcomm : ∀ u, g' (e u) = e' (g u)) (S : Set U) :
    (e '' S).encard = S.encard ∧ (g' '' (e '' S)).encard = (g '' S).encard := by
  refine ⟨he.encard_image S, ?_⟩
  have himg : g' '' (e '' S) = e' '' (g '' S) := by
    rw [Set.image_image, Set.image_image]
    exact Set.image_congr fun u _ => hcomm u
  rw [himg]
  exact he'.encard_image _


def meetSet {ι : Type*} (stage : ℝ → Set ι) (J : ℝ → ι → ι → Prop) (t x : ℝ) :
    Set (comps stage J t) :=
  {C | ∃ z ∈ C.val, z ∈ stage x}

theorem comps_eq_imCls {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop} (t : ℝ)
    (C : comps stage J t) :
    C = imCls (J := J) t (compRep stage J t C) (compRep_spec stage J t C).1 :=
  Subtype.ext (compRep_spec stage J t C).2.symm

theorem compRep_mem_structMap {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) {s t : ℝ} (hst : s ≤ t) (C : comps stage J t) :
    compRep stage J t C ∈ (structMap hLaw hst C).val :=
  hLaw.refl (hLaw.antitone hst (compRep_spec stage J t C).1)

theorem imToY_meet {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY) {α ε : ℝ}
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x))
    {t L : ℝ} (htL : t ≤ L) (hαL : α ≤ L) :
    imToY φ t '' meetSet (trS stageX α) (imJ φ) t L ⊆
      meetSet stageY JY (max t α - ε) (L - ε) := by
  rintro _ ⟨C, ⟨z, hzC, hzL⟩, rfl⟩
  have hzL' : z ∈ stageX L := by
    have hm : max L α = L := max_eq_left hαL
    have : z ∈ stageX (max L α) := hzL
    rwa [hm] at this
  obtain ⟨hz, himg⟩ := imToY_of_mem φ t C hzC
  have hle : max t α ≤ L := max_le htL hαL
  
  have hq := hSq1 (max t α) L (le_max_right t α) hαL hle (imCls (J := JX) L z hzL')
  rw [structMap_imCls hLawX hle z hzL'] at hq
  
  set D := φ L hαL (imCls (J := JX) L z hzL') with hD
  refine ⟨compRep stageY JY (L - ε) D, ?_, (compRep_spec stageY JY (L - ε) D).1⟩
  rw [← himg, hq]
  exact compRep_mem_structMap hLawY _ D

theorem comps_eq_imCls_of_mem {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (t : ℝ) (C : comps stage J t) {w : ι} (hw : w ∈ C.val) :
    ∃ hws : w ∈ stage t, C = imCls (J := J) t w hws := by
  have sp := compRep_spec stage J t C
  have hJ : J t (compRep stage J t C) w := (Set.ext_iff.mp sp.2 w).mpr hw
  refine ⟨(hLaw.mem hJ).2, Subtype.ext ?_⟩
  rw [← sp.2]
  exact Set.ext fun y => ⟨fun h => hLaw.trans (hLaw.symm hJ) h, fun h => hLaw.trans hJ h⟩

theorem imToY_meet_psi {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY) {α ε : ℝ}
    (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x))
    (hSq3 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (y : comps stageY JY β),
      φ (β - ε) hβε (ψ β hβ y) =
        structMap hLawY (show (β - ε) - ε ≤ β by linarith) y)
    {t R : ℝ} (htR : t ≤ R) (hαR : α ≤ R) :
    meetSet stageY JY (max t α - ε) (R + ε) ⊆
      imToY φ t '' meetSet (trS stageX α) (imJ φ) t R := by
  rintro y ⟨w, hwy, hwR⟩
  have hβ : α ≤ R + ε := by linarith
  have hβε : α ≤ R + ε - ε := by linarith
  obtain ⟨Xc, hXc⟩ : ∃ Xc : comps stageX JX (R + ε - ε),
      Xc = ψ (R + ε) hβ (imCls (J := JY) (R + ε) w hwR) := ⟨_, rfl⟩
  have hz : compRep stageX JX (R + ε - ε) Xc ∈ stageX (R + ε - ε) :=
    (compRep_spec stageX JX (R + ε - ε) Xc).1
  have hzR : compRep stageX JX (R + ε - ε) Xc ∈ stageX R :=
    hLawX.antitone (show R ≤ R + ε - ε by linarith) hz
  have hle : max t α ≤ R + ε - ε := by
    have h0 := max_le htR hαR
    linarith
  have hzT : compRep stageX JX (R + ε - ε) Xc ∈ stageX (max t α) := hLawX.antitone hle hz
  have hL := imLaw hLawX hLawY φ hSq1
  refine ⟨imCls (J := imJ φ) t (compRep stageX JX (R + ε - ε) Xc) hzT,
    ⟨compRep stageX JX (R + ε - ε) Xc, hL.refl hzT, ?_⟩, ?_⟩
  · show compRep stageX JX (R + ε - ε) Xc ∈ stageX (max R α)
    rw [max_eq_left hαR]
    exact hzR
  · obtain ⟨hz', himg⟩ := imToY_of_mem φ t
      (imCls (J := imJ φ) t (compRep stageX JX (R + ε - ε) Xc) hzT) (hL.refl hzT)
    rw [← himg]
    have h1 := hSq1 (max t α) (R + ε - ε) (le_max_right t α) hβε hle Xc
    have hXr : Xc = imCls (J := JX) (R + ε - ε) (compRep stageX JX (R + ε - ε) Xc) hz :=
      comps_eq_imCls (R + ε - ε) Xc
    rw [hXr, structMap_imCls hLawX hle _ hz] at h1
    rw [h1, ← hXr, hXc, hSq3 (R + ε) hβ hβε, structMap_imCls hLawY _ w hwR,
      structMap_imCls hLawY _ w]
    obtain ⟨hwT, hyw⟩ := comps_eq_imCls_of_mem hLawY (max t α - ε) y hwy
    rw [hyw]

theorem windowCensus_abstract {U W U' W' : Type*} (g : U → W) (g' : U' → W')
    (e : U → U') (e' : W → W') (he : Function.Injective e) (he' : Function.Injective e')
    (hcomm : ∀ u, g' (e u) = e' (g u)) {SL SR : Set U} {TL TR : Set U'}
    (hL : e '' SL ⊆ TL) (hR : TR ⊆ e '' SR) :
    SL.encard + (g '' SR).encard + (g' '' TL).encard + TR.encard ≤
      SR.encard + (g '' SL).encard + TL.encard + (g' '' TR).encard := by
  have hA := mergeCount_mono g' hL
  have hB := mergeCount_mono g' hR
  obtain ⟨hL1, hL2⟩ := mergeCount_transport g g' e e' he he' hcomm SL
  obtain ⟨hR1, hR2⟩ := mergeCount_transport g g' e e' he he' hcomm SR
  rw [hL1, hL2] at hA
  rw [hR1, hR2] at hB
  
  calc SL.encard + (g '' SR).encard + (g' '' TL).encard + TR.encard
      = (SL.encard + (g' '' TL).encard) + (TR.encard + (g '' SR).encard) := by ac_rfl
    _ ≤ (TL.encard + (g '' SL).encard) + (SR.encard + (g' '' TR).encard) :=
        add_le_add hA hB
    _ = SR.encard + (g '' SL).encard + TL.encard + (g' '' TR).encard := by ac_rfl

theorem imWindowCensus {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY) {α ε : ℝ}
    (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x))
    (hSq3 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (y : comps stageY JY β),
      φ (β - ε) hβε (ψ β hβ y) =
        structMap hLawY (show (β - ε) - ε ≤ β by linarith) y)
    {l u L R : ℝ} (hlu : l ≤ u) (huL : u ≤ L) (hαL : α ≤ L) (huR : u ≤ R) (hαR : α ≤ R) :
    let hL := imLaw hLawX hLawY φ hSq1
    let hYle : max l α - ε ≤ max u α - ε := by linarith [max_le_max hlu (le_refl α)]
    (meetSet (trS stageX α) (imJ φ) u L).encard +
        (structMap hL hlu '' meetSet (trS stageX α) (imJ φ) u R).encard +
        (structMap hLawY hYle '' meetSet stageY JY (max u α - ε) (L - ε)).encard +
        (meetSet stageY JY (max u α - ε) (R + ε)).encard ≤
      (meetSet (trS stageX α) (imJ φ) u R).encard +
        (structMap hL hlu '' meetSet (trS stageX α) (imJ φ) u L).encard +
        (meetSet stageY JY (max u α - ε) (L - ε)).encard +
        (structMap hLawY hYle '' meetSet stageY JY (max u α - ε) (R + ε)).encard := by
  intro hL hYle
  exact windowCensus_abstract (structMap hL hlu) (structMap hLawY hYle)
    (imToY φ u) (imToY φ l)
    (imToY_injective hLawX hLawY φ hSq1 u) (imToY_injective hLawX hLawY φ hSq1 l)
    (fun C => (imToY_structMap hLawX hLawY φ hSq1 hlu C).symm)
    (imToY_meet hLawX hLawY φ hSq1 huL hαL)
    (imToY_meet_psi hLawX hLawY hε φ ψ hSq1 hSq3 huR hαR)


theorem imJ_of_JX {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) {α ε : ℝ}
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε)) {t : ℝ} {x y : ιX}
    (h : JX (max t α) x y) : imJ φ t x y := by
  obtain ⟨hx, hy⟩ := hLawX.mem h
  refine ⟨hx, hy, ?_⟩
  have hc : imCls (J := JX) (max t α) x hx = imCls (max t α) y hy := by
    apply Subtype.ext
    exact Set.ext fun z =>
      ⟨fun hz => hLawX.trans (hLawX.symm h) hz, fun hz => hLawX.trans h hz⟩
  rw [hc]

theorem comps_eq_of_rep {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) {t : ℝ} (C D : comps stage J t)
    (h : J t (compRep stage J t C) (compRep stage J t D)) : C = D := by
  have s₁ := compRep_spec stage J t C
  have s₂ := compRep_spec stage J t D
  apply Subtype.ext
  rw [← s₁.2, ← s₂.2]
  exact Set.ext fun y => ⟨fun hy => hLaw.trans (hLaw.symm h) hy, fun hy => hLaw.trans h hy⟩

theorem rep_J_of_structMap_eq {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) {s t : ℝ} (hst : s ≤ t) (C D : comps stage J t)
    (h : structMap hLaw hst C = structMap hLaw hst D) :
    J s (compRep stage J t C) (compRep stage J t D) := by
  have hD := (compRep_spec stage J t D).1
  have hmem : compRep stage J t D ∈ (structMap hLaw hst D).val :=
    hLaw.refl (hLaw.antitone hst hD)
  rw [← h] at hmem
  exact hmem

theorem imFinite {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY) {α ε : ℝ}
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x))
    (hFin : ∀ t, ((fun x => {y | JX t x y}) '' stageX t).Finite) (t : ℝ) :
    ((fun x => {y | imJ φ t x y}) '' trS stageX α t).Finite := by
  have hL := imLaw hLawX hLawY φ hSq1
  refine ((hFin (max t α)).image (fun C => {y | ∃ x' ∈ stageX (max t α),
      {w | JX (max t α) x' w} = C ∧ imJ φ t x' y})).subset ?_
  rintro D ⟨x, hx, rfl⟩
  refine ⟨{w | JX (max t α) x w}, ⟨x, hx, rfl⟩, ?_⟩
  ext y
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨x', hx', hc, hy⟩
    have hxx' : JX (max t α) x x' := by
      have hm : x' ∈ {w | JX (max t α) x' w} := hLawX.refl hx'
      rw [hc] at hm
      exact hm
    exact hL.trans (imJ_of_JX hLawX φ hxx') hy
  · intro hy
    exact ⟨x, hx, rfl, hy⟩

theorem imStep {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY) {α ε : ℝ}
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x))
    {TX TY : Finset ℝ}
    (hTX : ∀ t s : ℝ, t ≤ s → (∀ u ∈ TX, u < t ∨ s < u) →
      (∀ x ∈ stageX t, ∃ y ∈ stageX s, JX t x y) ∧
      (∀ y ∈ stageX s, ∀ y' ∈ stageX s, JX t y y' → JX s y y'))
    (hTY : ∀ t s : ℝ, t ≤ s → (∀ u ∈ TY, u < t ∨ s < u) →
      (∀ x ∈ stageY t, ∃ y ∈ stageY s, JY t x y) ∧
      (∀ y ∈ stageY s, ∀ y' ∈ stageY s, JY t y y' → JY s y y'))
    (t s : ℝ) (hts : t ≤ s)
    (hfree : ∀ u ∈ TX ∪ TY.image (· + ε) ∪ {α}, u < t ∨ s < u) :
    (∀ x ∈ trS stageX α t, ∃ y ∈ trS stageX α s, imJ φ t x y) ∧
    (∀ y ∈ trS stageX α s, ∀ y' ∈ trS stageX α s, imJ φ t y y' → imJ φ s y y') := by
  have hL := imLaw hLawX hLawY φ hSq1
  rcases hfree α (Finset.mem_union_right _ (Finset.mem_singleton_self α)) with hαt | hsα
  swap
  · 
    have hm : max t α = max s α := by
      rw [max_eq_right (by linarith), max_eq_right (by linarith)]
    have key : ∀ y y', imJ φ t y y' → imJ φ s y y' := by
      intro y y' h
      have gen : ∀ (m m' : ℝ), m = m' → ∀ (p : α ≤ m) (q : α ≤ m'),
          (∃ (hx : y ∈ stageX m) (hy : y' ∈ stageX m),
            φ m p (imCls (J := JX) m y hx) = φ m p (imCls (J := JX) m y' hy)) →
          (∃ (hx : y ∈ stageX m') (hy : y' ∈ stageX m'),
            φ m' q (imCls (J := JX) m' y hx) = φ m' q (imCls (J := JX) m' y' hy)) := by
        rintro m _ rfl p q hh
        exact hh
      exact gen _ _ hm _ _ h
    refine ⟨fun x hx => ⟨x, ?_, hL.refl hx⟩, fun y _ y' _ h => key y y' h⟩
    show x ∈ stageX (max s α)
    rw [← hm]; exact hx
  have htm : max t α = t := max_eq_left hαt.le
  have hsm : max s α = s := max_eq_left (by linarith)
  have hle : max t α ≤ max s α := max_le_max hts le_rfl
  refine ⟨fun x hx => ?_, fun y hy y' hy' h => ?_⟩
  · have hX := hTX t s hts (fun u hu => hfree u
      (Finset.mem_union_left _ (Finset.mem_union_left _ hu)))
    have hx' : x ∈ stageX t := by rw [← htm]; exact hx
    obtain ⟨y, hy, hJ⟩ := hX.1 x hx'
    refine ⟨y, ?_, imJ_of_JX hLawX φ ?_⟩
    · show y ∈ stageX (max s α)
      rw [hsm]; exact hy
    · rw [htm]; exact hJ
  obtain ⟨hyt, hy't, hE⟩ := h
  refine ⟨hy, hy', ?_⟩
  have hlY : max t α - ε ≤ max s α - ε := by linarith
  have h1 := hSq1 (max t α) (max s α) (le_max_right t α) (le_max_right s α) hle
    (imCls (J := JX) (max s α) y hy)
  have h2 := hSq1 (max t α) (max s α) (le_max_right t α) (le_max_right s α) hle
    (imCls (J := JX) (max s α) y' hy')
  rw [structMap_imCls hLawX hle y hy] at h1
  rw [structMap_imCls hLawX hle y' hy'] at h2
  have hAB : structMap hLawY hlY
        (φ (max s α) (le_max_right s α) (imCls (J := JX) (max s α) y hy)) =
      structMap hLawY hlY
        (φ (max s α) (le_max_right s α) (imCls (J := JX) (max s α) y' hy')) :=
    h1.symm.trans (hE.trans h2)
  have hJ := rep_J_of_structMap_eq hLawY hlY _ _ hAB
  have hY := hTY (max t α - ε) (max s α - ε) hlY (fun u hu => by
    have hu' := hfree (u + ε)
      (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hu)))
    rw [htm, hsm]
    rcases hu' with hlt | hgt
    · left; linarith
    · right; linarith)
  exact comps_eq_of_rep hLawY _ _
    (hY.2 _ (compRep_spec _ _ _ _).1 _ (compRep_spec _ _ _ _).1 hJ)

theorem imTame {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameX : IsTameModule stageX JX) (hTameY : IsTameModule stageY JY) {α ε : ℝ}
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x)) :
    IsTameModule (trS stageX α) (imJ φ) := by
  obtain ⟨hFinX, ⟨TX, hTX⟩, ⟨s0, hs0⟩⟩ := hTameX
  obtain ⟨_hFinY, ⟨TY, hTY⟩, _hEmpY⟩ := hTameY
  refine ⟨imFinite hLawX hLawY φ hSq1 hFinX, ⟨TX ∪ TY.image (· + ε) ∪ {α}, ?_⟩, ⟨s0, ?_⟩⟩
  · intro t s hts hfree
    exact imStep hLawX hLawY φ hSq1 hTX hTY t s hts hfree
  · intro s hs
    exact hs0 (max s α) (le_trans hs (le_max_left s α))

noncomputable def imOfX {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop} {α ε : ℝ}
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε)) (t : ℝ)
    (C : comps stageX JX (max t α)) : comps (trS stageX α) (imJ φ) t :=
  imCls (J := imJ φ) t (compRep stageX JX (max t α) C) (compRep_spec stageX JX (max t α) C).1

theorem imOfX_eq_of_mem {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) {α ε : ℝ}
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε)) (t : ℝ)
    (C : comps stageX JX (max t α)) (D : comps (trS stageX α) (imJ φ) t) {z : ιX}
    (hzC : z ∈ C.val) (hzD : z ∈ D.val) : imOfX φ t C = D := by
  have sD := compRep_spec (trS stageX α) (imJ φ) t D
  have sC := compRep_spec stageX JX (max t α) C
  have hD : imJ φ t (compRep (trS stageX α) (imJ φ) t D) z := (Set.ext_iff.mp sD.2 z).mpr hzD
  have hC0 : JX (max t α) (compRep stageX JX (max t α) C) z := (Set.ext_iff.mp sC.2 z).mpr hzC
  have hC : imJ φ t (compRep stageX JX (max t α) C) z := imJ_of_JX hLawX φ hC0
  obtain ⟨a, b, e1⟩ := hD
  obtain ⟨c, d, e2⟩ := hC
  apply Subtype.ext
  ext y
  constructor
  · intro hy
    have hy' : imJ φ t (compRep stageX JX (max t α) C) y := hy
    obtain ⟨f, g, e3⟩ := hy'
    have hyD : imJ φ t (compRep (trS stageX α) (imJ φ) t D) y := ⟨a, g, e1.trans (e2.symm.trans e3)⟩
    exact (Set.ext_iff.mp sD.2 y).mp hyD
  · intro hy
    have hy' : imJ φ t (compRep (trS stageX α) (imJ φ) t D) y := (Set.ext_iff.mp sD.2 y).mpr hy
    obtain ⟨f, g, e3⟩ := hy'
    exact (⟨c, g, e2.trans (e1.symm.trans e3)⟩ : imJ φ t (compRep stageX JX (max t α) C) y)

theorem imOfX_meet {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) {α ε : ℝ}
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε)) {t x : ℝ}
    (hαx : α ≤ x) {C : comps stageX JX (max t α)} (hC : C ∈ meetSet stageX JX (max t α) x) :
    imOfX φ t C ∈ meetSet (trS stageX α) (imJ φ) t x := by
  obtain ⟨z, hzC, hzx⟩ := hC
  have sC := compRep_spec stageX JX (max t α) C
  have hC0 : JX (max t α) (compRep stageX JX (max t α) C) z := (Set.ext_iff.mp sC.2 z).mpr hzC
  refine ⟨z, imJ_of_JX hLawX φ hC0, ?_⟩
  show z ∈ stageX (max x α)
  rw [max_eq_left hαx]
  exact hzx

theorem imOfX_meet_surj {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) {α ε : ℝ}
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε)) {t x : ℝ}
    (hαx : α ≤ x) {D : comps (trS stageX α) (imJ φ) t}
    (hD : D ∈ meetSet (trS stageX α) (imJ φ) t x) :
    ∃ C ∈ meetSet stageX JX (max t α) x, imOfX φ t C = D := by
  obtain ⟨z, hzD, hzx0⟩ := hD
  have hzx : z ∈ stageX x := by
    have h0 : z ∈ stageX (max x α) := hzx0
    rwa [max_eq_left hαx] at h0
  have sD := compRep_spec (trS stageX α) (imJ φ) t D
  have hJ : imJ φ t (compRep (trS stageX α) (imJ φ) t D) z := (Set.ext_iff.mp sD.2 z).mpr hzD
  obtain ⟨_h1, hz, _h3⟩ := hJ
  refine ⟨imCls (J := JX) (max t α) z hz, ⟨z, hLawX.refl hz, hzx⟩, ?_⟩
  exact imOfX_eq_of_mem hLawX φ t _ D (hLawX.refl hz) hzD

theorem imOfX_census_le {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) {α ε : ℝ}
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε)) {t x x' : ℝ}
    (hαx : α ≤ x) (hαx' : α ≤ x') :
    ((meetSet (trS stageX α) (imJ φ) t x) \ (meetSet (trS stageX α) (imJ φ) t x')).encard ≤
      ((meetSet stageX JX (max t α) x) \ (meetSet stageX JX (max t α) x')).encard := by
  have hsub : (meetSet (trS stageX α) (imJ φ) t x) \ (meetSet (trS stageX α) (imJ φ) t x') ⊆
      imOfX φ t '' ((meetSet stageX JX (max t α) x) \ (meetSet stageX JX (max t α) x')) := by
    rintro D ⟨hDx, hDx'⟩
    obtain ⟨C, hCx, hCD⟩ := imOfX_meet_surj hLawX φ hαx hDx
    refine ⟨C, ⟨hCx, fun hCx' => hDx' ?_⟩, hCD⟩
    rw [← hCD]
    exact imOfX_meet hLawX φ hαx' hCx'
  exact (Set.encard_le_encard hsub).trans (Set.encard_image_le _ _)

noncomputable def imToX {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop} {α ε : ℝ}
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε)) (t : ℝ)
    (hαt : α + ε ≤ t) (D : comps (trS stageX α) (imJ φ) t) :
    comps stageX JX (max t α - ε - ε) :=
  ψ (max t α - ε) (by have h := le_max_left t α; linarith) (imToY φ t D)

theorem imToX_of_mem {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) {α ε : ℝ} (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq4 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (x : comps stageX JX β),
      ψ (β - ε) hβε (φ β hβ x) = structMap hLawX (show (β - ε) - ε ≤ β by linarith) x)
    {t : ℝ} (hαt : α + ε ≤ t) (D : comps (trS stageX α) (imJ φ) t) {z : ιX}
    (hzD : z ∈ D.val) :
    ∃ hz : z ∈ stageX (max t α - ε - ε), imToX φ ψ t hαt D = imCls (J := JX) _ z hz := by
  obtain ⟨hz, hE⟩ := imToY_of_mem φ t D hzD
  have hle : max t α - ε - ε ≤ max t α := by linarith
  have hαβ : α ≤ max t α - ε := by have h := le_max_left t α; linarith
  refine ⟨hLawX.antitone hle hz, ?_⟩
  show ψ (max t α - ε) _ (imToY φ t D) = _
  rw [← hE]
  exact (hSq4 (max t α) (le_max_right t α) hαβ (imCls (J := JX) (max t α) z hz)).trans
    (structMap_imCls hLawX _ z hz)

theorem imToX_census_le {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) {α ε : ℝ} (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq4 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (x : comps stageX JX β),
      ψ (β - ε) hβε (φ β hβ x) = structMap hLawX (show (β - ε) - ε ≤ β by linarith) x)
    {t x x' : ℝ} (hαt : α + ε ≤ t) (htx : t ≤ x) (hαx : α ≤ x) (hαx' : α ≤ x') :
    ((meetSet stageX JX (max t α - ε - ε) x) \ (meetSet stageX JX (max t α - ε - ε) x')).encard ≤
      ((meetSet (trS stageX α) (imJ φ) t x) \ (meetSet (trS stageX α) (imJ φ) t x')).encard := by
  have hsub : (meetSet stageX JX (max t α - ε - ε) x) \ (meetSet stageX JX (max t α - ε - ε) x')
      ⊆ imToX φ ψ t hαt ''
        ((meetSet (trS stageX α) (imJ φ) t x) \ (meetSet (trS stageX α) (imJ φ) t x')) := by
    rintro C' ⟨⟨z, hzC', hzx⟩, hCx'⟩
    have hz : z ∈ stageX (max t α) := hLawX.antitone (max_le htx hαx) hzx
    have hzD : z ∈ (imCls (J := imJ φ) t z hz : comps (trS stageX α) (imJ φ) t).val :=
      (⟨hz, hz, rfl⟩ : imJ φ t z z)
    obtain ⟨hz2, hE⟩ := imToX_of_mem hLawX hε φ ψ hSq4 hαt _ hzD
    have hCeq : imToX φ ψ t hαt (imCls (J := imJ φ) t z hz) = C' := by
      obtain ⟨hz3, hC3⟩ := comps_eq_imCls_of_mem hLawX _ C' hzC'
      rw [hE, hC3]
    refine ⟨imCls (J := imJ φ) t z hz, ⟨⟨z, hzD, ?_⟩, fun hDx' => hCx' ?_⟩, hCeq⟩
    · show z ∈ stageX (max x α)
      rw [max_eq_left hαx]
      exact hzx
    · rw [← hCeq]
      obtain ⟨w, hwD, hwx'⟩ := hDx'
      obtain ⟨hw2, hE2⟩ := imToX_of_mem hLawX hε φ ψ hSq4 hαt _ hwD
      rw [hE2]
      refine ⟨w, hLawX.refl hw2, ?_⟩
      have h0 : w ∈ stageX (max x' α) := hwx'
      rwa [max_eq_left hαx'] at h0
  exact (Set.encard_le_encard hsub).trans (Set.encard_image_le _ _)


theorem comps_eq_imCls_of_J {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (t : ℝ) (C : comps stage J t) {y : ι}
    (hJ : J t (compRep stage J t C) y) :
    C = imCls (J := J) t y (hLaw.mem hJ).2 := by
  apply Subtype.ext
  rw [← (compRep_spec stage J t C).2]
  exact Set.ext fun z => ⟨fun h => hLaw.trans (hLaw.symm hJ) h, fun h => hLaw.trans hJ h⟩

theorem hcount_const {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) (b : ℝ)
    {t s : ℝ} (hts : t ≤ s) (hfree : ∀ τ ∈ critSet hTame, τ < t ∨ s < τ) :
    ({C : comps stage J t | birthSup hLaw t C = b} : Set (comps stage J t)).encard =
      ({C : comps stage J s | birthSup hLaw s C = b} : Set (comps stage J s)).encard := by
  have himg : structMap hLaw hts '' {C : comps stage J s | birthSup hLaw s C = b} =
      {C : comps stage J t | birthSup hLaw t C = b} := by
    ext C
    constructor
    · rintro ⟨C', hC', rfl⟩
      show birthSup hLaw t (structMap hLaw hts C') = b
      rw [t3_bSupThread hLaw hTame hts hfree rfl]
      exact hC'
    · intro hC
      obtain ⟨y, hys, hJ⟩ :=
        (critSet_spec hTame t s hts hfree).1 _ (compRep_spec stage J t C).1
      have hm : structMap hLaw hts (imCls (J := J) s y hys) = C := by
        rw [comps_eq_imCls_of_J hLaw t C hJ]
        apply Subtype.ext
        have hr := compRep_spec stage J s (imCls (J := J) s y hys)
        have hyr : J s y (compRep stage J s (imCls (J := J) s y hys)) :=
          (Set.ext_iff.mp hr.2 y).mpr (hLaw.refl hys) |> hLaw.symm
        have hyrt : J t y (compRep stage J s (imCls (J := J) s y hys)) :=
          hLaw.compat hts hyr
        exact Set.ext fun z =>
          ⟨fun h => hLaw.trans hyrt h, fun h => hLaw.trans (hLaw.symm hyrt) h⟩
      refine ⟨imCls (J := J) s y hys, ?_, hm⟩
      show birthSup hLaw s (imCls (J := J) s y hys) = b
      rw [← t3_bSupThread hLaw hTame hts hfree hm]
      exact hC
  rw [← himg]
  exact Set.InjOn.encard_image (f := structMap hLaw hts)
    (fun C₁ _ C₂ _ h => t3_crit_inj hLaw hTame hts hfree h)

theorem mult_eq_comb_small {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {b d : ℝ} (hbd : d < b) :
    ∃ δ₁ : ℝ, 0 < δ₁ ∧ δ₁ ≤ (b - d) / 2 ∧ ∀ η ∈ Set.Ioo (0 : ℝ) δ₁,
      mult (rankFn stage J) ((b : EReal), (d : EReal)) = t3_comb stage J b d η := by
  obtain ⟨δ₀, hδ₀, hδ₀le, hstab⟩ := t3_comb_stable hLaw hTame hbd
  refine ⟨δ₀, hδ₀, hδ₀le, fun η hη => ?_⟩
  have hηlim : η < (b - d) / 2 := lt_of_lt_of_le hη.2 hδ₀le
  rw [t3_mult_unfold hLaw hbd]
  apply le_antisymm
  · exact iInf₂_le η ⟨hη.1, hηlim⟩
  · refine le_iInf₂ fun η' hη' => ?_
    rcases le_or_gt η η' with hle | hlt
    · exact t3_comb_ge hLaw hTame hbd hη.1 hle hη'.2
    · exact (hstab η hη η' ⟨hη'.1, lt_trans hlt hη.2⟩).le

theorem hcount_le_up {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {b s₀ β : ℝ}
    (hs₀β : s₀ ≤ β) (hβb : β < b) :
    ({C : comps stage J s₀ | birthSup hLaw s₀ C = b} : Set (comps stage J s₀)).encard ≤
      ({C : comps stage J β | birthSup hLaw β C = b} : Set (comps stage J β)).encard := by
  have hsub : ({C : comps stage J s₀ | birthSup hLaw s₀ C = b} : Set (comps stage J s₀)) ⊆
      structMap hLaw hs₀β '' {A : comps stage J β | birthSup hLaw β A = b} := by
    intro C hC
    obtain ⟨A, hA, hAC⟩ := t5_aliveUp hLaw hTame hC hs₀β hβb
    exact ⟨A, hA, hAC⟩
  exact (Set.encard_le_encard hsub).trans (Set.encard_image_le _ _)

theorem hcount_jump {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {b z : ℝ} (hzb : z < b) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ →
      ({C : comps stage J (z + η) | birthSup hLaw (z + η) C = b} :
          Set (comps stage J (z + η))).encard =
        ({C : comps stage J (z - η) | birthSup hLaw (z - η) C = b} :
          Set (comps stage J (z - η))).encard +
        mult (rankFn stage J) ((b : EReal), (z : EReal)) := by
  obtain ⟨δb, hδb, -, hgb⟩ := t3_gapEx (critSet hTame) one_pos b
  obtain ⟨δz, hδz, -, hgz⟩ := t3_gapEx (critSet hTame) one_pos z
  obtain ⟨δ₁, hδ₁, hδ₁le, hm⟩ := mult_eq_comb_small hLaw hTame hzb
  refine ⟨min (min δb δz) δ₁, lt_min (lt_min hδb hδz) hδ₁, fun η hη0 hηδ => ?_⟩
  have hm1 : min (min δb δz) δ₁ ≤ min δb δz := min_le_left _ _
  have hm2 : min (min δb δz) δ₁ ≤ δ₁ := min_le_right _ _
  have hm3 : min δb δz ≤ δb := min_le_left _ _
  have hm4 : min δb δz ≤ δz := min_le_right _ _
  have hηδ₁ : η < δ₁ := lt_of_lt_of_le hηδ hm2
  have hηlim : η < (b - z) / 2 := lt_of_lt_of_le hηδ₁ hδ₁le
  have hcs := t3_comb_small hLaw hTame (δ₀ := min δb δz) hzb
    ⟨fun τ hτ hne => lt_of_le_of_lt hm3 (hgb τ hτ hne),
      fun τ hτ hne => lt_of_le_of_lt hm4 (hgz τ hτ hne)⟩
    ⟨hη0, lt_of_lt_of_le hηδ hm1⟩ hηlim
  rw [hm η ⟨hη0, hηδ₁⟩, hcs]
  have hle := hcount_le_up hLaw hTame (b := b) (s₀ := z - η) (β := z + η)
    (by linarith) (by linarith)
  exact (add_tsub_cancel_of_le hle).symm


theorem meetSet_iff_img {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) {t s : ℝ} (hts : t ≤ s) (C : comps stage J t) :
    C ∈ meetSet stage J t s ↔ C.val ∈ ((fun x => {y | J t x y}) '' stage s) := by
  constructor
  · rintro ⟨z, hzC, hzs⟩
    obtain ⟨_, hCz⟩ := comps_eq_imCls_of_mem hLaw t C hzC
    exact ⟨z, hzs, by rw [hCz]; rfl⟩
  · rintro ⟨z, hzs, hzeq⟩
    refine ⟨z, ?_, hzs⟩
    rw [← hzeq]
    exact hLaw.refl (hLaw.antitone hts hzs)

theorem bornEq_eq_meetDiff {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {t b : ℝ} (htb : t < b) :
    ∃ θ₀ : ℝ, 0 < θ₀ ∧ ∀ θ : ℝ, 0 < θ → θ < θ₀ →
      ({C : comps stage J t | birthSup hLaw t C = b} : Set (comps stage J t)) =
        meetSet stage J t (b - θ) \ meetSet stage J t (b + θ) := by
  obtain ⟨δ, hδ, -, hgap⟩ := t3_gapEx (critSet hTame) one_pos b
  refine ⟨min δ (b - t), lt_min hδ (by linarith), fun θ hθ hθ₀ => ?_⟩
  have hθδ : θ < δ := lt_of_lt_of_le hθ₀ (min_le_left _ _)
  have hθt : θ < b - t := lt_of_lt_of_le hθ₀ (min_le_right _ _)
  
  have hnear : ∀ C : comps stage J t, |birthSup hLaw t C - b| < δ → birthSup hLaw t C = b := by
    intro C hC
    by_contra hne
    exact absurd (hgap _ (t3_bSup_in_crit hLaw hTame C) hne) (not_lt.mpr hC.le)
  have hgen : ∀ σ : ℝ, |σ| = θ → ∀ C : comps stage J t, b + σ ≠ birthSup hLaw t C := by
    intro σ hσ C hC
    have h1 : birthSup hLaw t C = b := hnear C (by rw [← hC]; simp [hσ, hθδ])
    rw [h1] at hC
    have h2 : σ = 0 := by linarith
    rw [h2, abs_zero] at hσ
    linarith
  have hlo : ∀ C : comps stage J t, b - θ ≠ birthSup hLaw t C := by
    intro C
    have := hgen (-θ) (by rw [abs_neg, abs_of_pos hθ]) C
    rwa [← sub_eq_add_neg] at this
  have hhi : ∀ C : comps stage J t, b + θ ≠ birthSup hLaw t C :=
    hgen θ (abs_of_pos hθ)
  have hmlo := fun C => (meetSet_iff_img hLaw (show t ≤ b - θ by linarith) C).trans
    (t3_meets_birthSup hLaw hTame (show t ≤ b - θ by linarith) hlo C)
  have hmhi := fun C => (meetSet_iff_img hLaw (show t ≤ b + θ by linarith) C).trans
    (t3_meets_birthSup hLaw hTame (show t ≤ b + θ by linarith) hhi C)
  ext C
  simp only [Set.mem_setOf_eq, Set.mem_diff, hmlo C, hmhi C, not_lt]
  constructor
  · intro h
    rw [h]
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    exact hnear C (abs_lt.mpr ⟨by linarith, by linarith⟩)


theorem bornEq_im_le_X {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameX : IsTameModule stageX JX) (hTameY : IsTameModule stageY JY) {α ε : ℝ}
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x))
    {t b : ℝ} (htb : max t α < b) :
    ({C : comps (trS stageX α) (imJ φ) t |
        birthSup (imLaw hLawX hLawY φ hSq1) t C = b} :
        Set (comps (trS stageX α) (imJ φ) t)).encard ≤
      ({C : comps stageX JX (max t α) | birthSup hLawX (max t α) C = b} :
        Set (comps stageX JX (max t α))).encard := by
  have hmt : t ≤ max t α := le_max_left t α
  have hma : α ≤ max t α := le_max_right t α
  obtain ⟨θ₁, hθ₁, h₁⟩ := bornEq_eq_meetDiff (imLaw hLawX hLawY φ hSq1)
    (imTame hLawX hLawY hTameX hTameY φ hSq1) (t := t) (b := b) (by linarith)
  obtain ⟨θ₂, hθ₂, h₂⟩ := bornEq_eq_meetDiff hLawX hTameX (t := max t α) (b := b) htb
  set θ := min (min θ₁ θ₂) ((b - α) / 2) with hθdef
  have hθa : θ ≤ min θ₁ θ₂ := min_le_left _ _
  have hθb : θ ≤ (b - α) / 2 := min_le_right _ _
  have hθ1 : min θ₁ θ₂ ≤ θ₁ := min_le_left _ _
  have hθ2 : min θ₁ θ₂ ≤ θ₂ := min_le_right _ _
  have hθpos : 0 < θ := lt_min (lt_min hθ₁ hθ₂) (by linarith)
  rw [h₁ (θ / 2) (by linarith) (by linarith), h₂ (θ / 2) (by linarith) (by linarith)]
  exact imOfX_census_le hLawX φ (t := t) (x := b - θ / 2) (x' := b + θ / 2)
    (by linarith) (by linarith)

theorem bornEq_X_le_im {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameX : IsTameModule stageX JX) (hTameY : IsTameModule stageY JY) {α ε : ℝ}
    (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x))
    (hSq4 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (x : comps stageX JX β),
      ψ (β - ε) hβε (φ β hβ x) = structMap hLawX (show (β - ε) - ε ≤ β by linarith) x)
    {t b : ℝ} (hαt : α + ε ≤ t) (htb : t < b) :
    ({C : comps stageX JX (max t α - ε - ε) |
        birthSup hLawX (max t α - ε - ε) C = b} :
        Set (comps stageX JX (max t α - ε - ε))).encard ≤
      ({C : comps (trS stageX α) (imJ φ) t |
        birthSup (imLaw hLawX hLawY φ hSq1) t C = b} :
        Set (comps (trS stageX α) (imJ φ) t)).encard := by
  have hm : max t α = t := max_eq_left (by linarith)
  have hlow : max t α - ε - ε < b := by rw [hm]; linarith
  obtain ⟨θ₁, hθ₁, h₁⟩ := bornEq_eq_meetDiff (imLaw hLawX hLawY φ hSq1)
    (imTame hLawX hLawY hTameX hTameY φ hSq1) (t := t) (b := b) htb
  obtain ⟨θ₂, hθ₂, h₂⟩ := bornEq_eq_meetDiff hLawX hTameX (t := max t α - ε - ε) (b := b) hlow
  set θ := min (min θ₁ θ₂) ((b - t) / 2) with hθdef
  have hθa : θ ≤ min θ₁ θ₂ := min_le_left _ _
  have hθb : θ ≤ (b - t) / 2 := min_le_right _ _
  have hθ1 : min θ₁ θ₂ ≤ θ₁ := min_le_left _ _
  have hθ2 : min θ₁ θ₂ ≤ θ₂ := min_le_right _ _
  have hθpos : 0 < θ := lt_min (lt_min hθ₁ hθ₂) (by linarith)
  rw [h₁ (θ / 2) (by linarith) (by linarith), h₂ (θ / 2) (by linarith) (by linarith)]
  exact imToX_census_le hLawX hε φ ψ hSq4 (t := t) (x := b - θ / 2) (x' := b + θ / 2)
    hαt (by linarith) (by linarith) (by linarith)

lemma tel_exists_gap (S : Finset ℝ) (z : ℝ) :
    ∃ η > 0, ∀ y ∈ S, y ≠ z → η < |y - z| := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a S ha ih =>
    obtain ⟨η, hη, hS⟩ := ih
    by_cases haz : a = z
    · refine ⟨η, hη, ?_⟩
      intro y hy hyz
      rcases Finset.mem_insert.mp hy with h | h
      · exact absurd (h.trans haz) hyz
      · exact hS y h hyz
    · have hpos : 0 < |a - z| := abs_pos.mpr (sub_ne_zero.mpr haz)
      refine ⟨min η (|a - z| / 2), lt_min hη (by linarith), ?_⟩
      intro y hy hyz
      have h1 : min η (|a - z| / 2) ≤ η := min_le_left _ _
      have h2 : min η (|a - z| / 2) ≤ |a - z| / 2 := min_le_right _ _
      rcases Finset.mem_insert.mp hy with h | h
      · subst h; linarith
      · have := hS y h hyz; linarith

lemma tel_aux (h : ℝ → ℕ) (m : ℝ → ℕ) (Z : Finset ℝ)
    (hconst : ∀ s t : ℝ, s ≤ t → (∀ z ∈ Z, z < s ∨ t < z) → h s = h t)
    (hjump : ∀ z ∈ Z, ∃ η₀ > 0, ∀ η, 0 < η → η < η₀ → h (z + η) = h (z - η) + m z)
    (D₁ : ℝ) (hD₁ : D₁ ∉ Z) :
    ∀ n : ℕ, ∀ D₂ : ℝ, (Z.filter (fun z => D₁ < z ∧ z < D₂)).card = n → D₁ ≤ D₂ →
      D₂ ∉ Z → h D₂ = h D₁ + ∑ z ∈ Z.filter (fun z => D₁ < z ∧ z < D₂), m z := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro D₂ hcard hD hD₂
  rcases (Z.filter (fun z => D₁ < z ∧ z < D₂)).eq_empty_or_nonempty with hWe | hWne
  · rw [hWe, Finset.sum_empty, add_zero]
    symm
    apply hconst D₁ D₂ hD
    intro z hz
    have hz1 : z ≠ D₁ := fun e => hD₁ (by rw [← e]; exact hz)
    have hz2 : z ≠ D₂ := fun e => hD₂ (by rw [← e]; exact hz)
    have hnot : ¬ (D₁ < z ∧ z < D₂) := by
      intro hh
      have hmem : z ∈ Z.filter (fun z => D₁ < z ∧ z < D₂) := Finset.mem_filter.mpr ⟨hz, hh⟩
      rw [hWe] at hmem; simp at hmem
    rcases lt_or_ge z D₁ with h1 | h1
    · exact Or.inl h1
    · right
      have h1' : D₁ < z := lt_of_le_of_ne h1 (Ne.symm hz1)
      rcases lt_or_ge z D₂ with h2 | h2
      · exact absurd ⟨h1', h2⟩ hnot
      · exact lt_of_le_of_ne h2 (Ne.symm hz2)
  · obtain ⟨zs, hzsW, hle⟩ : ∃ zs ∈ Z.filter (fun z => D₁ < z ∧ z < D₂),
        ∀ y ∈ Z.filter (fun z => D₁ < z ∧ z < D₂), y ≤ zs :=
      ⟨_, Finset.max'_mem _ hWne, fun y hy => Finset.le_max' _ y hy⟩
    have hzsZ : zs ∈ Z := (Finset.mem_filter.mp hzsW).1
    have hzs1 : D₁ < zs := (Finset.mem_filter.mp hzsW).2.1
    have hzs2 : zs < D₂ := (Finset.mem_filter.mp hzsW).2.2
    obtain ⟨η₀, hη₀, hj⟩ := hjump zs hzsZ
    obtain ⟨η₁, hη₁, hgap⟩ := tel_exists_gap (insert D₁ (insert D₂ Z)) zs
    obtain ⟨η, hηa, hηb, hηpos⟩ : ∃ η, η ≤ η₀ / 2 ∧ η ≤ η₁ ∧ 0 < η :=
      ⟨min (η₀ / 2) η₁, min_le_left _ _, min_le_right _ _, lt_min (by linarith) hη₁⟩
    have hη_lt : η < η₀ := by linarith
    have gD₁ : η₁ < zs - D₁ := by
      have hg := hgap D₁ (by simp) (ne_of_lt hzs1)
      rwa [abs_sub_comm, abs_of_pos (by linarith)] at hg
    have gD₂ : η₁ < D₂ - zs := by
      have hg := hgap D₂ (by simp) (ne_of_gt hzs2)
      rwa [abs_of_pos (by linarith)] at hg
    have hA : h (zs + η) = h D₂ := by
      apply hconst (zs + η) D₂ (by linarith)
      intro z hz
      rcases le_or_gt z zs with h1 | h1
      · left; linarith
      · right
        rcases lt_or_ge z D₂ with h2 | h2
        · exfalso
          have hzW : z ∈ Z.filter (fun z => D₁ < z ∧ z < D₂) :=
            Finset.mem_filter.mpr ⟨hz, by linarith, h2⟩
          have := hle z hzW; linarith
        · exact lt_of_le_of_ne h2 (fun e => hD₂ (by rw [e]; exact hz))
    have hB : h (zs + η) = h (zs - η) + m zs := hj η hηpos hη_lt
    have hD₂'Z : zs - η ∉ Z := by
      intro hmem
      have hg := hgap (zs - η) (by simp [hmem]) (ne_of_lt (by linarith))
      rw [show zs - η - zs = -η by ring, abs_neg, abs_of_pos hηpos] at hg
      linarith
    have hfilt : Z.filter (fun z => D₁ < z ∧ z < zs - η) =
        (Z.filter (fun z => D₁ < z ∧ z < D₂)).erase zs := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hz, h1, h2⟩
        exact ⟨ne_of_lt (by linarith), hz, h1, by linarith⟩
      · rintro ⟨hne, hz, h1, h2⟩
        refine ⟨hz, h1, ?_⟩
        have hzle : z ≤ zs := hle z (Finset.mem_filter.mpr ⟨hz, h1, h2⟩)
        have hlt : z < zs := lt_of_le_of_ne hzle hne
        have hg := hgap z (by simp [hz]) hne
        rw [abs_of_neg (by linarith)] at hg
        linarith
    have hcard' : ((Z.filter (fun z => D₁ < z ∧ z < D₂)).erase zs).card < n := by
      rw [Finset.card_erase_of_mem hzsW, ← hcard]
      exact Nat.sub_lt (Finset.card_pos.mpr hWne) one_pos
    have hC := ih _ hcard' (zs - η) (by rw [hfilt]) (by linarith) hD₂'Z
    rw [hfilt] at hC
    rw [← hA, hB, hC, add_assoc, Finset.sum_erase_add _ _ hzsW]

theorem telescope_finite (h : ℝ → ℕ) (m : ℝ → ℕ) (Z : Finset ℝ)
    (hconst : ∀ s t : ℝ, s ≤ t → (∀ z ∈ Z, z < s ∨ t < z) → h s = h t)
    (hjump : ∀ z ∈ Z, ∃ η₀ > 0, ∀ η, 0 < η → η < η₀ → h (z + η) = h (z - η) + m z)
    {D₁ D₂ : ℝ} (hD : D₁ ≤ D₂) (hD₁ : D₁ ∉ Z) (hD₂ : D₂ ∉ Z) :
    h D₂ = h D₁ + ∑ z ∈ Z.filter (fun z => D₁ < z ∧ z < D₂), m z :=
  tel_aux h m Z hconst hjump D₁ hD₁ _ D₂ rfl hD hD₂

theorem cwb_fiber_sum {D : EReal × EReal → ℕ∞} (b : EReal) (W : Finset ℝ) :
    ({a : offD D | (offPt a).1 = b ∧ ∃ z ∈ W, (offPt a).2 = ((z : ℝ) : EReal)}).encard =
      ∑ z ∈ W, D (b, ((z : ℝ) : EReal)) := by
  classical
  induction W using Finset.induction_on with
  | empty => simp
  | insert z W hz ih =>
    have hsplit : ({a : offD D | (offPt a).1 = b ∧ ∃ y ∈ insert z W,
        (offPt a).2 = ((y : ℝ) : EReal)}) =
        {a : offD D | offPt a = (b, ((z : ℝ) : EReal))} ∪
        {a : offD D | (offPt a).1 = b ∧ ∃ y ∈ W, (offPt a).2 = ((y : ℝ) : EReal)} := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_union, Finset.mem_insert, Prod.ext_iff]
      constructor
      · rintro ⟨h1, y, hy | hy, h2⟩
        · subst hy; exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨h1, y, hy, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, y, hy, h2⟩)
        · exact ⟨h1, z, Or.inl rfl, h2⟩
        · exact ⟨h1, y, Or.inr hy, h2⟩
    have hdis : Disjoint {a : offD D | offPt a = (b, ((z : ℝ) : EReal))}
        {a : offD D | (offPt a).1 = b ∧ ∃ y ∈ W, (offPt a).2 = ((y : ℝ) : EReal)} := by
      rw [Set.disjoint_left]
      rintro a ha ⟨-, y, hy, h2⟩
      have ha2 : (offPt a).2 = ((z : ℝ) : EReal) := by rw [Set.mem_setOf_eq.mp ha]
      rw [ha2] at h2
      have hzy : z = y := EReal.coe_injective h2
      exact hz (hzy ▸ hy)
    rw [hsplit, Set.encard_union_eq hdis, t5_offD_fiber_encard, ih, Finset.sum_insert hz]

theorem cwb_cap {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hTame : IsTameModule stage J) {b D₂ : ℝ} (hD₂b : D₂ < b) :
    ∃ c : ℝ, D₂ < c ∧ c < b ∧ c ∉ critSet hTame := by
  obtain ⟨δ₀, hδ0, hδle, hgap⟩ := t3_gapEx (critSet hTame) (sub_pos.mpr hD₂b) b
  refine ⟨b - δ₀ / 2, by linarith, by linarith, ?_⟩
  intro hcm
  have hne : b - δ₀ / 2 ≠ b := by intro e; linarith
  have hg := hgap _ hcm hne
  rw [show b - δ₀ / 2 - b = -(δ₀ / 2) by ring, abs_neg, abs_of_pos (by linarith)] at hg
  linarith

theorem cwb_copies_eq {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {b D₁ D₂ : ℝ}
    (hD₂b : D₂ < b) (W : Finset ℝ)
    (hW : ∀ z, z ∈ W ↔ z ∈ critSet hTame ∧ D₁ < z ∧ z < D₂) :
    {a : offD (mult (rankFn stage J)) | (offPt a).1 = ((b : ℝ) : EReal) ∧
        ((D₁ : ℝ) : EReal) < (offPt a).2 ∧ (offPt a).2 < ((D₂ : ℝ) : EReal)} =
    {a : offD (mult (rankFn stage J)) | (offPt a).1 = ((b : ℝ) : EReal) ∧
        ∃ z ∈ W, (offPt a).2 = ((z : ℝ) : EReal)} := by
  ext a
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hez : (((offPt a).2.toReal : ℝ) : EReal) = (offPt a).2 :=
      EReal.coe_toReal (ne_top_of_lt h3) (ne_bot_of_gt h2)
    refine ⟨h1, (offPt a).2.toReal, ?_, hez.symm⟩
    rw [← hez] at h2 h3
    have hz1 := EReal.coe_lt_coe_iff.mp h2
    have hz2 := EReal.coe_lt_coe_iff.mp h3
    refine (hW _).mpr ⟨?_, hz1, hz2⟩
    by_contra hzn
    have h0 := t3_death_pin hLaw hTame (b := b) (d := (offPt a).2.toReal) (by linarith)
      (fun hm => hzn (Finset.mem_coe.mp hm))
    have hpt : offPt a = (((b : ℝ) : EReal), (((offPt a).2.toReal : ℝ) : EReal)) :=
      Prod.ext h1 hez.symm
    have hlt : ((a.1.2 : ℕ) : ℕ∞) < mult (rankFn stage J) (offPt a) := a.2
    rw [hpt, h0] at hlt
    exact absurd hlt (not_lt.mpr zero_le)
  · rintro ⟨h1, z, hz, h2⟩
    obtain ⟨-, hz1, hz2⟩ := (hW z).mp hz
    exact ⟨h1, by rw [h2]; exact EReal.coe_lt_coe_iff.mpr hz1,
      by rw [h2]; exact EReal.coe_lt_coe_iff.mpr hz2⟩

theorem cwb_hconst {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {b c : ℝ} (hcb : c < b)
    (hcn : c ∉ critSet hTame) (E : ℝ → ℕ∞)
    (hE : ∀ t, E t = ({C : comps stage J t | birthSup hLaw t C = b} :
      Set (comps stage J t)).encard) (h : ℝ → ℕ) (hh : ∀ t, h t = (E (min t c)).toNat) :
    ∀ s t : ℝ, s ≤ t → (∀ z ∈ (critSet hTame).filter (· < c), z < s ∨ t < z) →
      h s = h t := by
  intro s t hst hZ
  have hmin : min s c ≤ min t c := min_le_min_right c hst
  have hfree : ∀ τ ∈ critSet hTame, τ < min s c ∨ min t c < τ := by
    intro τ hτ
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hm1 : min t c ≤ c := min_le_right _ _
    have hm2 : min t c ≤ t := min_le_left _ _
    have hτc : τ < c := lt_of_le_of_ne (h2.trans hm1) (fun e => hcn (e ▸ hτ))
    have hτZ : τ ∈ (critSet hTame).filter (· < c) := Finset.mem_filter.mpr ⟨hτ, hτc⟩
    have hsτ : s ≤ τ := by
      rcases le_total s c with hsc | hsc
      · rw [min_eq_left hsc] at h1; exact h1
      · rw [min_eq_right hsc] at h1; linarith
    rcases hZ τ hτZ with h3 | h3 <;> linarith
  rw [hh, hh, hE, hE, hcount_const hLaw hTame b hmin hfree]

theorem cwb_hjump {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {b c : ℝ} (hcb : c < b)
    (E : ℝ → ℕ∞)
    (hE : ∀ t, E t = ({C : comps stage J t | birthSup hLaw t C = b} :
      Set (comps stage J t)).encard) (h : ℝ → ℕ) (hh : ∀ t, h t = (E (min t c)).toNat)
    (m : ℝ → ℕ) (hm : ∀ z, m z = (mult (rankFn stage J) ((b : EReal), (z : EReal))).toNat) :
    ∀ z ∈ (critSet hTame).filter (· < c), ∃ η₀ > 0, ∀ η, 0 < η → η < η₀ →
      h (z + η) = h (z - η) + m z := by
  intro z hz
  have hzc : z < c := (Finset.mem_filter.mp hz).2
  obtain ⟨η₀, hη0, hj⟩ := hcount_jump hLaw hTame (b := b) (z := z) (by linarith)
  refine ⟨min η₀ (c - z), lt_min hη0 (by linarith), ?_⟩
  intro η hη hηlt
  have hl1 : min η₀ (c - z) ≤ η₀ := min_le_left _ _
  have hl2 : min η₀ (c - z) ≤ c - z := min_le_right _ _
  have hp : min (z + η) c = z + η := min_eq_left (by linarith)
  have hq : min (z - η) c = z - η := min_eq_left (by linarith)
  have key := hj η hη (by linarith)
  have hmtop : mult (rankFn stage J) ((b : EReal), (z : EReal)) ≠ ⊤ :=
    t3_mult_lt_top hLaw hTame _ (Or.inr (EReal.coe_lt_coe_iff.mpr (by linarith)))
  have hfin : ∀ t, E t ≠ ⊤ := by
    intro t
    rw [hE]
    haveI : Finite (comps stage J t) := (hTame.1 t).to_subtype
    exact (Set.toFinite _).encard_lt_top.ne
  rw [← hE, ← hE] at key
  rw [hh, hh, hm, hp, hq, key, ENat.toNat_add (hfin _) hmtop]

theorem copies_birth_window {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {b D₁ D₂ : ℝ}
    (hD : D₁ ≤ D₂) (hD₂b : D₂ < b)
    (hD₁ : D₁ ∉ (critSet hTame : Set ℝ)) (hD₂ : D₂ ∉ (critSet hTame : Set ℝ)) :
    ({a : offD (mult (rankFn stage J)) | (offPt a).1 = ((b : ℝ) : EReal) ∧
        ((D₁ : ℝ) : EReal) < (offPt a).2 ∧ (offPt a).2 < ((D₂ : ℝ) : EReal)}).encard +
      ({C : comps stage J D₁ | birthSup hLaw D₁ C = b} : Set (comps stage J D₁)).encard =
    ({C : comps stage J D₂ | birthSup hLaw D₂ C = b} : Set (comps stage J D₂)).encard := by
  classical
  obtain ⟨c, hD₂c, hcb, hcn⟩ := cwb_cap hTame hD₂b
  obtain ⟨E, hE⟩ : ∃ E : ℝ → ℕ∞, ∀ t, E t = ({C : comps stage J t | birthSup hLaw t C = b} :
      Set (comps stage J t)).encard := ⟨_, fun _ => rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : ℝ → ℕ, ∀ t, h t = (E (min t c)).toNat := ⟨_, fun _ => rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : ℝ → ℕ, ∀ z, m z =
      (mult (rankFn stage J) ((b : EReal), (z : EReal))).toNat := ⟨_, fun _ => rfl⟩
  have hfin : ∀ t, E t ≠ ⊤ := by
    intro t
    rw [hE]
    haveI : Finite (comps stage J t) := (hTame.1 t).to_subtype
    exact (Set.toFinite _).encard_lt_top.ne
  have hD₁Z : D₁ ∉ (critSet hTame).filter (· < c) :=
    fun hz => hD₁ (Finset.mem_coe.mpr (Finset.mem_filter.mp hz).1)
  have hD₂Z : D₂ ∉ (critSet hTame).filter (· < c) :=
    fun hz => hD₂ (Finset.mem_coe.mpr (Finset.mem_filter.mp hz).1)
  have ht := telescope_finite h m _ (cwb_hconst hLaw hTame hcb hcn E hE h hh)
    (cwb_hjump hLaw hTame hcb E hE h hh m hm) hD hD₁Z hD₂Z
  rw [hh, hh, min_eq_left hD₂c.le, min_eq_left (hD.trans hD₂c.le)] at ht
  set W := ((critSet hTame).filter (· < c)).filter (fun z => D₁ < z ∧ z < D₂) with hWdef
  have hW : ∀ z, z ∈ W ↔ z ∈ critSet hTame ∧ D₁ < z ∧ z < D₂ := by
    intro z
    simp only [hWdef, Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, -⟩, h2, h3⟩; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, by linarith⟩, h2, h3⟩
  rw [cwb_copies_eq hLaw hTame hD₂b W hW, cwb_fiber_sum, ← hE, ← hE,
    ← ENat.coe_toNat (hfin D₂), ← ENat.coe_toNat (hfin D₁), ht, Nat.cast_add, Nat.cast_sum,
    add_comm]
  congr 1
  refine Finset.sum_congr rfl (fun z hz => ?_)
  obtain ⟨-, -, hz2⟩ := (hW z).mp hz
  rw [hm, ENat.coe_toNat (t3_mult_lt_top hLaw hTame _
    (Or.inr (EReal.coe_lt_coe_iff.mpr (by linarith))))]

private theorem exists_clusterChop : ∀ (k : ℕ) (B : Finset ℝ), B.card ≤ k → B.Nonempty →
    ∀ (ε : ℝ), 0 ≤ ε →
    ∃ c ∈ B, (∀ w ∈ B, c ≤ w) ∧ ∃ d ∈ B,
      (∀ t : ℝ, c - ε ≤ t → t ≤ d + ε → ∃ w ∈ B, c ≤ w ∧ w ≤ d ∧ |w - t| ≤ ε) ∧
      (∀ v ∈ B, d < v → d + 2 * ε < v) ∧ c ≤ d := by
  intro k
  induction k with
  | zero =>
    intro B hcard hB ε hε
    have h0 : B = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [h0] at hB
    exact absurd hB (by simp)
  | succ k ih =>
    intro B hcard hB ε hε
    have hmB : B.max' hB ∈ B := Finset.max'_mem _ hB
    have hle : ∀ v ∈ B, v ≤ B.max' hB := fun v hv =>
      (Finset.isGreatest_max' B hB).2 (Finset.mem_coe.mpr hv)
    have hcard' : (B.erase (B.max' hB)).card ≤ k := by
      have h1 := Finset.card_erase_add_one hmB
      omega
    rcases (B.erase (B.max' hB)).eq_empty_or_nonempty with hB'e | hB'ne
    · 
      have hsingle : ∀ v ∈ B, v = B.max' hB := by
        intro v hv
        by_contra hne
        have hvm : v ∈ B.erase (B.max' hB) := Finset.mem_erase.mpr ⟨hne, hv⟩
        rw [hB'e] at hvm
        exact absurd hvm (by simp)
      refine ⟨B.max' hB, hmB, fun w hw => le_of_eq (hsingle w hw).symm, B.max' hB, hmB,
        ?_, ?_, le_refl _⟩
      · intro t ht1 ht2
        exact ⟨B.max' hB, hmB, le_refl _, le_refl _, abs_le.mpr ⟨by linarith, by linarith⟩⟩
      · intro v hv hvlt
        rw [hsingle v hv] at hvlt
        exact absurd hvlt (lt_irrefl _)
    · 
      obtain ⟨c', hc'B', hc'min, d', hd'B', hnet', hfar', hc'd'⟩ :=
        ih (B.erase (B.max' hB)) hcard' hB'ne ε hε
      have hc'B : c' ∈ B := Finset.mem_of_mem_erase hc'B'
      have hd'B : d' ∈ B := Finset.mem_of_mem_erase hd'B'
      have hcmB : ∀ w ∈ B, c' ≤ w := by
        intro w hw
        by_cases hw' : w = B.max' hB
        · rw [hw']; exact hle c' hc'B
        · exact hc'min w (Finset.mem_erase.mpr ⟨hw', hw⟩)
      by_cases hA : ∀ v ∈ B.erase (B.max' hB), v ≤ d'
      · by_cases hsw : B.max' hB ≤ d' + 2 * ε
        · 
          refine ⟨c', hc'B, hcmB, B.max' hB, hmB, ?_, ?_, hle c' hc'B⟩
          · intro t ht1 ht2
            by_cases ht : t ≤ d' + ε
            · obtain ⟨w, hwB', hcw, hwd, hwabs⟩ := hnet' t ht1 ht
              exact ⟨w, Finset.mem_of_mem_erase hwB', hcw, hwd.trans (hle d' hd'B), hwabs⟩
            · have ht' : d' + ε < t := not_le.mp ht
              exact ⟨B.max' hB, hmB, hle c' hc'B, le_refl _,
                abs_le.mpr ⟨by linarith, by linarith⟩⟩
          · intro v hv hvlt
            exact absurd (hle v hv) (not_le.mpr hvlt)
        · 
          have hmaxlt : d' + 2 * ε < B.max' hB := not_le.mp hsw
          refine ⟨c', hc'B, hcmB, d', hd'B, ?_, ?_, hc'd'⟩
          · intro t ht1 ht2
            obtain ⟨w, hwB', hcw, hwd, hwabs⟩ := hnet' t ht1 ht2
            exact ⟨w, Finset.mem_of_mem_erase hwB', hcw, hwd, hwabs⟩
          · intro v hv hvlt
            by_cases hvm : v = B.max' hB
            · rw [hvm]; exact hmaxlt
            · exact absurd (hA v (Finset.mem_erase.mpr ⟨hvm, hv⟩)) (not_le.mpr hvlt)
      · 
        obtain ⟨v₀, hv₀, hv₀lt⟩ : ∃ v ∈ B.erase (B.max' hB), d' < v := by
          by_contra hcon
          have hcon' : ∀ v ∈ B.erase (B.max' hB), v ≤ d' := fun v hv =>
            le_of_not_gt fun hvlt => hcon ⟨v, hv, hvlt⟩
          exact hA hcon'
        refine ⟨c', hc'B, hcmB, d', hd'B, ?_, ?_, hc'd'⟩
        · intro t ht1 ht2
          obtain ⟨w, hwB', hcw, hwd, hwabs⟩ := hnet' t ht1 ht2
          exact ⟨w, Finset.mem_of_mem_erase hwB', hcw, hwd, hwabs⟩
        · intro v hv hvlt
          by_cases hvm : v = B.max' hB
          · rw [hvm]
            exact (hfar' v₀ hv₀ hv₀lt).trans_le (hle v₀ (Finset.mem_of_mem_erase hv₀))
          · exact hfar' v (Finset.mem_erase.mpr ⟨hvm, hv⟩) hvlt

theorem t5_cluster_chop {X Q : Type}
    (ε : ℝ) (hε : 0 ≤ ε) (bth : X → ℝ) (s : Set X) (hs : s.Finite)
    (fib : X → Set Q) (supply : ℝ → ℝ → Set Q)
    (hwin : ∀ L R : ℝ, L ≤ R → {x : X | L ≤ bth x ∧ bth x ≤ R}.encard ≤ (supply L R).encard)
    (hcone : ∀ (L R : ℝ), L ≤ R → ∀ x ∈ s, L ≤ bth x → bth x ≤ R → fib x ⊆ supply L R)
    (hnet : ∀ L R : ℝ, L ≤ R →
        (∀ t : ℝ, L - ε ≤ t → t ≤ R + ε →
          ∃ x ∈ s, L ≤ bth x ∧ bth x ≤ R ∧ |bth x - t| ≤ ε) →
        supply L R ⊆ ⋃ x ∈ {x ∈ s | L ≤ bth x ∧ bth x ≤ R}, fib x)
    (hdisj : ∀ x ∈ s, ∀ x' ∈ s, ∀ t : ℝ, bth x ≤ t → t + 2 * ε < bth x' → fib x ∩ fib x' = ∅) :
    s.encard ≤ (⋃ x ∈ s, fib x).encard := by
  rcases s.eq_empty_or_nonempty with h | ⟨x₀, hx₀⟩
  · subst h
    exact (le_of_eq Set.encard_empty).trans zero_le
  · obtain ⟨m, hm, hmin⟩ := s.exists_min_image bth hs ⟨x₀, hx₀⟩
    have main : ∀ (n : ℕ) (T : Set X) (u : ℝ), T.encard ≤ n → T = {x ∈ s | u < bth x} →
        T.encard ≤ (⋃ x ∈ T, fib x).encard := by
      intro n
      induction n with
      | zero =>
        intro T u hTn hTeq
        rcases T.eq_empty_or_nonempty with hT | ⟨x, hx⟩
        · subst hT
          exact (le_of_eq Set.encard_empty).trans zero_le
        · rw [Nat.cast_zero] at hTn
          exact absurd hTn (not_le.mpr (Set.encard_pos.mpr ⟨x, hx⟩))
      | succ k ih =>
        intro T u hTn hTeq
        rcases T.eq_empty_or_nonempty with hT | ⟨x₀, hx₀⟩
        · subst hT
          exact (le_of_eq Set.encard_empty).trans zero_le
        · have hTsub : T ⊆ s := by
            intro x hx
            rw [hTeq] at hx
            exact hx.1
          have hTfin : T.Finite := hs.subset hTsub
          have hBne : (hTfin.toFinset.image bth).Nonempty :=
            ⟨bth x₀, Finset.mem_image_of_mem bth ((Set.Finite.mem_toFinset hTfin).mpr hx₀)⟩
          obtain ⟨c, hcB, hcmin, d, hdB, hchnet, hfar, hcd⟩ :=
            exists_clusterChop (hTfin.toFinset.image bth).card
              (hTfin.toFinset.image bth) (le_refl _) hBne ε hε
          have hBmem : ∀ x ∈ T, bth x ∈ hTfin.toFinset.image bth :=
            fun _ hx => Finset.mem_image_of_mem bth ((Set.Finite.mem_toFinset hTfin).mpr hx)
          have hmem : ∀ w ∈ hTfin.toFinset.image bth, ∃ x ∈ T, bth x = w := by
            intro w hw
            obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
            exact ⟨x, (Set.Finite.mem_toFinset hTfin).mp hx, rfl⟩
          obtain ⟨x_c, hx_c, hc_eq⟩ := hmem c hcB
          obtain ⟨x_d, hx_d, hd_eq⟩ := hmem d hdB
          have hu_c : u < c := by
            have hx' := hx_c
            rw [hTeq] at hx'
            have h2 := hx'.2
            rwa [hc_eq] at h2
          have hsplitC : T = {x ∈ T | bth x ≤ d} ∪ {x ∈ T | d < bth x} := by
            ext x
            constructor
            · intro hx
              rcases lt_or_ge d (bth x) with h1 | h1
              · exact Or.inr ⟨hx, h1⟩
              · exact Or.inl ⟨hx, h1⟩
            · intro hx
              rcases hx with hx | hx
              · exact hx.1
              · exact hx.1
          have hdisjCT : Disjoint {x ∈ T | bth x ≤ d} {x ∈ T | d < bth x} := by
            rw [Set.disjoint_iff]
            intro x hx1
            exact absurd hx1.2.2 (by have := hx1.1.2; linarith)
          have hcard_split : T.encard = {x ∈ T | bth x ≤ d}.encard +
              {x ∈ T | d < bth x}.encard :=
            (congrArg Set.encard hsplitC).trans (Set.encard_union_eq hdisjCT)
          have hCne : {x ∈ T | bth x ≤ d}.Nonempty := ⟨x_d, hx_d, le_of_eq hd_eq⟩
          have hsliceeq : {x ∈ s | c ≤ bth x ∧ bth x ≤ d} = {x ∈ T | bth x ≤ d} := by
            ext x
            constructor
            · intro hx
              have hut : u < bth x := by
                have := hu_c
                have := hx.2.1
                linarith
              refine ⟨?_, hx.2.2⟩
              rw [hTeq]
              exact ⟨hx.1, hut⟩
            · intro hx
              exact ⟨hTsub hx.1, hcmin (bth x) (hBmem x hx.1), hx.2⟩
          have hnetCD : supply c d ⊆ ⋃ x ∈ {x ∈ T | bth x ≤ d}, fib x := by
            have hprem : ∀ t : ℝ, c - ε ≤ t → t ≤ d + ε →
                ∃ x ∈ s, c ≤ bth x ∧ bth x ≤ d ∧ |bth x - t| ≤ ε := by
              intro t ht1 ht2
              obtain ⟨w, hwB, hcw, hwd, hwabs⟩ := hchnet t ht1 ht2
              obtain ⟨x, hx, rfl⟩ := hmem w hwB
              exact ⟨x, hTsub hx, hcw, hwd, hwabs⟩
            have hnet1 := hnet c d hcd hprem
            rwa [hsliceeq] at hnet1
          have hCbound : {x ∈ T | bth x ≤ d}.encard ≤
              (⋃ x ∈ {x ∈ T | bth x ≤ d}, fib x).encard := by
            calc {x ∈ T | bth x ≤ d}.encard ≤ {x : X | c ≤ bth x ∧ bth x ≤ d}.encard :=
                  Set.encard_le_encard (fun x hx => ⟨hcmin (bth x) (hBmem x hx.1), hx.2⟩)
              _ ≤ (supply c d).encard := hwin c d hcd
              _ ≤ (⋃ x ∈ {x ∈ T | bth x ≤ d}, fib x).encard := Set.encard_le_encard hnetCD
          have hfiDisj : Disjoint (⋃ x ∈ {x ∈ T | bth x ≤ d}, fib x)
              (⋃ x ∈ {x ∈ T | d < bth x}, fib x) := by
            rw [Set.disjoint_iff]
            intro q hq1
            obtain ⟨hq1, hq2⟩ := hq1
            obtain ⟨x, hx, hqf⟩ := Set.mem_iUnion₂.mp hq1
            obtain ⟨x', hx', hqf'⟩ := Set.mem_iUnion₂.mp hq2
            have hcross : fib x ∩ fib x' = ∅ :=
              hdisj x (hTsub hx.1) x' (hTsub hx'.1) d hx.2
                (hfar (bth x') (hBmem x' hx'.1) hx'.2)
            have hqmem : q ∈ fib x ∩ fib x' := ⟨hqf, hqf'⟩
            rw [hcross] at hqmem
            exact absurd hqmem (by simp)
          have hT'eq : {x ∈ T | d < bth x} = {x ∈ s | d + 2 * ε < bth x} := by
            ext x
            constructor
            · intro hx
              exact ⟨hTsub hx.1, hfar (bth x) (hBmem x hx.1) hx.2⟩
            · intro hx
              have hut : u < bth x := by
                have := hu_c
                have := hcd
                have := hx.2
                linarith
              refine ⟨?_, ?_⟩
              · rw [hTeq]
                exact ⟨hx.1, hut⟩
              · have := hx.2
                linarith
          have hCfin : {x ∈ T | bth x ≤ d}.Finite := hTfin.subset fun x hx => hx.1
          have hT'fin : {x ∈ T | d < bth x}.Finite := hTfin.subset fun x hx => hx.1
          have hT'card : {x ∈ T | d < bth x}.encard ≤ (k : ℕ∞) := by
            have e2 : {x ∈ T | bth x ≤ d}.encard = (hCfin.toFinset.card : ℕ∞) :=
              hCfin.encard_eq_coe_toFinset_card
            have e3 : {x ∈ T | d < bth x}.encard = (hT'fin.toFinset.card : ℕ∞) :=
              hT'fin.encard_eq_coe_toFinset_card
            have hTn2 := hTn
            rw [hcard_split, e2, e3, ← ENat.natCast_add] at hTn2
            have hN := ENat.natCast_le_natCast.mp hTn2
            have hCpos : 1 ≤ hCfin.toFinset.card :=
              Finset.one_le_card.mpr (hCfin.toFinset_nonempty.mpr hCne)
            rw [e3, ENat.natCast_le_natCast]
            omega
          have hIH := ih {x ∈ T | d < bth x} (d + 2 * ε) hT'card hT'eq
          have hlast : (⋃ x ∈ {x ∈ T | bth x ≤ d}, fib x) ∪
              (⋃ x ∈ {x ∈ T | d < bth x}, fib x) = ⋃ x ∈ T, fib x := by
            rw [← Set.biUnion_union, ← hsplitC]
          calc T.encard = {x ∈ T | bth x ≤ d}.encard + {x ∈ T | d < bth x}.encard :=
                hcard_split
            _ ≤ (⋃ x ∈ {x ∈ T | bth x ≤ d}, fib x).encard +
                (⋃ x ∈ {x ∈ T | d < bth x}, fib x).encard :=
                add_le_add hCbound hIH
            _ = ((⋃ x ∈ {x ∈ T | bth x ≤ d}, fib x) ∪
                (⋃ x ∈ {x ∈ T | d < bth x}, fib x)).encard :=
                (Set.encard_union_eq hfiDisj).symm
            _ = (⋃ x ∈ T, fib x).encard := by rw [hlast]
    have hcard : s.encard ≤ (hs.toFinset.card : ℕ∞) :=
      le_of_eq hs.encard_eq_coe_toFinset_card
    have hs' : s = {x ∈ s | bth m - 1 < bth x} := by
      ext x
      constructor
      · intro hx
        exact ⟨hx, by have := hmin x hx; linarith⟩
      · exact fun hx => hx.1
    exact main _ s (bth m - 1) hcard hs'


set_option maxHeartbeats 8000000 in

private theorem t5_hallChoice {S T : Type} (G : S → Set T)
    (hfin : ∀ a, (G a).Finite)
    (hhall : ∀ s : Set S, s.Finite → s.encard ≤ (⋃ x ∈ s, G x).encard) :
    ∃ f : S → T, Function.Injective f ∧ ∀ a, f a ∈ G a := by
  classical
  have hballs : ∀ s : Finset S,
      s.card ≤ (s.biUnion (fun a => (hfin a).toFinset)).card := by
    intro s
    have hsub : (⋃ x ∈ (↑s : Set S), G x) ⊆
        (↑(s.biUnion (fun a => (hfin a).toFinset)) : Set T) := by
      intro y hy
      obtain ⟨x, hx, hgy⟩ := Set.mem_iUnion₂.1 hy
      exact Finset.mem_coe.2
        (Finset.mem_biUnion.2 ⟨x, Finset.mem_coe.1 hx,
          (Set.Finite.mem_toFinset (hfin x)).2 hgy⟩)
    have hball : (↑(s.card) : ℕ∞) ≤
        (↑((s.biUnion (fun a => (hfin a).toFinset)).card) : ℕ∞) :=
      calc (↑(s.card) : ℕ∞) = (↑s : Set S).encard :=
              (Set.encard_coe_eq_coe_finsetCard s).symm
        _ ≤ (⋃ x ∈ (↑s : Set S), G x).encard := hhall (↑s : Set S) s.finite_toSet
        _ ≤ (↑(s.biUnion (fun a => (hfin a).toFinset)) : Set T).encard :=
            Set.encard_le_encard hsub
        _ = (↑((s.biUnion (fun a => (hfin a).toFinset)).card) : ℕ∞) :=
            Set.encard_coe_eq_coe_finsetCard _
    exact ENat.natCast_le_natCast.1 hball
  obtain ⟨f, hfinj, hfmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective
      (t := fun a => (hfin a).toFinset)).mp hballs
  exact ⟨f, hfinj, fun a => (Set.Finite.mem_toFinset (hfin a)).mp (hfmem a)⟩












theorem copies_birth_closed_open {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {b A B : ℝ}
    (hAB : A ≤ B) (hBb : B < b) :
    ∃ θ₀ : ℝ, 0 < θ₀ ∧ ∀ θ : ℝ, 0 < θ → θ < θ₀ →
      A - θ ∉ (critSet hTame : Set ℝ) ∧ B + θ ∉ (critSet hTame : Set ℝ) ∧ B + θ < b ∧
      {a : offD (mult (rankFn stage J)) | (offPt a).1 = ((b : ℝ) : EReal) ∧
          ((A : ℝ) : EReal) ≤ (offPt a).2 ∧ (offPt a).2 ≤ ((B : ℝ) : EReal)} =
      {a : offD (mult (rankFn stage J)) | (offPt a).1 = ((b : ℝ) : EReal) ∧
          ((A - θ : ℝ) : EReal) < (offPt a).2 ∧ (offPt a).2 < ((B + θ : ℝ) : EReal)} := by
  obtain ⟨δA, hδA, -, hgA⟩ := t3_gapEx (critSet hTame) one_pos A
  obtain ⟨δB, hδB, -, hgB⟩ := t3_gapEx (critSet hTame) one_pos B
  refine ⟨min (min δA δB) (b - B), lt_min (lt_min hδA hδB) (by linarith),
    fun θ hθ hθ₀ => ?_⟩
  have h1 : min (min δA δB) (b - B) ≤ min δA δB := min_le_left _ _
  have h2 : min (min δA δB) (b - B) ≤ b - B := min_le_right _ _
  have h3 : min δA δB ≤ δA := min_le_left _ _
  have h4 : min δA δB ≤ δB := min_le_right _ _
  have hθA : θ < δA := by linarith
  have hθB : θ < δB := by linarith
  have hθb : θ < b - B := by linarith
  
  have nearA : ∀ τ ∈ (critSet hTame : Set ℝ), |τ - A| < δA → τ = A := by
    intro τ hτ hlt
    by_contra hne
    exact absurd (hgA τ (Finset.mem_coe.mp hτ) hne) (not_lt.mpr hlt.le)
  have nearB : ∀ τ ∈ (critSet hTame : Set ℝ), |τ - B| < δB → τ = B := by
    intro τ hτ hlt
    by_contra hne
    exact absurd (hgB τ (Finset.mem_coe.mp hτ) hne) (not_lt.mpr hlt.le)
  refine ⟨fun hc => ?_, fun hc => ?_, by linarith, ?_⟩
  · have := nearA _ hc (by rw [show A - θ - A = -θ by ring, abs_neg, abs_of_pos hθ]; exact hθA)
    linarith
  · have := nearB _ hc (by rw [show B + θ - B = θ by ring, abs_of_pos hθ]; exact hθB)
    linarith
  ext a
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hb, hA, hB⟩
    refine ⟨hb, lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr (by linarith)) hA,
      lt_of_le_of_lt hB (EReal.coe_lt_coe_iff.mpr (by linarith))⟩
  · rintro ⟨hb, hlo, hhi⟩
    have hez : (((offPt a).2.toReal : ℝ) : EReal) = (offPt a).2 :=
      EReal.coe_toReal (ne_top_of_lt hhi) (ne_bot_of_gt hlo)
    rw [← hez] at hlo hhi ⊢
    have hz1 := EReal.coe_lt_coe_iff.mp hlo
    have hz2 := EReal.coe_lt_coe_iff.mp hhi
    
    have hcrit : (offPt a).2.toReal ∈ (critSet hTame : Set ℝ) := by
      by_contra hzn
      have h0 := t3_death_pin hLaw hTame (b := b) (d := (offPt a).2.toReal) (by linarith) hzn
      have hpt : offPt a = (((b : ℝ) : EReal), (((offPt a).2.toReal : ℝ) : EReal)) :=
        Prod.ext hb hez.symm
      have hlt : ((a.1.2 : ℕ) : ℕ∞) < mult (rankFn stage J) (offPt a) := a.2
      rw [hpt, h0] at hlt
      exact absurd hlt (not_lt.mpr zero_le)
    refine ⟨hb, EReal.coe_le_coe_iff.mpr ?_, EReal.coe_le_coe_iff.mpr ?_⟩
    · by_contra hlt
      push_neg at hlt
      have := nearA _ hcrit (abs_lt.mpr ⟨by linarith, by linarith⟩)
      linarith
    · by_contra hlt
      push_neg at hlt
      have := nearB _ hcrit (abs_lt.mpr ⟨by linarith, by linarith⟩)
      linarith

noncomputable def bornCount {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (b : ℝ) : ℝ → ℕ∞ :=
  fun t => ({C : comps stage J t | birthSup hLaw t C = b} : Set (comps stage J t)).encard

theorem bornCount_ne_top {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) (b t : ℝ) :
    bornCount hLaw b t ≠ ⊤ := by
  haveI := (hTame.1 t).to_subtype
  exact (Set.toFinite _).encard_lt_top.ne

theorem eCore {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameX : IsTameModule stageX JX) (hTameY : IsTameModule stageY JY) {α ε : ℝ}
    (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x))
    (hSq4 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (x : comps stageX JX β),
      ψ (β - ε) hβε (φ β hβ x) = structMap hLawX (show (β - ε) - ε ≤ β by linarith) x)
    {b A B : ℝ} (hαA : α < A) (hAB : A ≤ B) (hBb : B + 2 * ε < b) :
    ({a : offD (mult (rankFn stageX JX)) | (offPt a).1 = ((b : ℝ) : EReal) ∧
        ((A : ℝ) : EReal) ≤ (offPt a).2 ∧ (offPt a).2 ≤ ((B : ℝ) : EReal)}).encard ≤
      ({a : offD (mult (rankFn (trS stageX α) (imJ φ))) | (offPt a).1 = ((b : ℝ) : EReal) ∧
        ((A : ℝ) : EReal) ≤ (offPt a).2 ∧ (offPt a).2 ≤ ((B + 2 * ε : ℝ) : EReal)}).encard := by
  have hLI := imLaw hLawX hLawY φ hSq1
  have hTI := imTame hLawX hLawY hTameX hTameY φ hSq1
  obtain ⟨θX, hθX, hX⟩ := copies_birth_closed_open hLawX hTameX (b := b) hAB (by linarith)
  obtain ⟨θI, hθI, hI⟩ := copies_birth_closed_open hLI hTI (b := b) (A := A) (B := B + 2 * ε)
    (by linarith) hBb
  set m := min (min θX θI) ((A - α) / 2) with hmdef
  have e1 : m ≤ min θX θI := min_le_left _ _
  have e2 : m ≤ (A - α) / 2 := min_le_right _ _
  have e3 : min θX θI ≤ θX := min_le_left _ _
  have e4 : min θX θI ≤ θI := min_le_right _ _
  have hm : 0 < m := lt_min (lt_min hθX hθI) (by linarith)
  set θ := m / 2 with hθdef
  have hθ : 0 < θ := by linarith
  obtain ⟨hXS, hXT, hXTb, hXeq⟩ := hX θ hθ (by linarith)
  obtain ⟨hIS, hIT, hITb, hIeq⟩ := hI θ hθ (by linarith)
  rw [hXeq, hIeq]
  
  have cX := copies_birth_window hLawX hTameX (b := b) (D₁ := A - θ) (D₂ := B + θ)
    (by linarith) hXTb hXS hXT
  have cI := copies_birth_window hLI hTI (b := b) (D₁ := A - θ) (D₂ := B + 2 * ε + θ)
    (by linarith) hITb hIS hIT
  
  have qTop := bornEq_X_le_im hLawX hLawY hTameX hTameY hε φ ψ hSq1 hSq4
    (t := B + 2 * ε + θ) (b := b) (by linarith) hITb
  have qBot := bornEq_im_le_X hLawX hLawY hTameX hTameY φ hSq1 (t := A - θ) (b := b)
    (by rw [max_eq_left (by linarith)]; linarith)
  change bornCount hLawX b (max (B + 2 * ε + θ) α - ε - ε) ≤ bornCount hLI b _ at qTop
  change bornCount hLI b (A - θ) ≤ bornCount hLawX b (max (A - θ) α) at qBot
  rw [show max (B + 2 * ε + θ) α - ε - ε = B + θ by
    rw [max_eq_left (by linarith)]; ring] at qTop
  rw [max_eq_left (by linarith : α ≤ A - θ)] at qBot
  change _ + bornCount hLawX b (A - θ) = bornCount hLawX b (B + θ) at cX
  change _ + bornCount hLI b (A - θ) = bornCount hLI b (B + 2 * ε + θ) at cI
  
  have hfin := bornCount_ne_top hLawX hTameX b (A - θ)
  refine (ENat.add_le_add_iff_right hfin).mp ?_
  calc _ + bornCount hLawX b (A - θ) = bornCount hLawX b (B + θ) := cX
    _ ≤ bornCount hLI b (B + 2 * ε + θ) := qTop
    _ = _ + bornCount hLI b (A - θ) := cI.symm
    _ ≤ _ + bornCount hLawX b (A - θ) := add_le_add le_rfl qBot

theorem meet_image {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) {l u x : ℝ} (hlu : l ≤ u) (hux : u ≤ x) :
    structMap hLaw hlu '' meetSet stage J u x = meetSet stage J l x := by
  ext D
  constructor
  · rintro ⟨C, ⟨w, hwC, hwx⟩, rfl⟩
    obtain ⟨hws, hCw⟩ := comps_eq_imCls_of_mem hLaw u C hwC
    rw [hCw, structMap_imCls hLaw hlu w hws]
    exact ⟨w, hLaw.refl (hLaw.antitone hlu hws), hwx⟩
  · rintro ⟨w, hwD, hwx⟩
    obtain ⟨hws, hDw⟩ := comps_eq_imCls_of_mem hLaw l D hwD
    have hwu : w ∈ stage u := hLaw.antitone hux hwx
    refine ⟨imCls (J := J) u w hwu, ⟨w, hLaw.refl hwu, hwx⟩, ?_⟩
    rw [structMap_imCls hLaw hlu w hwu, hDw]

theorem cwd_meet_anti {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) {t x x' : ℝ} (hxx : x ≤ x') :
    meetSet stage J t x' ⊆ meetSet stage J t x := by
  rintro C ⟨w, hwC, hwx⟩
  exact ⟨w, hwC, hLaw.antitone hxx hwx⟩

theorem cwd_rank_ncard {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {t x : ℝ} (htx : t ≤ x) :
    rankFn stage J x t = ((meetSet stage J t x).ncard : ℕ∞) := by
  haveI : Finite (comps stage J t) := (hTame.1 t).to_subtype
  rw [t3_rank_meets hLaw htx, Set.Finite.cast_ncard_eq (Set.toFinite (meetSet stage J t x))]
  congr 1
  ext C
  exact (meetSet_iff_img hLaw htx C).symm

theorem cwd_diff_le {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {l u x x' : ℝ}
    (hlu : l ≤ u) (hux : u ≤ x) (hxx : x ≤ x') :
    (meetSet stage J l x \ meetSet stage J l x').ncard ≤
      (meetSet stage J u x \ meetSet stage J u x').ncard := by
  haveI : Finite (comps stage J u) := (hTame.1 u).to_subtype
  haveI : Finite (comps stage J l) := (hTame.1 l).to_subtype
  have hsub : meetSet stage J l x \ meetSet stage J l x' ⊆
      structMap hLaw hlu '' (meetSet stage J u x \ meetSet stage J u x') := by
    rintro D ⟨hD1, hD2⟩
    rw [← meet_image hLaw hlu hux] at hD1
    obtain ⟨C, hC, rfl⟩ := hD1
    refine ⟨C, ⟨hC, fun hC' => hD2 ?_⟩, rfl⟩
    rw [← meet_image hLaw hlu (hux.trans hxx)]
    exact ⟨C, hC', rfl⟩
  exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_image_le (Set.toFinite _))

theorem cwd_ncard_le {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {l u x : ℝ}
    (hlu : l ≤ u) (hux : u ≤ x) :
    (meetSet stage J l x).ncard ≤ (meetSet stage J u x).ncard := by
  haveI : Finite (comps stage J u) := (hTame.1 u).to_subtype
  rw [← meet_image hLaw hlu hux]
  exact Set.ncard_image_le (Set.toFinite _)

theorem cwd_meet_const {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {t x x' : ℝ}
    (htx : t ≤ x) (hxx : x ≤ x') (hfree : ∀ c ∈ critSet hTame, c < x ∨ x' < c) :
    meetSet stage J t x = meetSet stage J t x' := by
  have hgen : ∀ y, x ≤ y → y ≤ x' → ∀ C : comps stage J t, y ≠ birthSup hLaw t C := by
    intro y h1 h2 C he
    have hc := t3_bSup_in_crit hLaw hTame C
    rw [← he] at hc
    rcases hfree y (Finset.mem_coe.mp hc) with h | h <;> linarith
  ext C
  rw [meetSet_iff_img hLaw htx, meetSet_iff_img hLaw (htx.trans hxx),
    t3_meets_birthSup hLaw hTame htx (hgen x le_rfl hxx) C,
    t3_meets_birthSup hLaw hTame (htx.trans hxx) (hgen x' hxx le_rfl) C]
  constructor
  · intro h
    rcases hfree _ (Finset.mem_coe.mp (t3_bSup_in_crit hLaw hTame C)) with h' | h'
    · linarith
    · exact h'
  · intro h; linarith

theorem cwd_jump_core {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {z b η : ℝ}
    (hη : 0 < η) (hzb : z + η ≤ b - η) :
    (meetSet stage J (z + η) (b - η)).ncard - (meetSet stage J (z - η) (b - η)).ncard =
      (meetSet stage J (z + η) (b + η)).ncard - (meetSet stage J (z - η) (b + η)).ncard +
      (t3_comb stage J b z η).toNat := by
  haveI : Finite (comps stage J (z + η)) := (hTame.1 _).to_subtype
  haveI : Finite (comps stage J (z - η)) := (hTame.1 _).to_subtype
  have h1 : z - η ≤ z + η := by linarith
  have h2 : z + η ≤ b + η := by linarith
  have h3 : b - η ≤ b + η := by linarith
  unfold t3_comb
  rw [cwd_rank_ncard hLaw hTame hzb, cwd_rank_ncard hLaw hTame h2,
    cwd_rank_ncard hLaw hTame (h1.trans hzb), cwd_rank_ncard hLaw hTame (h1.trans h2),
    ← ENat.coe_sub, ← ENat.coe_sub, ← ENat.coe_sub, ENat.toNat_coe]
  have hA := Set.ncard_diff_add_ncard_of_subset (cwd_meet_anti hLaw (t := z + η) h3)
    (Set.toFinite (meetSet stage J (z + η) (b - η)))
  have hC := Set.ncard_diff_add_ncard_of_subset (cwd_meet_anti hLaw (t := z - η) h3)
    (Set.toFinite (meetSet stage J (z - η) (b - η)))
  have hpq := cwd_diff_le hLaw hTame h1 hzb h3
  have hca := cwd_ncard_le hLaw hTame (x := b - η) h1 hzb
  have hcb := cwd_ncard_le hLaw hTame (x := b + η) h1 (hzb.trans h3)
  omega

theorem cwd_jump_theta {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {z c η θ : ℝ}
    (hθ : 0 < θ) (hθη : θ < η) (hzc : z + η ≤ c - η)
    (hgap : ∀ c' ∈ critSet hTame, c' < c - η ∨ c + η < c' ∨ c' = c) :
    (meetSet stage J (z + η) (c - θ)).ncard - (meetSet stage J (z - η) (c - θ)).ncard =
      (meetSet stage J (z + η) (c + θ)).ncard - (meetSet stage J (z - η) (c + θ)).ncard +
      (t3_comb stage J c z η).toNat := by
  have hη : 0 < η := hθ.trans hθη
  have hf1 : ∀ c' ∈ critSet hTame, c' < c - η ∨ c - θ < c' := by
    intro c' hc'
    rcases hgap c' hc' with h | h | h
    · exact Or.inl h
    · right; linarith
    · right; linarith
  have hf2 : ∀ c' ∈ critSet hTame, c' < c + θ ∨ c + η < c' := by
    intro c' hc'
    rcases hgap c' hc' with h | h | h
    · left; linarith
    · exact Or.inr h
    · left; linarith
  have hl : z - η ≤ z + η := by linarith
  rw [← cwd_meet_const hLaw hTame hzc (by linarith) hf1,
    ← cwd_meet_const hLaw hTame (hl.trans hzc) (by linarith) hf1,
    cwd_meet_const hLaw hTame (show z + η ≤ c + θ by linarith) (by linarith) hf2,
    cwd_meet_const hLaw hTame (show z - η ≤ c + θ by linarith) (by linarith) hf2]
  exact cwd_jump_core hLaw hTame hη hzc

theorem cwd_fin_unif {Q : ℝ → ℝ → Prop} (W : Finset ℝ)
    (hQ : ∀ b ∈ W, ∃ δ > 0, ∀ η, 0 < η → η < δ → Q b η) :
    ∃ δ > 0, ∀ b ∈ W, ∀ η, 0 < η → η < δ → Q b η := by
  classical
  induction W using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun b hb => by simp at hb⟩
  | insert a W ha ih =>
    obtain ⟨ε, hε, hle⟩ := ih (fun b hb => hQ b (Finset.mem_insert_of_mem hb))
    obtain ⟨δa, hδa, ha'⟩ := hQ a (Finset.mem_insert_self a W)
    refine ⟨min ε δa, lt_min hε hδa, ?_⟩
    intro b hb η h0 hη
    have h1 : min ε δa ≤ ε := min_le_left _ _
    have h2 : min ε δa ≤ δa := min_le_right _ _
    rcases Finset.mem_insert.mp hb with hba | hb
    · rw [hba]; exact ha' η h0 (by linarith)
    · exact hle b hb η h0 (by linarith)

theorem cwd_fiber_sum {D : EReal × EReal → ℕ∞} (d : EReal) (W : Finset ℝ) :
    ({a : offD D | (offPt a).2 = d ∧ ∃ b ∈ W, (offPt a).1 = ((b : ℝ) : EReal)}).encard =
      ∑ b ∈ W, D (((b : ℝ) : EReal), d) := by
  classical
  induction W using Finset.induction_on with
  | empty => simp
  | insert b W hb ih =>
    have hsplit : ({a : offD D | (offPt a).2 = d ∧ ∃ y ∈ insert b W,
        (offPt a).1 = ((y : ℝ) : EReal)}) =
        {a : offD D | offPt a = (((b : ℝ) : EReal), d)} ∪
        {a : offD D | (offPt a).2 = d ∧ ∃ y ∈ W, (offPt a).1 = ((y : ℝ) : EReal)} := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_union, Finset.mem_insert, Prod.ext_iff]
      constructor
      · rintro ⟨h1, y, hy | hy, h2⟩
        · subst hy; exact Or.inl ⟨h2, h1⟩
        · exact Or.inr ⟨h1, y, hy, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, y, hy, h2⟩)
        · exact ⟨h2, b, Or.inl rfl, h1⟩
        · exact ⟨h1, y, Or.inr hy, h2⟩
    have hdis : Disjoint {a : offD D | offPt a = (((b : ℝ) : EReal), d)}
        {a : offD D | (offPt a).2 = d ∧ ∃ y ∈ W, (offPt a).1 = ((y : ℝ) : EReal)} := by
      rw [Set.disjoint_left]
      rintro a ha ⟨-, y, hy, h2⟩
      have ha1 : (offPt a).1 = ((b : ℝ) : EReal) := by rw [Set.mem_setOf_eq.mp ha]
      rw [ha1] at h2
      have hby : b = y := EReal.coe_injective h2
      exact hb (hby ▸ hy)
    rw [hsplit, Set.encard_union_eq hdis, t5_offD_fiber_encard, ih, Finset.sum_insert hb]

theorem cwd_copies_eq {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {z L R : ℝ}
    (hzL : z < L) (W : Finset ℝ)
    (hW : ∀ b, b ∈ W ↔ b ∈ critSet hTame ∧ L < b ∧ b < R) :
    {a : offD (mult (rankFn stage J)) | ((L : ℝ) : EReal) < (offPt a).1 ∧
        (offPt a).1 < ((R : ℝ) : EReal) ∧ (offPt a).2 = ((z : ℝ) : EReal)} =
    {a : offD (mult (rankFn stage J)) | (offPt a).2 = ((z : ℝ) : EReal) ∧
        ∃ b ∈ W, (offPt a).1 = ((b : ℝ) : EReal)} := by
  ext a
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have heb : (((offPt a).1.toReal : ℝ) : EReal) = (offPt a).1 :=
      EReal.coe_toReal (ne_top_of_lt h2) (ne_bot_of_gt h1)
    refine ⟨h3, (offPt a).1.toReal, ?_, heb.symm⟩
    rw [← heb] at h1 h2
    have hb1 := EReal.coe_lt_coe_iff.mp h1
    have hb2 := EReal.coe_lt_coe_iff.mp h2
    refine (hW _).mpr ⟨?_, hb1, hb2⟩
    by_contra hbn
    have h0 := t3_birth_pin hLaw hTame (b := (offPt a).1.toReal) (d := z) (by linarith)
      (fun hm => hbn (Finset.mem_coe.mp hm))
    have hpt : offPt a = ((((offPt a).1.toReal : ℝ) : EReal), ((z : ℝ) : EReal)) :=
      Prod.ext heb.symm h3
    have hlt : ((a.1.2 : ℕ) : ℕ∞) < mult (rankFn stage J) (offPt a) := a.2
    rw [hpt, h0] at hlt
    exact absurd hlt (not_lt.mpr zero_le)
  · rintro ⟨h1, b, hb, h2⟩
    obtain ⟨-, hb1, hb2⟩ := (hW b).mp hb
    exact ⟨by rw [h2]; exact EReal.coe_lt_coe_iff.mpr hb1,
      by rw [h2]; exact EReal.coe_lt_coe_iff.mpr hb2, h1⟩

theorem cwd_thresholds {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {z L : ℝ} (hzL : z < L) :
    ∃ δ > 0, ∀ c ∈ (critSet hTame).filter (fun b => L < b), ∀ η, 0 < η → η < δ →
      (mult (rankFn stage J) ((c : EReal), (z : EReal)) = t3_comb stage J c z η ∧
        ∀ c' ∈ critSet hTame, c' < c - η ∨ c + η < c' ∨ c' = c) := by
  apply cwd_fin_unif
  intro c hc
  have hLc : L < c := (Finset.mem_filter.mp hc).2
  obtain ⟨δ₁, hδ₁, -, hcomb⟩ := mult_eq_comb_small hLaw hTame (b := c) (d := z) (by linarith)
  obtain ⟨δ₀, hδ₀, -, hgap⟩ := t3_gapEx (critSet hTame) one_pos c
  refine ⟨min δ₁ δ₀, lt_min hδ₁ hδ₀, fun η h0 hη => ⟨hcomb η ⟨h0, ?_⟩, ?_⟩⟩
  · exact lt_of_lt_of_le hη (min_le_left _ _)
  · intro c' hc'
    by_cases hcc : c' = c
    · exact Or.inr (Or.inr hcc)
    have hg := hgap c' hc' hcc
    have hm : min δ₁ δ₀ ≤ δ₀ := min_le_right _ _
    rcases lt_or_ge c' c with hlt | hge
    · rw [abs_of_neg (by linarith)] at hg; left; linarith
    · rw [abs_of_nonneg (by linarith)] at hg; right; left; linarith

theorem cwd_hconst {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {z L η : ℝ}
    (hη : 0 < η) (hzL : z + η ≤ L) (hL : L ∉ (critSet hTame : Set ℝ))
    (G : ℝ → ℕ) (hG : ∀ x, G x = (meetSet stage J (z + η) x).ncard -
      (meetSet stage J (z - η) x).ncard) (h : ℝ → ℕ) (hh : ∀ y, h y = G (max (-y) L))
    (Z : Finset ℝ) (hZ : ∀ y, y ∈ Z ↔ -y ∈ critSet hTame ∧ y < -L) :
    ∀ s t : ℝ, s ≤ t → (∀ y ∈ Z, y < s ∨ t < y) → h s = h t := by
  intro s t hst hfz
  have hmx : max (-t) L ≤ max (-s) L := max_le_max (by linarith) le_rfl
  have hfree : ∀ c ∈ critSet hTame, c < max (-t) L ∨ max (-s) L < c := by
    intro c hc
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hLe : L ≤ c := (le_max_right _ _).trans h1
    have hLc : L < c := lt_of_le_of_ne hLe (fun e => hL (by rw [e]; exact Finset.mem_coe.mpr hc))
    have hcZ : -c ∈ Z := (hZ _).mpr ⟨by rwa [neg_neg], by linarith⟩
    have ht' : -t ≤ c := (le_max_left _ _).trans h1
    rcases le_total (-s) L with hsL | hsL
    · rw [max_eq_right hsL] at h2; linarith
    · rw [max_eq_left hsL] at h2
      rcases hfz _ hcZ with h3 | h3 <;> linarith
  have hu : z + η ≤ max (-t) L := hzL.trans (le_max_right _ _)
  have hl : z - η ≤ max (-t) L := by linarith
  rw [hh, hh, hG, hG, cwd_meet_const hLaw hTame hu hmx hfree,
    cwd_meet_const hLaw hTame hl hmx hfree]

theorem cwd_hjump {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {z L η : ℝ}
    (hη : 0 < η) (hz2 : z + 2 * η ≤ L)
    (hQ : ∀ c ∈ (critSet hTame).filter (fun b => L < b),
      (mult (rankFn stage J) ((c : EReal), (z : EReal)) = t3_comb stage J c z η ∧
        ∀ c' ∈ critSet hTame, c' < c - η ∨ c + η < c' ∨ c' = c))
    (G : ℝ → ℕ) (hG : ∀ x, G x = (meetSet stage J (z + η) x).ncard -
      (meetSet stage J (z - η) x).ncard) (h : ℝ → ℕ) (hh : ∀ y, h y = G (max (-y) L))
    (m : ℝ → ℕ) (hm : ∀ y, m y =
      (mult (rankFn stage J) (((-y : ℝ) : EReal), ((z : ℝ) : EReal))).toNat)
    (Z : Finset ℝ) (hZ : ∀ y, y ∈ Z ↔ -y ∈ critSet hTame ∧ y < -L) :
    ∀ y ∈ Z, ∃ η₀ > 0, ∀ θ, 0 < θ → θ < η₀ → h (y + θ) = h (y - θ) + m y := by
  intro y hy
  obtain ⟨hyc, hyL⟩ := (hZ y).mp hy
  obtain ⟨hcomb, hgap⟩ := hQ (-y) (Finset.mem_filter.mpr ⟨hyc, by linarith⟩)
  refine ⟨min η (-y - L), lt_min hη (by linarith), ?_⟩
  intro θ hθ hθlt
  have hn1 : min η (-y - L) ≤ η := min_le_left _ _
  have hn2 : min η (-y - L) ≤ -y - L := min_le_right _ _
  have hp : max (-(y + θ)) L = -y - θ := by rw [max_eq_left (by linarith)]; ring
  have hq : max (-(y - θ)) L = -y + θ := by rw [max_eq_left (by linarith)]; ring
  rw [hh, hh, hp, hq, hG, hG, hm, hcomb]
  exact cwd_jump_theta hLaw hTame hθ (by linarith) (by linarith) hgap

theorem cwd_tel {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {z L R η : ℝ}
    (hη : 0 < η) (hz2 : z + 2 * η ≤ L) (hLR : L ≤ R)
    (hL : L ∉ (critSet hTame : Set ℝ)) (hR : R ∉ (critSet hTame : Set ℝ))
    (hQ : ∀ c ∈ (critSet hTame).filter (fun b => L < b),
      (mult (rankFn stage J) ((c : EReal), (z : EReal)) = t3_comb stage J c z η ∧
        ∀ c' ∈ critSet hTame, c' < c - η ∨ c + η < c' ∨ c' = c)) :
    (meetSet stage J (z + η) L).ncard - (meetSet stage J (z - η) L).ncard =
      (meetSet stage J (z + η) R).ncard - (meetSet stage J (z - η) R).ncard +
      ∑ b ∈ (critSet hTame).filter (fun b => L < b ∧ b < R),
        (mult (rankFn stage J) (((b : ℝ) : EReal), ((z : ℝ) : EReal))).toNat := by
  classical
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℕ, ∀ x, G x = (meetSet stage J (z + η) x).ncard -
      (meetSet stage J (z - η) x).ncard := ⟨_, fun _ => rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : ℝ → ℕ, ∀ y, h y = G (max (-y) L) := ⟨_, fun _ => rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : ℝ → ℕ, ∀ y, m y =
      (mult (rankFn stage J) (((-y : ℝ) : EReal), ((z : ℝ) : EReal))).toNat :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : Finset ℝ, ∀ y, y ∈ Z ↔ -y ∈ critSet hTame ∧ y < -L :=
    ⟨((critSet hTame).image (fun c => -c)).filter (· < -L), fun y => by
      rw [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨c, hc, rfl⟩, h2⟩; exact ⟨by rwa [neg_neg], h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨-y, h1, neg_neg y⟩, h2⟩⟩
  have hLZ : -L ∉ Z := fun hz => lt_irrefl _ ((hZ _).mp hz).2
  have hRZ : -R ∉ Z := fun hz => hR (by
    have h1 := ((hZ _).mp hz).1
    rw [neg_neg] at h1
    exact Finset.mem_coe.mpr h1)
  have ht := telescope_finite h m Z
    (cwd_hconst hLaw hTame hη (by linarith) hL G hG h hh Z hZ)
    (cwd_hjump hLaw hTame hη hz2 hQ G hG h hh m hm Z hZ) (show -R ≤ -L by linarith) hRZ hLZ
  rw [hh, hh, neg_neg, neg_neg, max_self, max_eq_left hLR, hG, hG] at ht
  have hZf : Z.filter (fun y => -R < y ∧ y < -L) =
      ((critSet hTame).filter (fun b => L < b ∧ b < R)).image (fun b => -b) := by
    ext y
    rw [Finset.mem_filter, Finset.mem_image, hZ]
    constructor
    · rintro ⟨⟨h1, -⟩, h2, h3⟩
      exact ⟨-y, Finset.mem_filter.mpr ⟨h1, by linarith, by linarith⟩, neg_neg y⟩
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.mp hb
      exact ⟨⟨by rwa [neg_neg], by linarith⟩, by linarith, by linarith⟩
  rw [hZf, Finset.sum_image (by intro a _ b _ hab; exact neg_injective hab)] at ht
  simp only [hm, neg_neg] at ht
  exact ht

theorem copies_death_window {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {z L R : ℝ}
    (hLR : L ≤ R) (hzL : z < L)
    (hL : L ∉ (critSet hTame : Set ℝ)) (hR : R ∉ (critSet hTame : Set ℝ)) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ →
      ({a : offD (mult (rankFn stage J)) | ((L : ℝ) : EReal) < (offPt a).1 ∧
          (offPt a).1 < ((R : ℝ) : EReal) ∧ (offPt a).2 = ((z : ℝ) : EReal)}).encard +
        (meetSet stage J (z + η) R).encard + (meetSet stage J (z - η) L).encard =
      (meetSet stage J (z + η) L).encard + (meetSet stage J (z - η) R).encard := by
  classical
  obtain ⟨δ, hδ, hδQ⟩ := cwd_thresholds hLaw hTame hzL
  refine ⟨min δ ((L - z) / 2), lt_min hδ (by linarith), ?_⟩
  intro η hη hηlt
  have hm1 : min δ ((L - z) / 2) ≤ δ := min_le_left _ _
  have hm2 : min δ ((L - z) / 2) ≤ (L - z) / 2 := min_le_right _ _
  have hz2 : z + 2 * η ≤ L := by linarith
  have ht := cwd_tel hLaw hTame hη hz2 hLR hL hR (fun c hc => hδQ c hc η hη (by linarith))
  set W' := (critSet hTame).filter (fun b => L < b ∧ b < R) with hW'def
  have hW' : ∀ b, b ∈ W' ↔ b ∈ critSet hTame ∧ L < b ∧ b < R := by
    intro b; rw [hW'def, Finset.mem_filter]
  rw [cwd_copies_eq hLaw hTame hzL W' hW', cwd_fiber_sum]
  have hfin : ∀ t x : ℝ, (meetSet stage J t x).encard = ((meetSet stage J t x).ncard : ℕ∞) := by
    intro t x
    haveI : Finite (comps stage J t) := (hTame.1 t).to_subtype
    exact ((Set.toFinite _).cast_ncard_eq).symm
  have hsum : ∑ b ∈ W', mult (rankFn stage J) (((b : ℝ) : EReal), ((z : ℝ) : EReal)) =
      ((∑ b ∈ W', (mult (rankFn stage J) (((b : ℝ) : EReal), ((z : ℝ) : EReal))).toNat : ℕ)
        : ℕ∞) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl (fun b hb => ?_)
    obtain ⟨-, hb1, -⟩ := (hW' b).mp hb
    rw [ENat.coe_toNat (t3_mult_lt_top hLaw hTame (((b : ℝ) : EReal), ((z : ℝ) : EReal))
      (Or.inr (EReal.coe_lt_coe_iff.mpr (by linarith))))]
  have hle1 := cwd_ncard_le hLaw hTame (x := L) (show z - η ≤ z + η by linarith) (by linarith)
  have hle2 := cwd_ncard_le hLaw hTame (x := R) (show z - η ≤ z + η by linarith) (by linarith)
  rw [hsum, hfin, hfin, hfin, hfin]
  norm_cast
  omega


theorem copies_death_closed_open {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {z L R : ℝ}
    (hzL : z < L) (hLR : L ≤ R) :
    ∃ θ₀ : ℝ, 0 < θ₀ ∧ ∀ θ : ℝ, 0 < θ → θ < θ₀ →
      L - θ ∉ (critSet hTame : Set ℝ) ∧ R + θ ∉ (critSet hTame : Set ℝ) ∧ z < L - θ ∧
      {a : offD (mult (rankFn stage J)) | ((L : ℝ) : EReal) ≤ (offPt a).1 ∧
          (offPt a).1 ≤ ((R : ℝ) : EReal) ∧ (offPt a).2 = ((z : ℝ) : EReal)} =
      {a : offD (mult (rankFn stage J)) | ((L - θ : ℝ) : EReal) < (offPt a).1 ∧
          (offPt a).1 < ((R + θ : ℝ) : EReal) ∧ (offPt a).2 = ((z : ℝ) : EReal)} := by
  obtain ⟨δL, hδL, -, hgL⟩ := t3_gapEx (critSet hTame) one_pos L
  obtain ⟨δR, hδR, -, hgR⟩ := t3_gapEx (critSet hTame) one_pos R
  refine ⟨min (min δL δR) (L - z), lt_min (lt_min hδL hδR) (by linarith),
    fun θ hθ hθ₀ => ?_⟩
  have h1 : min (min δL δR) (L - z) ≤ min δL δR := min_le_left _ _
  have h2 : min (min δL δR) (L - z) ≤ L - z := min_le_right _ _
  have h3 : min δL δR ≤ δL := min_le_left _ _
  have h4 : min δL δR ≤ δR := min_le_right _ _
  have hθL : θ < δL := by linarith
  have hθR : θ < δR := by linarith
  have nearL : ∀ τ ∈ (critSet hTame : Set ℝ), |τ - L| < δL → τ = L := by
    intro τ hτ hlt
    by_contra hne
    exact absurd (hgL τ (Finset.mem_coe.mp hτ) hne) (not_lt.mpr hlt.le)
  have nearR : ∀ τ ∈ (critSet hTame : Set ℝ), |τ - R| < δR → τ = R := by
    intro τ hτ hlt
    by_contra hne
    exact absurd (hgR τ (Finset.mem_coe.mp hτ) hne) (not_lt.mpr hlt.le)
  refine ⟨fun hc => ?_, fun hc => ?_, by linarith, ?_⟩
  · have := nearL _ hc (by rw [show L - θ - L = -θ by ring, abs_neg, abs_of_pos hθ]; exact hθL)
    linarith
  · have := nearR _ hc (by rw [show R + θ - R = θ by ring, abs_of_pos hθ]; exact hθR)
    linarith
  ext a
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hL, hR, hz⟩
    exact ⟨lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr (by linarith)) hL,
      lt_of_le_of_lt hR (EReal.coe_lt_coe_iff.mpr (by linarith)), hz⟩
  · rintro ⟨hlo, hhi, hz⟩
    have heb : (((offPt a).1.toReal : ℝ) : EReal) = (offPt a).1 :=
      EReal.coe_toReal (ne_top_of_lt hhi) (ne_bot_of_gt hlo)
    rw [← heb] at hlo hhi ⊢
    have hb1 := EReal.coe_lt_coe_iff.mp hlo
    have hb2 := EReal.coe_lt_coe_iff.mp hhi
    have hcrit : (offPt a).1.toReal ∈ (critSet hTame : Set ℝ) := by
      by_contra hbn
      have h0 := t3_birth_pin hLaw hTame (b := (offPt a).1.toReal) (d := z) (by linarith) hbn
      have hpt : offPt a = ((((offPt a).1.toReal : ℝ) : EReal), ((z : ℝ) : EReal)) :=
        Prod.ext heb.symm hz
      have hlt : ((a.1.2 : ℕ) : ℕ∞) < mult (rankFn stage J) (offPt a) := a.2
      rw [hpt, h0] at hlt
      exact absurd hlt (not_lt.mpr zero_le)
    refine ⟨EReal.coe_le_coe_iff.mpr ?_, EReal.coe_le_coe_iff.mpr ?_, hz⟩
    · by_contra hlt
      push_neg at hlt
      have := nearL _ hcrit (abs_lt.mpr ⟨by linarith, by linarith⟩)
      linarith
    · by_contra hlt
      push_neg at hlt
      have := nearR _ hcrit (abs_lt.mpr ⟨by linarith, by linarith⟩)
      linarith

theorem meetSet_encard_ne_top {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hTame : IsTameModule stage J) (t x : ℝ) : (meetSet stage J t x).encard ≠ ⊤ := by
  haveI := (hTame.1 t).to_subtype
  exact (Set.toFinite _).encard_lt_top.ne

theorem mCore {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameX : IsTameModule stageX JX) (hTameY : IsTameModule stageY JY) {α ε : ℝ}
    (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x))
    (hSq3 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (y : comps stageY JY β),
      φ (β - ε) hβε (ψ β hβ y) =
        structMap hLawY (show (β - ε) - ε ≤ β by linarith) y)
    {z L R : ℝ} (hαz : α < z) (hzL : z < L) (hLR : L ≤ R) :
    ({a : offD (mult (rankFn (trS stageX α) (imJ φ))) | ((L : ℝ) : EReal) ≤ (offPt a).1 ∧
        (offPt a).1 ≤ ((R : ℝ) : EReal) ∧ (offPt a).2 = ((z : ℝ) : EReal)}).encard ≤
      ({a : offD (mult (rankFn stageY JY)) | ((L - ε : ℝ) : EReal) ≤ (offPt a).1 ∧
        (offPt a).1 ≤ ((R + ε : ℝ) : EReal) ∧ (offPt a).2 = ((z - ε : ℝ) : EReal)}).encard := by
  have hLI := imLaw hLawX hLawY φ hSq1
  have hTI := imTame hLawX hLawY hTameX hTameY φ hSq1
  obtain ⟨θI, hθI, hI⟩ := copies_death_closed_open hLI hTI hzL hLR
  obtain ⟨θY, hθY, hY⟩ := copies_death_closed_open hLawY hTameY (z := z - ε) (L := L - ε)
    (R := R + ε) (by linarith) (by linarith)
  set m := min θI θY with hmdef
  have m1 : m ≤ θI := min_le_left _ _
  have m2 : m ≤ θY := min_le_right _ _
  have hm : 0 < m := lt_min hθI hθY
  set θ := m / 2 with hθdef
  obtain ⟨hIL, hIR, hIz, hIeq⟩ := hI θ (by linarith) (by linarith)
  obtain ⟨hYL, hYR, hYz, hYeq⟩ := hY θ (by linarith) (by linarith)
  rw [hIeq, hYeq]
  obtain ⟨ηI, hηI, cI⟩ := copies_death_window hLI hTI (z := z) (L := L - θ) (R := R + θ)
    (by linarith) hIz hIL hIR
  obtain ⟨ηY, hηY, cY⟩ := copies_death_window hLawY hTameY (z := z - ε) (L := L - ε - θ)
    (R := R + ε + θ) (by linarith) hYz hYL hYR
  set k := min (min ηI ηY) (min (z - α) (L - θ - z)) with hkdef
  have k1 : k ≤ min ηI ηY := min_le_left _ _
  have k2 : k ≤ min (z - α) (L - θ - z) := min_le_right _ _
  have k3 : min ηI ηY ≤ ηI := min_le_left _ _
  have k4 : min ηI ηY ≤ ηY := min_le_right _ _
  have k5 : min (z - α) (L - θ - z) ≤ z - α := min_le_left _ _
  have k6 : min (z - α) (L - θ - z) ≤ L - θ - z := min_le_right _ _
  have hk : 0 < k := lt_min (lt_min hηI hηY) (lt_min (by linarith) (by linarith))
  set η := k / 2 with hηdef
  have cI' := cI η (by linarith) (by linarith)
  have cY' := cY η (by linarith) (by linarith)
  have M1 := imWindowCensus hLawX hLawY hε φ ψ hSq1 hSq3 (l := z - η) (u := z + η)
    (L := L - θ) (R := R + θ) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith)
  dsimp only at M1
  have hmu : max (z + η) α = z + η := max_eq_left (by linarith)
  have hml : max (z - η) α = z - η := max_eq_left (by linarith)
  rw [meet_image hLI (by linarith) (by linarith : z + η ≤ R + θ),
    meet_image hLI (by linarith) (by linarith : z + η ≤ L - θ),
    meet_image hLawY _ (by rw [hmu]; linarith : max (z + η) α - ε ≤ L - θ - ε),
    meet_image hLawY _ (by rw [hmu]; linarith : max (z + η) α - ε ≤ R + θ + ε)] at M1
  rw [hmu, hml, show z + η - ε = z - ε + η by ring, show z - η - ε = z - ε - η by ring,
    show L - θ - ε = L - ε - θ by ring, show R + θ + ε = R + ε + θ by ring] at M1
  
  have f1 := meetSet_encard_ne_top hTI (z + η) (R + θ)
  have f2 := meetSet_encard_ne_top hTI (z - η) (L - θ)
  have f3 := meetSet_encard_ne_top hTameY (z - ε - η) (L - ε - θ)
  have f4 := meetSet_encard_ne_top hTameY (z - ε + η) (R + ε + θ)
  have hK : (meetSet (trS stageX α) (imJ φ) (z + η) (R + θ)).encard +
      (meetSet (trS stageX α) (imJ φ) (z - η) (L - θ)).encard +
      ((meetSet stageY JY (z - ε - η) (L - ε - θ)).encard +
        (meetSet stageY JY (z - ε + η) (R + ε + θ)).encard) ≠ ⊤ := by
    simp only [ne_eq, ENat.add_eq_top, not_or]
    exact ⟨⟨f1, f2⟩, f3, f4⟩
  refine (ENat.add_le_add_iff_right hK).mp ?_
  calc _ + ((meetSet (trS stageX α) (imJ φ) (z + η) (R + θ)).encard +
        (meetSet (trS stageX α) (imJ φ) (z - η) (L - θ)).encard +
        ((meetSet stageY JY (z - ε - η) (L - ε - θ)).encard +
          (meetSet stageY JY (z - ε + η) (R + ε + θ)).encard))
      = ((meetSet (trS stageX α) (imJ φ) (z + η) (L - θ)).encard +
          (meetSet (trS stageX α) (imJ φ) (z - η) (R + θ)).encard) +
        ((meetSet stageY JY (z - ε - η) (L - ε - θ)).encard +
          (meetSet stageY JY (z - ε + η) (R + ε + θ)).encard) := by
        rw [← cI']
        ac_rfl
    _ ≤ (meetSet (trS stageX α) (imJ φ) (z + η) (R + θ)).encard +
          (meetSet (trS stageX α) (imJ φ) (z - η) (L - θ)).encard +
        (meetSet stageY JY (z - ε + η) (L - ε - θ)).encard +
          (meetSet stageY JY (z - ε - η) (R + ε + θ)).encard := by
        calc _ = (meetSet (trS stageX α) (imJ φ) (z + η) (L - θ)).encard +
              (meetSet (trS stageX α) (imJ φ) (z - η) (R + θ)).encard +
              (meetSet stageY JY (z - ε - η) (L - ε - θ)).encard +
              (meetSet stageY JY (z - ε + η) (R + ε + θ)).encard := by ac_rfl
          _ ≤ _ := M1
    _ = _ + ((meetSet (trS stageX α) (imJ φ) (z + η) (R + θ)).encard +
        (meetSet (trS stageX α) (imJ φ) (z - η) (L - θ)).encard +
        ((meetSet stageY JY (z - ε - η) (L - ε - θ)).encard +
          (meetSet stageY JY (z - ε + η) (R + ε + θ)).encard)) := by
        calc _ = ((meetSet (trS stageX α) (imJ φ) (z + η) (R + θ)).encard +
              (meetSet (trS stageX α) (imJ φ) (z - η) (L - θ)).encard) +
              ((meetSet stageY JY (z - ε + η) (L - ε - θ)).encard +
                (meetSet stageY JY (z - ε - η) (R + ε + θ)).encard) := by ac_rfl
          _ = _ := by rw [← cY']; ac_rfl


def IDz (D : EReal × EReal → ℕ∞) (κ z : ℝ) : Type :=
  {q : offD D // ∃ b : ℝ, offPt q = (((b : ℝ) : EReal), ((z : ℝ) : EReal)) ∧ z + κ ≤ b}

noncomputable def IDz.b {D : EReal × EReal → ℕ∞} {κ z : ℝ} (q : IDz D κ z) : ℝ :=
  (offPt q.1).1.toReal

theorem IDz.spec {D : EReal × EReal → ℕ∞} {κ z : ℝ} (q : IDz D κ z) :
    offPt q.1 = (((q.b : ℝ) : EReal), ((z : ℝ) : EReal)) ∧ z + κ ≤ q.b := by
  obtain ⟨b, hp, h1⟩ := q.2
  have hb : q.b = b := by
    show (offPt q.1).1.toReal = b
    rw [hp]
    exact EReal.toReal_coe b
  rw [hb]
  exact ⟨hp, h1⟩

theorem mHall_z {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameX : IsTameModule stageX JX) (hTameY : IsTameModule stageY JY) {α ε : ℝ}
    (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x))
    (hSq3 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (y : comps stageY JY β),
      φ (β - ε) hβε (ψ β hβ y) =
        structMap hLawY (show (β - ε) - ε ≤ β by linarith) y)
    {κ z : ℝ} (hκ : 0 < κ) (hαz : α < z)
    (s : Set (IDz (mult (rankFn (trS stageX α) (imJ φ))) κ z)) (hs : s.Finite) :
    s.encard ≤ (⋃ q ∈ s, {y : offD (mult (rankFn stageY JY)) |
      ((q.b - ε : ℝ) : EReal) ≤ (offPt y).1 ∧ (offPt y).1 ≤ ((q.b + ε : ℝ) : EReal) ∧
        (offPt y).2 = ((z - ε : ℝ) : EReal)}).encard := by
  refine t5_cluster_chop ε hε (fun q => q.b) s hs _
    (fun L R => {y : offD (mult (rankFn stageY JY)) |
      ((L - ε : ℝ) : EReal) ≤ (offPt y).1 ∧ (offPt y).1 ≤ ((R + ε : ℝ) : EReal) ∧
        (offPt y).2 = ((z - ε : ℝ) : EReal)}) ?_ ?_ ?_ ?_
  · 
    intro L R hLR
    by_cases hAB : max L (z + κ) ≤ R
    · have a1 : L ≤ max L (z + κ) := le_max_left _ _
      have a2 : z + κ ≤ max L (z + κ) := le_max_right _ _
      have hM := mCore hLawX hLawY hTameX hTameY hε φ ψ hSq1 hSq3 (z := z)
        (L := max L (z + κ)) (R := R) hαz (by linarith) hAB
      refine le_trans ?_ (le_trans hM (Set.encard_le_encard ?_))
      · refine Set.encard_le_encard_of_injOn (f := fun q => q.1) ?_
          (fun q₁ _ q₂ _ h => Subtype.ext h)
        intro q hq
        obtain ⟨hp, h1⟩ := q.spec
        obtain ⟨hq1, hq2⟩ := hq
        refine ⟨?_, ?_, by rw [hp]⟩
        · rw [hp]
          exact EReal.coe_le_coe_iff.mpr (max_le hq1 h1)
        · rw [hp]
          exact EReal.coe_le_coe_iff.mpr hq2
      · rintro y ⟨hy1, hy2, hy3⟩
        exact ⟨le_trans (EReal.coe_le_coe_iff.mpr (by linarith)) hy1, hy2, hy3⟩
    · have hempty : {q : IDz (mult (rankFn (trS stageX α) (imJ φ))) κ z |
          L ≤ q.b ∧ q.b ≤ R} = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.mpr fun q hq => hAB ?_
        obtain ⟨-, h1⟩ := q.spec
        obtain ⟨hq1, hq2⟩ := hq
        exact le_trans (max_le hq1 h1) hq2
      rw [hempty, Set.encard_empty]
      exact zero_le
  · 
    rintro L R - q - hL hR y ⟨hy1, hy2, hy3⟩
    exact ⟨le_trans (EReal.coe_le_coe_iff.mpr (by linarith)) hy1,
      le_trans hy2 (EReal.coe_le_coe_iff.mpr (by linarith)), hy3⟩
  · 
    rintro L R - hwit y hy
    obtain ⟨hy1, hy2, hy3⟩ := hy
    have heb : (((offPt y).1.toReal : ℝ) : EReal) = (offPt y).1 :=
      EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) hy2)
        (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hy1)
    rw [← heb] at hy1 hy2
    obtain ⟨q, hqs, hqL, hqR, hqt⟩ := hwit _ (EReal.coe_le_coe_iff.mp hy1)
      (EReal.coe_le_coe_iff.mp hy2)
    obtain ⟨hlo, hhi⟩ := abs_le.mp hqt
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    refine ⟨q, ⟨hqs, hqL, hqR⟩, ?_, ?_, hy3⟩
    · rw [← heb]; exact EReal.coe_le_coe_iff.mpr (by linarith)
    · rw [← heb]; exact EReal.coe_le_coe_iff.mpr (by linarith)
  · 
    rintro q - q' - t hqt htq'
    refine Set.eq_empty_iff_forall_notMem.mpr fun y hy => ?_
    obtain ⟨⟨-, hy2, -⟩, ⟨hy4, -, -⟩⟩ := hy
    have := le_trans hy4 hy2
    have h := EReal.coe_le_coe_iff.mp this
    linarith


theorem lowLevelCensus {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY) {α ε : ℝ}
    (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x))
    (hSq3 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (y : comps stageY JY β),
      φ (β - ε) hβε (ψ β hβ y) =
        structMap hLawY (show (β - ε) - ε ≤ β by linarith) y)
    {u L R : ℝ} (huL : u ≤ L) (hαL : α ≤ L) (huR : u ≤ R) (hαR : α ≤ R) :
    (meetSet (trS stageX α) (imJ φ) u L \ meetSet (trS stageX α) (imJ φ) u R).encard ≤
      (meetSet stageY JY (max u α - ε) (L - ε) \
        meetSet stageY JY (max u α - ε) (R + ε)).encard := by
  refine Set.encard_le_encard_of_injOn (f := imToY φ u) ?_
    (fun x₁ _ x₂ _ h => imToY_injective hLawX hLawY φ hSq1 u h)
  rintro x ⟨hxL, hxR⟩
  refine ⟨imToY_meet hLawX hLawY φ hSq1 huL hαL ⟨x, hxL, rfl⟩, fun hyR => hxR ?_⟩
  obtain ⟨y, hyR', hyx⟩ := imToY_meet_psi hLawX hLawY hε φ ψ hSq1 hSq3 huR hαR hyR
  rw [← imToY_injective hLawX hLawY φ hSq1 u hyx]
  exact hyR'

theorem lw_rank_meet {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) {t x : ℝ} (htx : t ≤ x) :
    rankFn stage J x t = (meetSet stage J t x).encard := by
  rw [t3_rank_meets hLaw htx]
  congr 1
  ext C
  exact (meetSet_iff_img hLaw htx C).symm

theorem lw_diff_count {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {t b : ℝ} (htb : t < b) :
    ∃ θ₀ : ℝ, 0 < θ₀ ∧ ∀ θ : ℝ, 0 < θ → θ < θ₀ →
      rankFn stage J (b - θ) t - rankFn stage J (b + θ) t = bornCount hLaw b t := by
  obtain ⟨θ₀, hθ₀, h⟩ := bornEq_eq_meetDiff hLaw hTame htb
  refine ⟨min θ₀ (b - t), lt_min hθ₀ (by linarith), fun θ hθ hθlt => ?_⟩
  have h1 : θ < θ₀ := lt_of_lt_of_le hθlt (min_le_left _ _)
  have h2 : θ < b - t := lt_of_lt_of_le hθlt (min_le_right _ _)
  rw [lw_rank_meet hLaw (show t ≤ b - θ by linarith),
    lw_rank_meet hLaw (show t ≤ b + θ by linarith)]
  unfold bornCount
  rw [h θ hθ h1]
  have hsplit := Set.encard_diff_add_encard_of_subset
    (cwd_meet_anti hLaw (t := t) (show b - θ ≤ b + θ by linarith))
  rw [← hsplit]
  exact (ENat.addLECancellable_of_ne_top (meetSet_encard_ne_top hTame t (b + θ))).add_tsub_cancel_right

theorem lw_mult_bot_unfold (r : ℝ → ℝ → ℕ∞) (b : ℝ) :
    mult r ((b : EReal), (⊥ : EReal)) =
      ⨅ (ε : ℝ) (_ : 0 < ε), ⨅ (t : ℝ) (_ : t ≤ b - ε), (r (b - ε) t - r (b + ε) t) := by
  unfold mult
  rw [if_pos ⟨EReal.coe_ne_bot b, EReal.coe_ne_top b⟩, if_pos rfl]
  simp only [EReal.toReal_coe]

theorem lw_count_low {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {b t t' : ℝ}
    (hcrit : ∀ τ ∈ critSet hTame, t < τ) (ht'b : t' < b) :
    bornCount hLaw b t ≤ bornCount hLaw b t' := by
  unfold bornCount
  rcases le_or_gt t' t with h | h
  · exact (hcount_const hLaw hTame b h (fun τ hτ => Or.inr (hcrit τ hτ))).symm.le
  · exact hcount_le_up hLaw hTame h.le ht'b

theorem lw_lower {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {b t t' ε : ℝ}
    (hcrit : ∀ τ ∈ critSet hTame, t < τ) (hε : 0 < ε) (ht' : t' ≤ b - ε) :
    bornCount hLaw b t ≤ rankFn stage J (b - ε) t' - rankFn stage J (b + ε) t' := by
  obtain ⟨θ₀, hθ₀, h⟩ := lw_diff_count hLaw hTame (show t' < b by linarith)
  set θ := min (θ₀ / 2) ε with hθdef
  have hθ1 : θ ≤ θ₀ / 2 := min_le_left _ _
  have hθ2 : θ ≤ ε := min_le_right _ _
  have hθpos : 0 < θ := lt_min (by linarith) hε
  have hA : rankFn stage J (b - θ) t' ≤ rankFn stage J (b - ε) t' := by
    rw [lw_rank_meet hLaw (show t' ≤ b - θ by linarith), lw_rank_meet hLaw ht']
    exact Set.encard_le_encard (cwd_meet_anti hLaw (show b - ε ≤ b - θ by linarith))
  have hB : rankFn stage J (b + ε) t' ≤ rankFn stage J (b + θ) t' := by
    rw [lw_rank_meet hLaw (show t' ≤ b + ε by linarith),
      lw_rank_meet hLaw (show t' ≤ b + θ by linarith)]
    exact Set.encard_le_encard (cwd_meet_anti hLaw (show b + θ ≤ b + ε by linarith))
  calc bornCount hLaw b t ≤ bornCount hLaw b t' :=
        lw_count_low hLaw hTame hcrit (show t' < b by linarith)
    _ = rankFn stage J (b - θ) t' - rankFn stage J (b + θ) t' :=
        (h θ hθpos (by linarith)).symm
    _ ≤ _ := tsub_le_tsub hA hB

theorem mult_bot_eq {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {b t : ℝ}
    (htb : t < b) (hcrit : ∀ τ ∈ critSet hTame, t < τ) :
    mult (rankFn stage J) ((b : EReal), (⊥ : EReal)) =
      ({C : comps stage J t | birthSup hLaw t C = b} : Set (comps stage J t)).encard := by
  rw [lw_mult_bot_unfold]
  change _ = bornCount hLaw b t
  apply le_antisymm
  · obtain ⟨θ₀, hθ₀, h⟩ := lw_diff_count hLaw hTame htb
    set θ := min (θ₀ / 2) (b - t) with hθdef
    have hθ1 : θ ≤ θ₀ / 2 := min_le_left _ _
    have hθ2 : θ ≤ b - t := min_le_right _ _
    have hθpos : 0 < θ := lt_min (by linarith) (by linarith)
    exact ((iInf₂_le θ hθpos).trans (iInf₂_le t (by linarith))).trans_eq
      (h θ hθpos (by linarith))
  · exact le_iInf₂ fun ε hε => le_iInf₂ fun t' ht' => lw_lower hLaw hTame hcrit hε ht'

theorem lw_fiber_sum {α : Type*} (f : α → ℝ) (W : Finset ℝ) (S : Set α)
    (hS : ∀ a ∈ S, f a ∈ W) :
    S.encard = ∑ w ∈ W, (S ∩ {a | f a = w}).encard := by
  classical
  induction W using Finset.induction_on generalizing S with
  | empty =>
    have hS0 : S = ∅ := Set.eq_empty_of_forall_notMem fun a ha => by simpa using hS a ha
    simp [hS0]
  | insert z W hz ih =>
    rw [Finset.sum_insert hz]
    have hS' : ∀ a ∈ S ∩ {a | f a ≠ z}, f a ∈ W := by
      rintro a ⟨haS, haz⟩
      rcases Finset.mem_insert.mp (hS a haS) with h | h
      · exact absurd h haz
      · exact h
    have hdis : Disjoint (S ∩ {a | f a = z}) (S ∩ {a | f a ≠ z}) := by
      rw [Set.disjoint_left]
      rintro a ⟨-, h1⟩ ⟨-, h2⟩
      exact h2 h1
    have hun : S = (S ∩ {a | f a = z}) ∪ (S ∩ {a | f a ≠ z}) := by
      ext a
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
      tauto
    conv_lhs => rw [hun]
    rw [Set.encard_union_eq hdis, ih _ hS']
    congr 1
    refine Finset.sum_congr rfl fun w hw => ?_
    congr 1
    ext a
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨h1, -⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨⟨h1, fun h => hz (by rw [← h, h3]; exact hw)⟩, h3⟩

theorem lw_low_level {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hTame : IsTameModule stage J) (u : ℝ) :
    ∃ t₀ : ℝ, t₀ < u ∧ ∀ τ ∈ critSet hTame, t₀ < τ := by
  classical
  refine ⟨(insert u (critSet hTame)).min' ⟨u, Finset.mem_insert_self _ _⟩ - 1, ?_,
    fun τ hτ => ?_⟩
  · have := Finset.min'_le (insert u (critSet hTame)) u (Finset.mem_insert_self _ _)
    linarith
  · have := Finset.min'_le (insert u (critSet hTame)) τ (Finset.mem_insert_of_mem hτ)
    linarith

theorem lw_born_zero {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {b : ℝ}
    (hb : b ∉ (critSet hTame : Set ℝ)) (t : ℝ) : bornCount hLaw b t = 0 := by
  unfold bornCount
  rw [Set.encard_eq_zero]
  refine Set.eq_empty_of_forall_notMem fun C hC => hb ?_
  have hC' : birthSup hLaw t C = b := hC
  rw [← hC']
  exact t3_bSup_in_crit hLaw hTame C

theorem lw_copies_b {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {b u : ℝ}
    (hub : u < b) (hu : u ∉ (critSet hTame : Set ℝ)) :
    ({a : offD (mult (rankFn stage J)) | (offPt a).1 = ((b : ℝ) : EReal) ∧
        ((offPt a).2 = ⊥ ∨ (offPt a).2 < ((u : ℝ) : EReal))}).encard = bornCount hLaw b u := by
  obtain ⟨t₀, ht₀u, ht₀c⟩ := lw_low_level hTame u
  have ht₀n : t₀ ∉ (critSet hTame : Set ℝ) := fun h => lt_irrefl _ (ht₀c t₀ h)
  have hcwb := copies_birth_window hLaw hTame ht₀u.le hub ht₀n hu
  have hbot := mult_bot_eq hLaw hTame (show t₀ < b by linarith) ht₀c
  have hsplit : {a : offD (mult (rankFn stage J)) | (offPt a).1 = ((b : ℝ) : EReal) ∧
        ((offPt a).2 = ⊥ ∨ (offPt a).2 < ((u : ℝ) : EReal))} =
      {a : offD (mult (rankFn stage J)) | offPt a = (((b : ℝ) : EReal), ⊥)} ∪
      {a : offD (mult (rankFn stage J)) | (offPt a).1 = ((b : ℝ) : EReal) ∧
        ((t₀ : ℝ) : EReal) < (offPt a).2 ∧ (offPt a).2 < ((u : ℝ) : EReal)} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_union, Prod.ext_iff]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hb2 : (offPt a).2 = ⊥
      · exact Or.inl ⟨h1, hb2⟩
      · have h2' : (offPt a).2 < ((u : ℝ) : EReal) := h2.resolve_left hb2
        refine Or.inr ⟨h1, ?_, h2'⟩
        by_contra hle
        rw [not_lt] at hle
        have htop : (offPt a).2 ≠ ⊤ := ne_top_of_lt h2'
        have hdeq : (offPt a).2 = (((offPt a).2.toReal : ℝ) : EReal) :=
          (EReal.coe_toReal htop hb2).symm
        have hdt : (offPt a).2.toReal ≤ t₀ := by
          rw [hdeq] at hle
          exact EReal.coe_le_coe_iff.mp hle
        have hpos : (0 : ℕ∞) < mult (rankFn stage J) (offPt a) :=
          lt_of_le_of_lt zero_le a.property
        have hpt : offPt a = (((b : ℝ) : EReal), (((offPt a).2.toReal : ℝ) : EReal)) :=
          Prod.ext h1 hdeq
        rw [hpt, t3_death_pin hLaw hTame (show (offPt a).2.toReal < b by linarith)
          (fun h => lt_irrefl _ (lt_of_le_of_lt hdt (ht₀c _ h)))] at hpos
        exact lt_irrefl _ hpos
    · rintro (⟨h1, h2⟩ | ⟨h1, -, h3⟩)
      · exact ⟨h1, Or.inl h2⟩
      · exact ⟨h1, Or.inr h3⟩
  have hdis : Disjoint
      {a : offD (mult (rankFn stage J)) | offPt a = (((b : ℝ) : EReal), ⊥)}
      {a : offD (mult (rankFn stage J)) | (offPt a).1 = ((b : ℝ) : EReal) ∧
        ((t₀ : ℝ) : EReal) < (offPt a).2 ∧ (offPt a).2 < ((u : ℝ) : EReal)} := by
    rw [Set.disjoint_left]
    rintro a ha ⟨-, h2, -⟩
    have ha2 : (offPt a).2 = ⊥ := by rw [Set.mem_setOf_eq.mp ha]
    rw [ha2] at h2
    exact not_lt_bot h2
  rw [hsplit, Set.encard_union_eq hdis, t5_offD_fiber_encard, hbot, add_comm]
  exact hcwb

theorem lw_meet_diff_sum {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {L R u : ℝ}
    (huL : u ≤ L) (hLR : L ≤ R)
    (hL : L ∉ (critSet hTame : Set ℝ)) (hR : R ∉ (critSet hTame : Set ℝ))
    (W : Finset ℝ) (hW : ∀ τ, τ ∈ W ↔ τ ∈ critSet hTame ∧ L < τ ∧ τ < R) :
    (meetSet stage J u L \ meetSet stage J u R).encard = ∑ w ∈ W, bornCount hLaw w u := by
  have hmem : ∀ x : ℝ, u ≤ x → x ∉ (critSet hTame : Set ℝ) → ∀ C : comps stage J u,
      C ∈ meetSet stage J u x ↔ x < birthSup hLaw u C := fun x hux hx C =>
    (meetSet_iff_img hLaw hux C).trans (t3_meets_birthSup hLaw hTame hux
      (fun C' h => hx (by rw [h]; exact t3_bSup_in_crit hLaw hTame C')) C)
  rw [lw_fiber_sum (birthSup hLaw u) W _ ?_]
  · refine Finset.sum_congr rfl fun w hw => ?_
    obtain ⟨-, hLw, hwR⟩ := (hW w).mp hw
    unfold bornCount
    congr 1
    ext C
    simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨-, h⟩
      exact h
    · intro h
      refine ⟨⟨(hmem L huL hL C).mpr (by rw [h]; exact hLw), fun hCR => ?_⟩, h⟩
      have h' := (hmem R (huL.trans hLR) hR C).mp hCR
      rw [h] at h'
      linarith
  · rintro C ⟨hCL, hCR⟩
    rw [hmem L huL hL C] at hCL
    rw [hmem R (huL.trans hLR) hR C, not_lt] at hCR
    have hc := t3_bSup_in_crit hLaw hTame C
    refine (hW _).mpr ⟨hc, hCL, lt_of_le_of_ne hCR fun h => hR ?_⟩
    rw [← h]
    exact hc

theorem copies_level_window {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {L R u : ℝ}
    (hLR : L ≤ R) (huL : u < L)
    (hL : L ∉ (critSet hTame : Set ℝ)) (hR : R ∉ (critSet hTame : Set ℝ))
    (hu : u ∉ (critSet hTame : Set ℝ)) :
    ({a : offD (mult (rankFn stage J)) | ((L : ℝ) : EReal) < (offPt a).1 ∧
        (offPt a).1 < ((R : ℝ) : EReal) ∧
        ((offPt a).2 = ⊥ ∨ (offPt a).2 < ((u : ℝ) : EReal))}).encard +
      (meetSet stage J u R).encard = (meetSet stage J u L).encard := by
  obtain ⟨W, hW⟩ : ∃ W : Finset ℝ, ∀ τ, τ ∈ W ↔ τ ∈ critSet hTame ∧ L < τ ∧ τ < R :=
    ⟨(critSet hTame).filter (fun τ => L < τ ∧ τ < R), fun τ => Finset.mem_filter⟩
  rw [lw_fiber_sum (fun a => (offPt a).1.toReal) W _ ?_]
  · rw [← Set.encard_diff_add_encard_of_subset (cwd_meet_anti hLaw (t := u) hLR),
      lw_meet_diff_sum hLaw hTame huL.le hLR hL hR W hW]
    congr 1
    refine Finset.sum_congr rfl fun w hw => ?_
    obtain ⟨-, hLw, hwR⟩ := (hW w).mp hw
    rw [← lw_copies_b hLaw hTame (show u < w by linarith) hu]
    congr 1
    ext a
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      refine ⟨?_, h3⟩
      rw [← h4]
      exact (EReal.coe_toReal (ne_top_of_lt h2) (ne_bot_of_gt h1)).symm
    · rintro ⟨h1, h3⟩
      refine ⟨⟨?_, ?_, h3⟩, ?_⟩
      · rw [h1]; exact EReal.coe_lt_coe_iff.mpr hLw
      · rw [h1]; exact EReal.coe_lt_coe_iff.mpr hwR
      · simp only [h1, EReal.toReal_coe]
  · rintro a ⟨h1, h2, h3⟩
    obtain ⟨b, hbeq⟩ : ∃ b : ℝ, (offPt a).1 = ((b : ℝ) : EReal) :=
      ⟨_, (EReal.coe_toReal (ne_top_of_lt h2) (ne_bot_of_gt h1)).symm⟩
    rw [hbeq] at h1 h2
    have hLb : L < b := EReal.coe_lt_coe_iff.mp h1
    have hbR : b < R := EReal.coe_lt_coe_iff.mp h2
    show (offPt a).1.toReal ∈ W
    rw [hbeq, EReal.toReal_coe]
    refine (hW b).mpr ⟨?_, hLb, hbR⟩
    by_contra hbc
    have hz := lw_copies_b hLaw hTame (show u < b by linarith) hu
    rw [lw_born_zero hLaw hTame hbc u, Set.encard_eq_zero] at hz
    exact (Set.eq_empty_iff_forall_notMem.mp hz) a ⟨hbeq, h3⟩

theorem interval_hall_aux {X Q α : Type} [LinearOrder α] (lo hi : X → α) (pos : Q → α) :
    ∀ (n : ℕ) (s : Finset X), s.card ≤ n → (∀ x ∈ s, lo x ≤ hi x) →
    (∀ A B : α, A ≤ B → {x ∈ (s : Set X) | A ≤ lo x ∧ hi x ≤ B}.encard ≤
        {q : Q | A ≤ pos q ∧ pos q ≤ B}.encard) →
    (s : Set X).encard ≤ (⋃ x ∈ (s : Set X), {q : Q | lo x ≤ pos q ∧ pos q ≤ hi x}).encard := by
  intro n
  induction n with
  | zero =>
    intro s hs _ _
    have h0 : s = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hs)
    subst h0; simp
  | succ n ih =>
    intro s hcard hlohi hwin
    rcases s.eq_empty_or_nonempty with h | hne
    · subst h; simp
    obtain ⟨x0, hx0, hA⟩ := s.exists_mem_eq_inf' hne lo
    obtain ⟨x1, hx1, hB⟩ := s.exists_mem_eq_sup' hne hi
    by_cases hcov : ∀ q : Q, s.inf' hne lo ≤ pos q → pos q ≤ s.sup' hne hi →
        q ∈ ⋃ x ∈ (s : Set X), {q : Q | lo x ≤ pos q ∧ pos q ≤ hi x}
    · have hAB : s.inf' hne lo ≤ s.sup' hne hi :=
        le_trans (Finset.inf'_le _ hx0) (le_trans (hlohi x0 hx0) (Finset.le_sup' _ hx0))
      have h1 : (s : Set X) ⊆
          {x ∈ (s : Set X) | s.inf' hne lo ≤ lo x ∧ hi x ≤ s.sup' hne hi} :=
        fun x hx => ⟨hx, Finset.inf'_le _ hx, Finset.le_sup' _ hx⟩
      calc (s : Set X).encard ≤ _ := Set.encard_le_encard h1
        _ ≤ _ := hwin _ _ hAB
        _ ≤ _ := Set.encard_le_encard (fun q hq => hcov q hq.1 hq.2)
    · push Not at hcov
      obtain ⟨q, hqA, hqB, hqN⟩ := hcov
      have hsep : ∀ x ∈ s, hi x < pos q ∨ pos q < lo x := by
        intro x hx
        by_contra hc
        push Not at hc
        exact hqN (Set.mem_biUnion (Finset.mem_coe.mpr hx) ⟨hc.2, hc.1⟩)
      have hx0L : hi x0 < pos q := by
        rcases hsep x0 hx0 with h | h
        · exact h
        · exact absurd (hA ▸ hqA) (not_le.mpr h)
      have hx1R : pos q < lo x1 := by
        rcases hsep x1 hx1 with h | h
        · exact absurd (hB ▸ hqB) (not_le.mpr h)
        · exact h
      set L := s.filter (fun x => hi x < pos q) with hLdef
      set R := s.filter (fun x => pos q < lo x) with hRdef
      have hLc : L.card ≤ n := by
        have : L.card < s.card := Finset.card_lt_card
          (Finset.filter_ssubset.mpr ⟨x1, hx1, fun h => absurd (lt_trans h (lt_of_lt_of_le hx1R
            (hlohi x1 hx1))) (lt_irrefl _)⟩)
        omega
      have hRc : R.card ≤ n := by
        have : R.card < s.card := Finset.card_lt_card
          (Finset.filter_ssubset.mpr ⟨x0, hx0, fun h => absurd (lt_trans h (lt_of_le_of_lt
            (hlohi x0 hx0) hx0L)) (lt_irrefl _)⟩)
        omega
      have hLs : L ⊆ s := Finset.filter_subset _ _
      have hRs : R ⊆ s := Finset.filter_subset _ _
      have hL := ih L hLc (fun x hx => hlohi x (hLs hx)) (fun A B hAB => by
        refine le_trans (Set.encard_le_encard ?_) (hwin A B hAB)
        intro x hx; exact ⟨Finset.mem_coe.mpr (hLs hx.1), hx.2⟩)
      have hR := ih R hRc (fun x hx => hlohi x (hRs hx)) (fun A B hAB => by
        refine le_trans (Set.encard_le_encard ?_) (hwin A B hAB)
        intro x hx; exact ⟨Finset.mem_coe.mpr (hRs hx.1), hx.2⟩)
      have hcovs : (s : Set X) ⊆ (L : Set X) ∪ (R : Set X) := by
        intro x hx
        rcases hsep x hx with h | h
        · exact Or.inl (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hx, h⟩))
        · exact Or.inr (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hx, h⟩))
      have hdisj : Disjoint (⋃ x ∈ (L : Set X), {q : Q | lo x ≤ pos q ∧ pos q ≤ hi x})
          (⋃ x ∈ (R : Set X), {q : Q | lo x ≤ pos q ∧ pos q ≤ hi x}) := by
        rw [Set.disjoint_left]
        intro r hr1 hr2
        obtain ⟨x, hx, hrx⟩ := Set.mem_iUnion₂.mp hr1
        obtain ⟨y, hy, hry⟩ := Set.mem_iUnion₂.mp hr2
        have h1 : hi x < pos q := (Finset.mem_filter.mp hx).2
        have h2 : pos q < lo y := (Finset.mem_filter.mp hy).2
        have h3 : pos r ≤ hi x := hrx.2
        have h4 : lo y ≤ pos r := hry.1
        exact absurd (lt_of_le_of_lt h4 (lt_of_le_of_lt h3 (lt_trans h1 h2))) (lt_irrefl _)
      have hsub : (⋃ x ∈ (L : Set X), {q : Q | lo x ≤ pos q ∧ pos q ≤ hi x}) ∪
          (⋃ x ∈ (R : Set X), {q : Q | lo x ≤ pos q ∧ pos q ≤ hi x}) ⊆
          ⋃ x ∈ (s : Set X), {q : Q | lo x ≤ pos q ∧ pos q ≤ hi x} :=
        Set.union_subset (Set.biUnion_subset_biUnion_left (Finset.coe_subset.mpr hLs))
          (Set.biUnion_subset_biUnion_left (Finset.coe_subset.mpr hRs))
      calc (s : Set X).encard ≤ ((L : Set X) ∪ (R : Set X)).encard := Set.encard_le_encard hcovs
        _ ≤ (L : Set X).encard + (R : Set X).encard := Set.encard_union_le _ _
        _ ≤ _ := add_le_add hL hR
        _ = _ := (Set.encard_union_eq hdisj).symm
        _ ≤ _ := Set.encard_le_encard hsub

theorem interval_hall {X Q : Type} (lo hi : X → ℝ) (pos : Q → ℝ)
    (s : Set X) (hs : s.Finite) (hlohi : ∀ x ∈ s, lo x ≤ hi x)
    (hwin : ∀ A B : ℝ, A ≤ B →
      {x ∈ s | A ≤ lo x ∧ hi x ≤ B}.encard ≤ {q : Q | A ≤ pos q ∧ pos q ≤ B}.encard) :
    s.encard ≤ (⋃ x ∈ s, {q : Q | lo x ≤ pos q ∧ pos q ≤ hi x}).encard := by
  obtain ⟨t, rfl⟩ := hs.exists_finset_coe
  exact interval_hall_aux lo hi pos t.card t le_rfl hlohi hwin


theorem eLow {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameX : IsTameModule stageX JX) (hTameY : IsTameModule stageY JY) {α ε : ℝ}
    (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x))
    (hSq4 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (x : comps stageX JX β),
      ψ (β - ε) hβε (φ β hβ x) = structMap hLawX (show (β - ε) - ε ≤ β by linarith) x)
    {b B : ℝ} (hαB : α + ε ≤ B) (hBb : B < b) :
    ({a : offD (mult (rankFn stageX JX)) | (offPt a).1 = ((b : ℝ) : EReal) ∧
        ((offPt a).2 = ⊥ ∨ (offPt a).2 ≤ ((B - 2 * ε : ℝ) : EReal))}).encard ≤
      ({a : offD (mult (rankFn (trS stageX α) (imJ φ))) | (offPt a).1 = ((b : ℝ) : EReal) ∧
        ((offPt a).2 = ⊥ ∨ (offPt a).2 ≤ ((B : ℝ) : EReal))}).encard := by
  have hLI := imLaw hLawX hLawY φ hSq1
  have hTI := imTame hLawX hLawY hTameX hTameY φ hSq1
  obtain ⟨δX, hδX, -, hgX⟩ := t3_gapEx (critSet hTameX) one_pos (B - 2 * ε)
  obtain ⟨δI, hδI, -, hgI⟩ := t3_gapEx (critSet hTI) one_pos B
  set m := min (min δX δI) (b - B) with hmdef
  have m1 : m ≤ min δX δI := min_le_left _ _
  have m2 : m ≤ b - B := min_le_right _ _
  have m3 : min δX δI ≤ δX := min_le_left _ _
  have m4 : min δX δI ≤ δI := min_le_right _ _
  have hm : 0 < m := lt_min (lt_min hδX hδI) (by linarith)
  set θ := m / 2 with hθdef
  have hθ : 0 < θ := by linarith
  
  have htX : B - 2 * ε + θ ∉ (critSet hTameX : Set ℝ) := by
    intro hc
    have hne : B - 2 * ε + θ ≠ B - 2 * ε := by linarith
    have := hgX _ (Finset.mem_coe.mp hc) hne
    rw [show B - 2 * ε + θ - (B - 2 * ε) = θ by ring, abs_of_pos hθ] at this
    linarith
  have hTI' : B + θ ∉ (critSet hTI : Set ℝ) := by
    intro hc
    have hne : B + θ ≠ B := by linarith
    have := hgI _ (Finset.mem_coe.mp hc) hne
    rw [show B + θ - B = θ by ring, abs_of_pos hθ] at this
    linarith
  
  have hX := lw_copies_b hLawX hTameX (b := b) (u := B - 2 * ε + θ) (by linarith) htX
  have hI := lw_copies_b hLI hTI (b := b) (u := B + θ) (by linarith) hTI'
  have qTop := bornEq_X_le_im hLawX hLawY hTameX hTameY hε φ ψ hSq1 hSq4
    (t := B + θ) (b := b) (by linarith) (by linarith)
  change bornCount hLawX b (max (B + θ) α - ε - ε) ≤ bornCount hLI b (B + θ) at qTop
  rw [show max (B + θ) α - ε - ε = B - 2 * ε + θ by
    rw [max_eq_left (by linarith)]; ring] at qTop
  have hsubX : {a : offD (mult (rankFn stageX JX)) | (offPt a).1 = ((b : ℝ) : EReal) ∧
      ((offPt a).2 = ⊥ ∨ (offPt a).2 ≤ ((B - 2 * ε : ℝ) : EReal))} ⊆
      {a : offD (mult (rankFn stageX JX)) | (offPt a).1 = ((b : ℝ) : EReal) ∧
      ((offPt a).2 = ⊥ ∨ (offPt a).2 < ((B - 2 * ε + θ : ℝ) : EReal))} := by
    rintro a ⟨h1, h2 | h2⟩
    · exact ⟨h1, Or.inl h2⟩
    · exact ⟨h1, Or.inr (lt_of_le_of_lt h2 (EReal.coe_lt_coe_iff.mpr (by linarith)))⟩
  
  have hsubI : {a : offD (mult (rankFn (trS stageX α) (imJ φ))) |
      (offPt a).1 = ((b : ℝ) : EReal) ∧
      ((offPt a).2 = ⊥ ∨ (offPt a).2 < ((B + θ : ℝ) : EReal))} ⊆
      {a : offD (mult (rankFn (trS stageX α) (imJ φ))) | (offPt a).1 = ((b : ℝ) : EReal) ∧
      ((offPt a).2 = ⊥ ∨ (offPt a).2 ≤ ((B : ℝ) : EReal))} := by
    rintro a ⟨h1, h2 | h2⟩
    · exact ⟨h1, Or.inl h2⟩
    · refine ⟨h1, Or.inr ?_⟩
      by_contra hgt
      push_neg at hgt
      have hez : (((offPt a).2.toReal : ℝ) : EReal) = (offPt a).2 :=
        EReal.coe_toReal (ne_top_of_lt h2) (ne_bot_of_gt hgt)
      rw [← hez] at h2 hgt
      have hd1 := EReal.coe_lt_coe_iff.mp hgt
      have hd2 := EReal.coe_lt_coe_iff.mp h2
      have hcrit : (offPt a).2.toReal ∈ (critSet hTI : Set ℝ) := by
        by_contra hzn
        have h0 := t3_death_pin hLI hTI (b := b) (d := (offPt a).2.toReal) (by linarith) hzn
        have hpt : offPt a = (((b : ℝ) : EReal), (((offPt a).2.toReal : ℝ) : EReal)) :=
          Prod.ext h1 hez.symm
        have hlt : ((a.1.2 : ℕ) : ℕ∞) <
            mult (rankFn (trS stageX α) (imJ φ)) (offPt a) := a.2
        rw [hpt, h0] at hlt
        exact absurd hlt (not_lt.mpr zero_le)
      have hne : (offPt a).2.toReal ≠ B := by linarith
      have := hgI _ (Finset.mem_coe.mp hcrit) hne
      rw [abs_of_pos (by linarith)] at this
      linarith
  calc _ ≤ _ := Set.encard_le_encard hsubX
    _ = bornCount hLawX b (B - 2 * ε + θ) := hX
    _ ≤ bornCount hLI b (B + θ) := qTop
    _ = _ := hI.symm
    _ ≤ _ := Set.encard_le_encard hsubI


noncomputable def jlo (α : ℝ) (p : EReal × EReal) : ℝ :=
  if p.2 ≤ ((α : ℝ) : EReal) then α else p.2.toReal

noncomputable def jhi (α ε : ℝ) (p : EReal × EReal) : ℝ :=
  if p.2 = ⊥ then α + ε else
    if p.2 ≤ ((α : ℝ) : EReal) then max (α + ε) (p.2.toReal + 2 * ε) else p.2.toReal + 2 * ε

def JDem (α ε κ b : ℝ) (p : EReal × EReal) : Prop :=
  p.1 = ((b : ℝ) : EReal) ∧ (p.2 = ⊥ ∨ (∃ d : ℝ, p.2 = ((d : ℝ) : EReal) ∧ d ≤ α ∧ d + 2 * ε < b) ∨
    (∃ d : ℝ, p.2 = ((d : ℝ) : EReal) ∧ α + κ ≤ d ∧ d + 2 * ε + κ ≤ b))

theorem jlo_of_le {α : ℝ} {p : EReal × EReal} (h : p.2 ≤ ((α : ℝ) : EReal)) : jlo α p = α := by
  simp only [jlo, if_pos h]

theorem jlo_of_gt {α d : ℝ} {p : EReal × EReal} (hp : p.2 = ((d : ℝ) : EReal)) (h : α < d) :
    jlo α p = d := by
  have hn : ¬ p.2 ≤ ((α : ℝ) : EReal) := by
    rw [hp]; exact not_le.mpr (EReal.coe_lt_coe_iff.mpr h)
  unfold jlo; rw [if_neg hn, hp, EReal.toReal_coe]

theorem jdem_facts {α ε κ b : ℝ} (hε : 0 ≤ ε) (hκ : 0 < κ) (hb : α + ε < b) {p : EReal × EReal}
    (hp : JDem α ε κ b p) :
    jlo α p ≤ jhi α ε p ∧ jhi α ε p < b ∧
    (∀ B : ℝ, α + ε ≤ B → jhi α ε p ≤ B → p.2 = ⊥ ∨ p.2 ≤ ((B - 2 * ε : ℝ) : EReal)) ∧
    (∀ A : ℝ, α < A → A ≤ jlo α p → ∃ d : ℝ, p.2 = ((d : ℝ) : EReal) ∧ A ≤ d ∧
      jhi α ε p = d + 2 * ε ∧ α + κ ≤ d ∧ d + 2 * ε + κ ≤ b) := by
  obtain ⟨-, hbot | ⟨d, hd, hdα, hdb⟩ | ⟨d, hd, hdα, hdb⟩⟩ := hp
  · have hle : p.2 ≤ ((α : ℝ) : EReal) := by rw [hbot]; exact bot_le
    have hhi : jhi α ε p = α + ε := by simp only [jhi, if_pos hbot]
    rw [jlo_of_le hle, hhi]
    refine ⟨by linarith, hb, fun B _ _ => Or.inl hbot, fun A hA hAl => ?_⟩
    linarith
  · have hle : p.2 ≤ ((α : ℝ) : EReal) := by rw [hd]; exact EReal.coe_le_coe_iff.mpr hdα
    have hnb : p.2 ≠ ⊥ := by rw [hd]; exact EReal.coe_ne_bot d
    have hhi : jhi α ε p = max (α + ε) (d + 2 * ε) := by
      unfold jhi; rw [if_neg hnb, if_pos hle, hd, EReal.toReal_coe]
    have x1 : α + ε ≤ max (α + ε) (d + 2 * ε) := le_max_left _ _
    have x2 : d + 2 * ε ≤ max (α + ε) (d + 2 * ε) := le_max_right _ _
    rw [jlo_of_le hle, hhi]
    refine ⟨by linarith, max_lt (by linarith) (by linarith), fun B _ hB => Or.inr ?_,
      fun A hA hAl => ?_⟩
    · rw [hd]; exact EReal.coe_le_coe_iff.mpr (by linarith)
    · linarith
  · have hgt : α < d := by linarith
    have hnb : p.2 ≠ ⊥ := by rw [hd]; exact EReal.coe_ne_bot d
    have hnle : ¬ p.2 ≤ ((α : ℝ) : EReal) := by
      rw [hd]; exact not_le.mpr (EReal.coe_lt_coe_iff.mpr hgt)
    have hhi : jhi α ε p = d + 2 * ε := by
      unfold jhi; rw [if_neg hnb, if_neg hnle, hd, EReal.toReal_coe]
    rw [jlo_of_gt hd hgt, hhi]
    refine ⟨by linarith, by linarith, fun B _ hB => Or.inr ?_,
      fun A hA hAl => ⟨d, hd, hAl, rfl, hdα, hdb⟩⟩
    rw [hd]; exact EReal.coe_le_coe_iff.mpr (by linarith)

theorem jhi_ge {α ε κ b : ℝ} (hε : 0 ≤ ε) (hκ : 0 < κ) {p : EReal × EReal}
    (hp : JDem α ε κ b p) : α + ε ≤ jhi α ε p := by
  obtain ⟨-, hbot | ⟨d, hd, hdα', -⟩ | ⟨d, hd, hdα, -⟩⟩ := hp
  · simp only [jhi, if_pos hbot, le_refl]
  · have hle : p.2 ≤ ((α : ℝ) : EReal) := by
      rw [hd]; exact EReal.coe_le_coe_iff.mpr hdα'
    have hnb : p.2 ≠ ⊥ := by rw [hd]; exact EReal.coe_ne_bot d
    unfold jhi; rw [if_neg hnb, if_pos hle]
    exact le_max_left _ _
  · have hnb : p.2 ≠ ⊥ := by rw [hd]; exact EReal.coe_ne_bot d
    have hnle : ¬ p.2 ≤ ((α : ℝ) : EReal) := by
      rw [hd]; exact not_le.mpr (EReal.coe_lt_coe_iff.mpr (by linarith))
    unfold jhi; rw [if_neg hnb, if_neg hnle, hd, EReal.toReal_coe]
    linarith

theorem exists_bound_below {T : Type} (f : T → ℝ) {c b : ℝ} (hcb : c < b) (s : Set T)
    (hs : s.Finite) (hf : ∀ x ∈ s, f x < b) : ∃ H : ℝ, c ≤ H ∧ H < b ∧ ∀ x ∈ s, f x ≤ H := by
  classical
  obtain ⟨t, rfl⟩ := hs.exists_finset_coe
  induction t using Finset.induction with
  | empty => exact ⟨c, le_rfl, hcb, fun x hx => absurd hx (Finset.notMem_empty x)⟩
  | insert y t hyt ih =>
    obtain ⟨H, h1, h2, h3⟩ := ih (Finset.finite_toSet t) (fun x hx => hf x (Finset.mem_coe.mpr
      (Finset.mem_insert_of_mem (Finset.mem_coe.mp hx))))
    have hy := hf y (Finset.mem_coe.mpr (Finset.mem_insert_self y t))
    refine ⟨max H (f y), le_trans h1 (le_max_left _ _), max_lt h2 hy, fun x hx => ?_⟩
    rcases Finset.mem_insert.mp (Finset.mem_coe.mp hx) with rfl | hx
    · exact le_max_right _ _
    · exact le_trans (h3 x (Finset.mem_coe.mpr hx)) (le_max_left _ _)

theorem eJointHall_b {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameX : IsTameModule stageX JX) (hTameY : IsTameModule stageY JY) {α ε : ℝ}
    (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x))
    (hSq4 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (x : comps stageX JX β),
      ψ (β - ε) hβε (φ β hβ x) = structMap hLawX (show (β - ε) - ε ≤ β by linarith) x)
    {κ b : ℝ} (hκ : 0 < κ) (hb : α + ε < b)
    (s : Set {x : offD (mult (rankFn stageX JX)) // JDem α ε κ b (offPt x)}) (hs : s.Finite) :
    s.encard ≤ (⋃ x ∈ s, {q : {q : offD (mult (rankFn (trS stageX α) (imJ φ))) //
        (offPt q).1 = ((b : ℝ) : EReal)} |
      jlo α (offPt x.1) ≤ jlo α (offPt q.1) ∧ jlo α (offPt q.1) ≤ jhi α ε (offPt x.1)}).encard := by
  refine interval_hall
    (X := {x : offD (mult (rankFn stageX JX)) // JDem α ε κ b (offPt x)})
    (Q := {q : offD (mult (rankFn (trS stageX α) (imJ φ))) // (offPt q).1 = ((b : ℝ) : EReal)})
    (fun x => jlo α (offPt x.1)) (fun x => jhi α ε (offPt x.1))
    (fun q => jlo α (offPt q.1)) s hs
    (fun x _ => (jdem_facts hε hκ hb x.2).1) ?_
  intro A B hAB
  
  have himg : ∀ (I : Set (offD (mult (rankFn (trS stageX α) (imJ φ))))),
      (∀ q ∈ I, (offPt q).1 = ((b : ℝ) : EReal) ∧ A ≤ jlo α (offPt q) ∧ jlo α (offPt q) ≤ B) →
      I.encard ≤ {q : {q : offD (mult (rankFn (trS stageX α) (imJ φ))) //
          (offPt q).1 = ((b : ℝ) : EReal)} |
        A ≤ jlo α (offPt q.1) ∧ jlo α (offPt q.1) ≤ B}.encard := by
    intro I hI
    refine le_trans (Set.encard_le_encard (t := Subtype.val '' {q : {q : offD (mult (rankFn
      (trS stageX α) (imJ φ))) // (offPt q).1 = ((b : ℝ) : EReal)} |
        A ≤ jlo α (offPt q.1) ∧ jlo α (offPt q.1) ≤ B}) ?_)
      (Subtype.val_injective.encard_image _).le
    intro q hq
    obtain ⟨h1, h2, h3⟩ := hI q hq
    exact ⟨⟨q, h1⟩, ⟨h2, h3⟩, rfl⟩
  by_cases hA : α < A
  · 
    by_cases hAB' : max A (α + κ) ≤ min (B - 2 * ε) (b - 2 * ε - κ)
    · have a1 : A ≤ max A (α + κ) := le_max_left _ _
      have a2 : α + κ ≤ max A (α + κ) := le_max_right _ _
      have b1 : min (B - 2 * ε) (b - 2 * ε - κ) ≤ B - 2 * ε := min_le_left _ _
      have b2 : min (B - 2 * ε) (b - 2 * ε - κ) ≤ b - 2 * ε - κ := min_le_right _ _
      have hE := eCore hLawX hLawY hTameX hTameY hε φ ψ hSq1 hSq4 (b := b)
        (A := max A (α + κ)) (B := min (B - 2 * ε) (b - 2 * ε - κ)) (by linarith) hAB'
        (by linarith)
      refine le_trans ?_ (le_trans hE (himg _ ?_))
      · refine Set.encard_le_encard_of_injOn (f := fun x => x.1) ?_
          (fun x₁ _ x₂ _ h => Subtype.ext h)
        rintro x ⟨-, hxl, hxh⟩
        obtain ⟨d, hd, hAd, hhi, hdα, hdb⟩ := (jdem_facts hε hκ hb x.2).2.2.2 A hA hxl
        refine ⟨x.2.1, ?_, ?_⟩
        · rw [hd]; exact EReal.coe_le_coe_iff.mpr (max_le hAd hdα)
        · rw [hd]; exact EReal.coe_le_coe_iff.mpr (le_min (by linarith) (by linarith))
      · rintro q ⟨h1, h2, h3⟩
        have hez : (((offPt q).2.toReal : ℝ) : EReal) = (offPt q).2 :=
          EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) h3)
            (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h2)
        rw [← hez] at h2 h3
        have r2 := EReal.coe_le_coe_iff.mp h2
        have r3 := EReal.coe_le_coe_iff.mp h3
        rw [jlo_of_gt hez.symm (by linarith)]
        exact ⟨h1, by linarith, by linarith⟩
    · have hempty : {x ∈ s | A ≤ jlo α (offPt x.1) ∧ jhi α ε (offPt x.1) ≤ B} = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => hAB' ?_
        obtain ⟨-, hxl, hxh⟩ := hx
        obtain ⟨d, -, hAd, hhi, hdα, hdb⟩ := (jdem_facts hε hκ hb x.2).2.2.2 A hA hxl
        exact le_trans (max_le hAd hdα) (le_min (by linarith) (by linarith))
      rw [hempty, Set.encard_empty]
      exact zero_le
  · push_neg at hA
    by_cases hB : α + ε ≤ B
    · 
      obtain ⟨H, hH1, hH2, hH3⟩ := exists_bound_below (fun x => jhi α ε (offPt x.1)) hb s hs
        (fun x _ => (jdem_facts hε hκ hb x.2).2.1)
      have c1 : min B H ≤ B := min_le_left _ _
      have c2 : min B H ≤ H := min_le_right _ _
      have c3 : α + ε ≤ min B H := le_min hB hH1
      have hL := eLow hLawX hLawY hTameX hTameY hε φ ψ hSq1 hSq4 (b := b) (B := min B H)
        c3 (by linarith)
      refine le_trans ?_ (le_trans hL (himg _ ?_))
      · refine Set.encard_le_encard_of_injOn (f := fun x => x.1) ?_
          (fun x₁ _ x₂ _ h => Subtype.ext h)
        rintro x ⟨hxs, -, hxh⟩
        exact ⟨x.2.1, (jdem_facts hε hκ hb x.2).2.2.1 (min B H) c3
          (le_min hxh (hH3 x hxs))⟩
      · rintro q ⟨h1, h2 | h2⟩
        · have hle : (offPt q).2 ≤ ((α : ℝ) : EReal) := by rw [h2]; exact bot_le
          rw [jlo_of_le hle]
          exact ⟨h1, hA, by linarith⟩
        · by_cases hq : (offPt q).2 ≤ ((α : ℝ) : EReal)
          · rw [jlo_of_le hq]
            exact ⟨h1, hA, by linarith⟩
          · push_neg at hq
            have hez : (((offPt q).2.toReal : ℝ) : EReal) = (offPt q).2 :=
              EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) h2)
                (ne_bot_of_gt hq)
            rw [← hez] at h2 hq
            have r2 := EReal.coe_le_coe_iff.mp h2
            have rq := EReal.coe_lt_coe_iff.mp hq
            rw [jlo_of_gt hez.symm rq]
            exact ⟨h1, by linarith, by linarith⟩
    · push_neg at hB
      have hempty : {x ∈ s | A ≤ jlo α (offPt x.1) ∧ jhi α ε (offPt x.1) ≤ B} = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
        obtain ⟨-, -, hxh⟩ := hx
        have := jhi_ge hε hκ x.2
        linarith
      rw [hempty, Set.encard_empty]
      exact zero_le

theorem encard_split_pred {S : Type} (s : Set S) (p : S -> Prop) :
    s.encard = {a ∈ s | p a}.encard + {a ∈ s | ¬ p a}.encard := by
  rw [← Set.encard_union_eq]
  · congr 1
    ext a
    by_cases h : p a <;> simp [h]
  · rw [Set.disjoint_left]
    intro a h1 h2
    exact h2.2 h1.2

theorem fiber_union_disjoint {S T K : Type} (κ : S → K) (G : S → Set T)
    (hdisj : ∀ a a' : S, κ a ≠ κ a' → G a ∩ G a' = ∅) (s₁ s₂ : Set S)
    (h : ∀ a ∈ s₁, ∀ a' ∈ s₂, κ a ≠ κ a') :
    Disjoint (⋃ x ∈ s₁, G x) (⋃ x ∈ s₂, G x) := by
  rw [Set.disjoint_left]
  intro t h1 h2
  simp only [Set.mem_iUnion] at h1 h2
  obtain ⟨a, ha, hta⟩ := h1
  obtain ⟨a', ha', hta'⟩ := h2
  have := hdisj a a' (h a ha a' ha')
  have hmem : t ∈ G a ∩ G a' := ⟨hta, hta'⟩
  rw [this] at hmem
  exact hmem

theorem fiber_union_split {S T : Type} (G : S → Set T) (s : Set S) (p : S -> Prop) :
    (⋃ x ∈ s, G x) = (⋃ x ∈ {a ∈ s | p a}, G x) ∪ (⋃ x ∈ {a ∈ s | ¬ p a}, G x) := by
  rw [← Set.biUnion_union]
  congr 1
  ext a
  by_cases h : p a <;> simp [h]

theorem hall_of_classes_aux {S T K : Type} (κ : S → K) (G : S → Set T)
    (hdisj : ∀ a a' : S, κ a ≠ κ a' → G a ∩ G a' = ∅)
    (hclass : ∀ s : Set S, s.Finite → (∀ a ∈ s, ∀ a' ∈ s, κ a = κ a') →
      s.encard ≤ (⋃ x ∈ s, G x).encard) (F : Finset K) :
    ∀ s : Set S, s.Finite → κ '' s ⊆ ↑F → s.encard ≤ (⋃ x ∈ s, G x).encard := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    intro s _ hsub
    have : s = ∅ := by
      rw [← Set.image_eq_empty (f := κ)]
      simpa using hsub
    subst this
    simp
  | insert k F _ ih =>
    intro s hs hsub
    rw [encard_split_pred s (fun a => κ a = k), fiber_union_split G s (fun a => κ a = k),
      Set.encard_union_eq (fiber_union_disjoint κ G hdisj _ _ ?_)]
    · apply add_le_add
      · apply hclass _ (hs.subset (fun a h => h.1))
        intro a ha a' ha'
        rw [ha.2, ha'.2]
      · apply ih _ (hs.subset (fun a h => h.1))
        rintro _ ⟨a, ha, rfl⟩
        have := hsub ⟨a, ha.1, rfl⟩
        simp only [Finset.coe_insert, Set.mem_insert_iff] at this
        exact this.resolve_left ha.2
    · intro a ha a' ha'
      rw [ha.2]
      exact fun h => ha'.2 h.symm

theorem hall_of_classes {S T K : Type} (κ : S → K) (G : S → Set T)
    (hdisj : ∀ a a' : S, κ a ≠ κ a' → G a ∩ G a' = ∅)
    (hclass : ∀ s : Set S, s.Finite → (∀ a ∈ s, ∀ a' ∈ s, κ a = κ a') →
      s.encard ≤ (⋃ x ∈ s, G x).encard) :
    ∀ s : Set S, s.Finite → s.encard ≤ (⋃ x ∈ s, G x).encard := by
  intro s hs
  exact hall_of_classes_aux κ G hdisj hclass (hs.image κ).toFinset s hs (by simp)


def JD (D : EReal × EReal → ℕ∞) (α ε κ : ℝ) : Type :=
  {x : offD D // ∃ b : ℝ, α + ε < b ∧ JDem α ε κ b (offPt x)}

noncomputable def JD.b {D : EReal × EReal → ℕ∞} {α ε κ : ℝ} (x : JD D α ε κ) : ℝ :=
  (offPt x.1).1.toReal

theorem JD.spec {D : EReal × EReal → ℕ∞} {α ε κ : ℝ} (x : JD D α ε κ) :
    α + ε < x.b ∧ JDem α ε κ x.b (offPt x.1) := by
  obtain ⟨b, hb, hJ⟩ := x.2
  have hxb : x.b = b := by
    show (offPt x.1).1.toReal = b
    rw [hJ.1]
    exact EReal.toReal_coe b
  rw [hxb]
  exact ⟨hb, hJ⟩

def JD.toJ {D : EReal × EReal → ℕ∞} {α ε κ : ℝ} (x : JD D α ε κ) :
    {x' : offD D // JDem α ε κ x.b (offPt x')} :=
  ⟨x.1, (JD.spec x).2⟩

theorem eGlobal {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameX : IsTameModule stageX JX) (hTameY : IsTameModule stageY JY) {α ε : ℝ}
    (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x))
    (hSq4 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (x : comps stageX JX β),
      ψ (β - ε) hβε (φ β hβ x) = structMap hLawX (show (β - ε) - ε ≤ β by linarith) x)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ E : JD (mult (rankFn stageX JX)) α ε κ → offD (mult (rankFn (trS stageX α) (imJ φ))),
      Function.Injective E ∧ ∀ x, (offPt (E x)).1 = (offPt x.1).1 ∧
        jlo α (offPt x.1) ≤ jlo α (offPt (E x)) ∧ jlo α (offPt (E x)) ≤ jhi α ε (offPt x.1) := by
  classical
  have hLI := imLaw hLawX hLawY φ hSq1
  have hTI := imTame hLawX hLawY hTameX hTameY φ hSq1
  haveI : Finite (offD (mult (rankFn (trS stageX α) (imJ φ)))) :=
    Set.finite_univ_iff.mp (t5_offD_finite hLI hTI)
  have hE : ∀ b : ℝ, α + ε < b → ∃ f : {x : offD (mult (rankFn stageX JX)) //
        JDem α ε κ b (offPt x)} → {q : offD (mult (rankFn (trS stageX α) (imJ φ))) //
          (offPt q).1 = ((b : ℝ) : EReal)},
      Function.Injective f ∧ ∀ x, f x ∈ {q : {q : offD (mult (rankFn (trS stageX α) (imJ φ))) //
          (offPt q).1 = ((b : ℝ) : EReal)} |
        jlo α (offPt x.1) ≤ jlo α (offPt q.1) ∧ jlo α (offPt q.1) ≤ jhi α ε (offPt x.1)} :=
    fun b hb => t5_hallChoice _ (fun _ => Set.toFinite _)
      (fun s hs => eJointHall_b hLawX hLawY hTameX hTameY hε φ ψ hSq1 hSq4 hκ hb s hs)
  choose f hfinj hfmem using hE
  refine ⟨fun x => (f x.b (JD.spec x).1 x.toJ).1, ?_, fun x => ?_⟩
  · intro x x' hxx
    have key : ∀ (b₁ b₂ : ℝ) (h : b₁ = b₂) (h₁ : α + ε < b₁) (h₂ : α + ε < b₂)
        (y₁ : {x : offD (mult (rankFn stageX JX)) // JDem α ε κ b₁ (offPt x)})
        (y₂ : {x : offD (mult (rankFn stageX JX)) // JDem α ε κ b₂ (offPt x)}),
        (f b₁ h₁ y₁).1 = (f b₂ h₂ y₂).1 → y₁.1 = y₂.1 := by
      intro b₁ b₂ h h₁ h₂ y₁ y₂ hq
      subst h
      exact congrArg Subtype.val (hfinj b₁ h₁ (Subtype.ext hq))
    have hb1 := (f x.b (JD.spec x).1 x.toJ).2
    have hb2 := (f x'.b (JD.spec x').1 x'.toJ).2
    simp only at hxx
    rw [hxx] at hb1
    rw [hb1] at hb2
    exact Subtype.ext (key _ _ (EReal.coe_injective hb2) _ _ x.toJ x'.toJ hxx)
  · obtain ⟨h1, h2⟩ := hfmem x.b (JD.spec x).1 x.toJ
    refine ⟨?_, h1, h2⟩
    rw [(f x.b (JD.spec x).1 x.toJ).2, (JD.spec x).2.1]

theorem copies_low_open_closed {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) (P Q v : ℝ) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ →
      P - η ∉ (critSet hTame : Set ℝ) ∧ Q + η ∉ (critSet hTame : Set ℝ) ∧
      (v ≤ P - η → ∀ a : offD (mult (rankFn stage J)), ((P - η : ℝ) : EReal) < (offPt a).1 →
        (offPt a).1 < ((Q + η : ℝ) : EReal) →
        ((offPt a).2 = ⊥ ∨ (offPt a).2 < ((v : ℝ) : EReal)) →
        ((P : ℝ) : EReal) ≤ (offPt a).1 ∧ (offPt a).1 ≤ ((Q : ℝ) : EReal)) := by
  obtain ⟨δL, hδL, -, hgL⟩ := t3_gapEx (critSet hTame) one_pos P
  obtain ⟨δR, hδR, -, hgR⟩ := t3_gapEx (critSet hTame) one_pos Q
  refine ⟨min δL δR, lt_min hδL hδR, fun η hη hη₀ => ?_⟩
  have hθL : η < δL := lt_of_lt_of_le hη₀ (min_le_left _ _)
  have hθR : η < δR := lt_of_lt_of_le hη₀ (min_le_right _ _)
  have nearL : ∀ τ ∈ (critSet hTame : Set ℝ), |τ - P| < δL → τ = P := by
    intro τ hτ hlt
    by_contra hne
    exact absurd (hgL τ (Finset.mem_coe.mp hτ) hne) (not_lt.mpr hlt.le)
  have nearR : ∀ τ ∈ (critSet hTame : Set ℝ), |τ - Q| < δR → τ = Q := by
    intro τ hτ hlt
    by_contra hne
    exact absurd (hgR τ (Finset.mem_coe.mp hτ) hne) (not_lt.mpr hlt.le)
  refine ⟨fun hc => ?_, fun hc => ?_, fun hvP a hlo hhi hd => ?_⟩
  · have := nearL _ hc (by rw [show P - η - P = -η by ring, abs_neg, abs_of_pos hη]; exact hθL)
    linarith
  · have := nearR _ hc (by rw [show Q + η - Q = η by ring, abs_of_pos hη]; exact hθR)
    linarith
  have heb : (((offPt a).1.toReal : ℝ) : EReal) = (offPt a).1 :=
    EReal.coe_toReal (ne_top_of_lt hhi) (ne_bot_of_gt hlo)
  rw [← heb] at hlo hhi ⊢
  have hb1 := EReal.coe_lt_coe_iff.mp hlo
  have hb2 := EReal.coe_lt_coe_iff.mp hhi
  have hcrit : (offPt a).1.toReal ∈ (critSet hTame : Set ℝ) := by
    by_contra hbn
    have hlt : ((a.1.2 : ℕ) : ℕ∞) < mult (rankFn stage J) (offPt a) := a.2
    by_cases hbot : (offPt a).2 = ⊥
    · have hpt : offPt a = ((((offPt a).1.toReal : ℝ) : EReal), (⊥ : EReal)) :=
        Prod.ext heb.symm hbot
      rw [hpt, t3_ess_pin hLaw hTame hbn] at hlt
      exact absurd hlt (not_lt.mpr zero_le)
    · have hdv : (offPt a).2 < ((v : ℝ) : EReal) := hd.resolve_left hbot
      have hed : (((offPt a).2.toReal : ℝ) : EReal) = (offPt a).2 :=
        EReal.coe_toReal (ne_top_of_lt hdv) hbot
      have hdv' : (offPt a).2.toReal < v := EReal.coe_lt_coe_iff.mp (by rw [hed]; exact hdv)
      have hpt : offPt a = ((((offPt a).1.toReal : ℝ) : EReal),
          (((offPt a).2.toReal : ℝ) : EReal)) := Prod.ext heb.symm hed.symm
      rw [hpt, t3_birth_pin hLaw hTame (by linarith) hbn] at hlt
      exact absurd hlt (not_lt.mpr zero_le)
  refine ⟨EReal.coe_le_coe_iff.mpr ?_, EReal.coe_le_coe_iff.mpr ?_⟩
  · by_contra hlt
    push_neg at hlt
    have := nearL _ hcrit (abs_lt.mpr ⟨by linarith, by linarith⟩)
    linarith
  · by_contra hlt
    push_neg at hlt
    have := nearR _ hcrit (abs_lt.mpr ⟨by linarith, by linarith⟩)
    linarith

def ILow (D : EReal × EReal → ℕ∞) (α ε κ : ℝ) : Type :=
  {q : offD D // ((offPt q).2 = ⊥ ∨ (offPt q).2 ≤ ((α : ℝ) : EReal)) ∧
    ∃ b : ℝ, (offPt q).1 = ((b : ℝ) : EReal) ∧ α + ε + κ ≤ b}

noncomputable def ILow.b {D : EReal × EReal → ℕ∞} {α ε κ : ℝ} (q : ILow D α ε κ) : ℝ :=
  (offPt q.1).1.toReal

theorem ILow.spec {D : EReal × EReal → ℕ∞} {α ε κ : ℝ} (q : ILow D α ε κ) :
    ((offPt q.1).2 = ⊥ ∨ (offPt q.1).2 ≤ ((α : ℝ) : EReal)) ∧
      (offPt q.1).1 = ((q.b : ℝ) : EReal) ∧ α + ε + κ ≤ q.b := by
  obtain ⟨hd, b, hp, h1⟩ := q.2
  have hb : q.b = b := by
    show (offPt q.1).1.toReal = b
    rw [hp]
    exact EReal.toReal_coe b
  rw [hb]
  exact ⟨hd, hp, h1⟩

theorem lowCore {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameX : IsTameModule stageX JX) (hTameY : IsTameModule stageY JY) {α ε : ℝ}
    (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x))
    (hSq3 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (y : comps stageY JY β),
      φ (β - ε) hβε (ψ β hβ y) =
        structMap hLawY (show (β - ε) - ε ≤ β by linarith) y)
    {θ : ℝ} (hθ : 0 < θ)
    (hgapI : ∀ τ ∈ critSet (imTame hLawX hLawY hTameX hTameY φ hSq1), τ ≤ α ∨ α + θ < τ)
    (hgY : α + θ - ε ∉ (critSet hTameY : Set ℝ)) {L R : ℝ} (huL : α + θ < L) (hLR : L ≤ R) :
    {a : offD (mult (rankFn (trS stageX α) (imJ φ))) | ((L : ℝ) : EReal) ≤ (offPt a).1 ∧
        (offPt a).1 ≤ ((R : ℝ) : EReal) ∧
        ((offPt a).2 = ⊥ ∨ (offPt a).2 ≤ ((α : ℝ) : EReal))}.encard ≤
      {y : offD (mult (rankFn stageY JY)) | ((L - ε : ℝ) : EReal) ≤ (offPt y).1 ∧
        (offPt y).1 ≤ ((R + ε : ℝ) : EReal) ∧
        ((offPt y).2 = ⊥ ∨ (offPt y).2 < ((α + θ - ε : ℝ) : EReal))}.encard := by
  have hLI := imLaw hLawX hLawY φ hSq1
  have hTI := imTame hLawX hLawY hTameX hTameY φ hSq1
  have hu : α + θ ∉ (critSet hTI : Set ℝ) := fun h => by
    rcases hgapI _ h with h | h <;> linarith
  obtain ⟨η₀, hη₀, hI⟩ := copies_low_open_closed hLI hTI L R (α + θ)
  obtain ⟨η₁, hη₁, hY⟩ := copies_low_open_closed hLawY hTameY (L - ε) (R + ε) (α + θ - ε)
  have hm1 : min (min η₀ η₁) (L - (α + θ)) ≤ min η₀ η₁ := min_le_left _ _
  have hm2 : min (min η₀ η₁) (L - (α + θ)) ≤ L - (α + θ) := min_le_right _ _
  have hm3 : min η₀ η₁ ≤ η₀ := min_le_left _ _
  have hm4 : min η₀ η₁ ≤ η₁ := min_le_right _ _
  have hm0 : 0 < min (min η₀ η₁) (L - (α + θ)) := lt_min (lt_min hη₀ hη₁) (by linarith)
  obtain ⟨η, hηdef⟩ : ∃ η, η = min (min η₀ η₁) (L - (α + θ)) / 2 := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; linarith
  have hηI : η < η₀ := by rw [hηdef]; linarith
  have hηY : η < η₁ := by rw [hηdef]; linarith
  have hηu : η < L - (α + θ) := by rw [hηdef]; linarith
  obtain ⟨hIL, hIR, -⟩ := hI η hη hηI
  obtain ⟨hYL, hYR, hYsub⟩ := hY η hη hηY
  have cI := copies_level_window hLI hTI (L := L - η) (R := R + η) (u := α + θ)
    (by linarith) (by linarith) hIL hIR hu
  have cY := copies_level_window hLawY hTameY (L := L - ε - η) (R := R + ε + η)
    (u := α + θ - ε) (by linarith) (by linarith) hYL hYR hgY
  have hC := lowLevelCensus hLawX hLawY hε φ ψ hSq1 hSq3 (u := α + θ) (L := L - η)
    (R := R + η) (by linarith) (by linarith) (by linarith) (by linarith)
  rw [max_eq_left (by linarith : α ≤ α + θ), show L - η - ε = L - ε - η by ring,
    show R + η + ε = R + ε + η by ring] at hC
  have dI := Set.encard_diff_add_encard_of_subset
    (cwd_meet_anti hLI (t := α + θ) (show L - η ≤ R + η by linarith))
  have dY := Set.encard_diff_add_encard_of_subset
    (cwd_meet_anti hLawY (t := α + θ - ε) (show L - ε - η ≤ R + ε + η by linarith))
  have s1 := (ENat.add_le_add_iff_right (meetSet_encard_ne_top hTI _ _)).mp
    (le_of_eq (cI.trans dI.symm))
  have s2 := (ENat.add_le_add_iff_right (meetSet_encard_ne_top hTameY _ _)).mp
    (le_of_eq (dY.trans cY.symm))
  refine le_trans (Set.encard_le_encard ?_)
    (le_trans s1 (le_trans hC (le_trans s2 (Set.encard_le_encard ?_))))
  · rintro a ⟨h1, h2, h3⟩
    refine ⟨lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr (by linarith)) h1,
      lt_of_le_of_lt h2 (EReal.coe_lt_coe_iff.mpr (by linarith)), ?_⟩
    exact h3.imp id (fun h => lt_of_le_of_lt h (EReal.coe_lt_coe_iff.mpr (by linarith)))
  · rintro y ⟨h1, h2, h3⟩
    obtain ⟨k1, k2⟩ := hYsub (by linarith) y h1 h2 h3
    exact ⟨k1, k2, h3⟩

theorem mLowHall {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameX : IsTameModule stageX JX) (hTameY : IsTameModule stageY JY) {α ε : ℝ}
    (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x))
    (hSq3 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (y : comps stageY JY β),
      φ (β - ε) hβε (ψ β hβ y) =
        structMap hLawY (show (β - ε) - ε ≤ β by linarith) y)
    {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ) (hθεκ : θ < ε + κ)
    (hgapI : ∀ τ ∈ critSet (imTame hLawX hLawY hTameX hTameY φ hSq1), τ ≤ α ∨ α + θ < τ)
    (hgY : α + θ - ε ∉ (critSet hTameY : Set ℝ))
    (s : Set (ILow (mult (rankFn (trS stageX α) (imJ φ))) α ε κ)) (hs : s.Finite) :
    s.encard ≤ (⋃ q ∈ s, {y : offD (mult (rankFn stageY JY)) |
      ((q.b - ε : ℝ) : EReal) ≤ (offPt y).1 ∧ (offPt y).1 ≤ ((q.b + ε : ℝ) : EReal) ∧
        ((offPt y).2 = ⊥ ∨ (offPt y).2 < ((α + θ - ε : ℝ) : EReal))}).encard := by
  refine t5_cluster_chop ε hε (fun q => q.b) s hs _
    (fun L R => {y : offD (mult (rankFn stageY JY)) |
      ((L - ε : ℝ) : EReal) ≤ (offPt y).1 ∧ (offPt y).1 ≤ ((R + ε : ℝ) : EReal) ∧
        ((offPt y).2 = ⊥ ∨ (offPt y).2 < ((α + θ - ε : ℝ) : EReal))}) ?_ ?_ ?_ ?_
  · 
    intro L R hLR
    by_cases hAB : max L (α + ε + κ) ≤ R
    · have a1 : L ≤ max L (α + ε + κ) := le_max_left _ _
      have a2 : α + ε + κ ≤ max L (α + ε + κ) := le_max_right _ _
      have hM := lowCore hLawX hLawY hTameX hTameY hε φ ψ hSq1 hSq3 hθ hgapI hgY
        (L := max L (α + ε + κ)) (R := R) (by linarith) hAB
      refine le_trans ?_ (le_trans hM (Set.encard_le_encard ?_))
      · refine Set.encard_le_encard_of_injOn (f := fun q => q.1) ?_
          (fun q₁ _ q₂ _ h => Subtype.ext h)
        intro q hq
        obtain ⟨hd, hp, h1⟩ := q.spec
        obtain ⟨hq1, hq2⟩ := hq
        refine ⟨?_, ?_, hd⟩
        · rw [hp]
          exact EReal.coe_le_coe_iff.mpr (max_le hq1 h1)
        · rw [hp]
          exact EReal.coe_le_coe_iff.mpr hq2
      · rintro y ⟨hy1, hy2, hy3⟩
        exact ⟨le_trans (EReal.coe_le_coe_iff.mpr (by linarith)) hy1, hy2, hy3⟩
    · have hempty : {q : ILow (mult (rankFn (trS stageX α) (imJ φ))) α ε κ |
          L ≤ q.b ∧ q.b ≤ R} = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.mpr fun q hq => hAB ?_
        obtain ⟨-, -, h1⟩ := q.spec
        obtain ⟨hq1, hq2⟩ := hq
        exact le_trans (max_le hq1 h1) hq2
      rw [hempty, Set.encard_empty]
      exact zero_le
  · 
    rintro L R - q - hL hR y ⟨hy1, hy2, hy3⟩
    exact ⟨le_trans (EReal.coe_le_coe_iff.mpr (by linarith)) hy1,
      le_trans hy2 (EReal.coe_le_coe_iff.mpr (by linarith)), hy3⟩
  · 
    rintro L R - hwit y hy
    obtain ⟨hy1, hy2, hy3⟩ := hy
    have heb : (((offPt y).1.toReal : ℝ) : EReal) = (offPt y).1 :=
      EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) hy2)
        (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hy1)
    rw [← heb] at hy1 hy2
    obtain ⟨q, hqs, hqL, hqR, hqt⟩ := hwit _ (EReal.coe_le_coe_iff.mp hy1)
      (EReal.coe_le_coe_iff.mp hy2)
    obtain ⟨hlo, hhi⟩ := abs_le.mp hqt
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    refine ⟨q, ⟨hqs, hqL, hqR⟩, ?_, ?_, hy3⟩
    · rw [← heb]; exact EReal.coe_le_coe_iff.mpr (by linarith)
    · rw [← heb]; exact EReal.coe_le_coe_iff.mpr (by linarith)
  · 
    rintro q - q' - t hqt htq'
    refine Set.eq_empty_iff_forall_notMem.mpr fun y hy => ?_
    obtain ⟨⟨-, hy2, -⟩, ⟨hy4, -, -⟩⟩ := hy
    have := le_trans hy4 hy2
    have h := EReal.coe_le_coe_iff.mp this
    linarith


theorem hall_transfer {A B C T : Type} (vA : A → C) (vB : B → C)
    (hA : Function.Injective vA) (hB : Function.Injective vB)
    (GA : A → Set T) (GB : B → Set T) (sA : Set A) (sB : Set B)
    (himg : vA '' sA = vB '' sB) (hG : ∀ a b, vA a = vB b → GA a = GB b)
    (h : sB.encard ≤ (⋃ b ∈ sB, GB b).encard) :
    sA.encard ≤ (⋃ a ∈ sA, GA a).encard := by
  have h1 : sA.encard = sB.encard := by
    rw [← hA.encard_image, ← hB.encard_image, himg]
  have h2 : (⋃ a ∈ sA, GA a) = ⋃ b ∈ sB, GB b := by
    ext t
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨a, ha, ht⟩
      obtain ⟨b, hb, hba⟩ : vA a ∈ vB '' sB := himg ▸ ⟨a, ha, rfl⟩
      exact ⟨b, hb, (hG a b hba.symm) ▸ ht⟩
    · rintro ⟨b, hb, ht⟩
      obtain ⟨a, ha, hab⟩ : vB b ∈ vA '' sA := himg ▸ ⟨b, hb, rfl⟩
      exact ⟨a, ha, (hG a b hab).symm ▸ ht⟩
  rw [h1, h2]
  exact h

def IMD (D : EReal × EReal → ℕ∞) (α ε θ κ : ℝ) : Type :=
  {q : offD D // ∃ b : ℝ, (offPt q).1 = ((b : ℝ) : EReal) ∧
    ((((offPt q).2 = ⊥ ∨ (offPt q).2 ≤ ((α : ℝ) : EReal)) ∧ α + ε + κ ≤ b) ∨
      (∃ z : ℝ, (offPt q).2 = ((z : ℝ) : EReal) ∧ α + θ < z ∧ z + κ ≤ b))}

def GM {DY : EReal × EReal → ℕ∞} (α ε θ : ℝ) (p : EReal × EReal) : Set (offD DY) :=
  {y | ((p.1.toReal - ε : ℝ) : EReal) ≤ (offPt y).1 ∧ (offPt y).1 ≤ ((p.1.toReal + ε : ℝ) : EReal) ∧
    ((p.2 = ⊥ ∨ p.2 ≤ ((α : ℝ) : EReal)) → ((offPt y).2 = ⊥ ∨
      (offPt y).2 < ((α + θ - ε : ℝ) : EReal))) ∧
    (¬ (p.2 = ⊥ ∨ p.2 ≤ ((α : ℝ) : EReal)) → (offPt y).2 = ((p.2.toReal - ε : ℝ) : EReal))}

theorem mGlobal {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameX : IsTameModule stageX JX) (hTameY : IsTameModule stageY JY) {α ε : ℝ}
    (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x))
    (hSq3 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (y : comps stageY JY β),
      φ (β - ε) hβε (ψ β hβ y) =
        structMap hLawY (show (β - ε) - ε ≤ β by linarith) y)
    {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ) (hθεκ : θ < ε + κ)
    (hgapI : ∀ τ ∈ critSet (imTame hLawX hLawY hTameX hTameY φ hSq1), τ ≤ α ∨ α + θ < τ)
    (hgY : α + θ - ε ∉ (critSet hTameY : Set ℝ)) :
    ∃ M : IMD (mult (rankFn (trS stageX α) (imJ φ))) α ε θ κ → offD (mult (rankFn stageY JY)),
      Function.Injective M ∧ ∀ q, M q ∈ GM (DY := mult (rankFn stageY JY)) α ε θ (offPt q.1) := by
  classical
  haveI : Finite (offD (mult (rankFn stageY JY))) :=
    Set.finite_univ_iff.mp (t5_offD_finite hLawY hTameY)
  
  let cls : IMD (mult (rankFn (trS stageX α) (imJ φ))) α ε θ κ → EReal := fun q =>
    if (offPt q.1).2 ≤ ((α : ℝ) : EReal) then ⊥ else (offPt q.1).2
  have hlow : ∀ q : IMD (mult (rankFn (trS stageX α) (imJ φ))) α ε θ κ,
      ((offPt q.1).2 = ⊥ ∨ (offPt q.1).2 ≤ ((α : ℝ) : EReal)) ↔
        (offPt q.1).2 ≤ ((α : ℝ) : EReal) := fun q =>
    ⟨fun h => h.elim (fun h0 => by rw [h0]; exact bot_le) id, Or.inr⟩
  
  have hfin : ∀ q : IMD (mult (rankFn (trS stageX α) (imJ φ))) α ε θ κ,
      ¬ (offPt q.1).2 ≤ ((α : ℝ) : EReal) →
      ∃ z : ℝ, (offPt q.1).2 = ((z : ℝ) : EReal) ∧ α + θ < z := by
    intro q hq
    obtain ⟨b, -, hlo | ⟨z, hz, hzθ, -⟩⟩ := q.2
    · exact absurd ((hlow q).mp hlo.1) hq
    · exact ⟨z, hz, hzθ⟩
  refine t5_hallChoice
    (fun q : IMD (mult (rankFn (trS stageX α) (imJ φ))) α ε θ κ =>
      GM (DY := mult (rankFn stageY JY)) α ε θ (offPt q.1))
    (fun _ => Set.toFinite _) (hall_of_classes cls _ ?_ ?_)
  · 
    intro a a' hne
    refine Set.eq_empty_iff_forall_notMem.mpr fun y hy => hne ?_
    obtain ⟨⟨-, -, ha1, ha2⟩, ⟨-, -, ha1', ha2'⟩⟩ := hy
    by_cases hal : (offPt a.1).2 ≤ ((α : ℝ) : EReal)
    · by_cases hal' : (offPt a'.1).2 ≤ ((α : ℝ) : EReal)
      · simp only [cls, if_pos hal, if_pos hal']
      · exfalso
        obtain ⟨z, hz, hzθ⟩ := hfin a' hal'
        have hy2 := ha2' (fun h => hal' ((hlow a').mp h))
        rw [hz, EReal.toReal_coe] at hy2
        rcases ha1 ((hlow a).mpr hal) with h | h
        · rw [hy2] at h; exact EReal.coe_ne_bot _ h
        · rw [hy2] at h; have := EReal.coe_lt_coe_iff.mp h; linarith
    · by_cases hal' : (offPt a'.1).2 ≤ ((α : ℝ) : EReal)
      · exfalso
        obtain ⟨z, hz, hzθ⟩ := hfin a hal
        have hy2 := ha2 (fun h => hal ((hlow a).mp h))
        rw [hz, EReal.toReal_coe] at hy2
        rcases ha1' ((hlow a').mpr hal') with h | h
        · rw [hy2] at h; exact EReal.coe_ne_bot _ h
        · rw [hy2] at h; have := EReal.coe_lt_coe_iff.mp h; linarith
      · obtain ⟨z, hz, -⟩ := hfin a hal
        obtain ⟨z', hz', -⟩ := hfin a' hal'
        have hy2 := ha2 (fun h => hal ((hlow a).mp h))
        have hy2' := ha2' (fun h => hal' ((hlow a').mp h))
        rw [hz, EReal.toReal_coe] at hy2
        rw [hz', EReal.toReal_coe] at hy2'
        rw [hy2] at hy2'
        have hzz : z = z' := by have := EReal.coe_injective hy2'; linarith
        simp only [cls, if_neg hal, if_neg hal', hz, hz', hzz]
  · 
    intro s hs hcl
    rcases s.eq_empty_or_nonempty with h0 | ⟨q₀, hq₀⟩
    · rw [h0, Set.encard_empty]; exact zero_le
    by_cases hl₀ : (offPt q₀.1).2 ≤ ((α : ℝ) : EReal)
    · 
      have hall_low : ∀ q ∈ s, (offPt q.1).2 ≤ ((α : ℝ) : EReal) := by
        intro q hq
        by_contra hql
        have hc := hcl q hq q₀ hq₀
        simp only [cls, if_neg hql, if_pos hl₀] at hc
        obtain ⟨z, hz, -⟩ := hfin q hql
        rw [hz] at hc
        exact EReal.coe_ne_bot _ hc
      refine hall_transfer (fun q : IMD (mult (rankFn (trS stageX α) (imJ φ))) α ε θ κ => q.1)
        (fun y : ILow (mult (rankFn (trS stageX α) (imJ φ))) α ε κ => y.1)
        (fun _ _ h => Subtype.ext h) (fun _ _ h => Subtype.ext h) _ _ s
        {y | y.1 ∈ (fun q : IMD (mult (rankFn (trS stageX α) (imJ φ))) α ε θ κ => q.1) '' s} ?_ ?_
        (mLowHall hLawX hLawY hTameX hTameY hε φ ψ hSq1 hSq3 hθ hκ hθεκ hgapI hgY _
          (Set.Finite.preimage
            (f := fun y : ILow (mult (rankFn (trS stageX α) (imJ φ))) α ε κ => y.1)
            (fun _ _ _ _ h => Subtype.ext h) (hs.image (fun q : IMD (mult (rankFn (trS stageX α) (imJ φ))) α ε θ κ => q.1))))
      · ext c
        constructor
        · rintro ⟨q, hq, rfl⟩
          obtain ⟨b, hb, hlo | ⟨z, hz, hzθ, -⟩⟩ := q.2
          · exact ⟨⟨q.1, hlo.1, b, hb, hlo.2⟩, ⟨q, hq, rfl⟩, rfl⟩
          · exfalso
            have := hall_low q hq
            rw [hz] at this
            have := EReal.coe_le_coe_iff.mp this
            linarith
        · rintro ⟨y, ⟨q, hq, hqy⟩, rfl⟩
          exact ⟨q, hq, hqy⟩
      · intro q y hqy
        have hqlow : (offPt q.1).2 = ⊥ ∨ (offPt q.1).2 ≤ ((α : ℝ) : EReal) := by
          rw [hqy]; exact y.2.1
        ext w
        simp only [GM, Set.mem_setOf_eq, ILow.b, ← hqy]
        constructor
        · rintro ⟨h1, h2, h3, -⟩
          exact ⟨h1, h2, h3 hqlow⟩
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h1, h2, fun _ => h3, fun hn => absurd hqlow hn⟩
    · 
      obtain ⟨z, hz, hzθ⟩ := hfin q₀ hl₀
      have hall_z : ∀ q ∈ s, (offPt q.1).2 = ((z : ℝ) : EReal) := by
        intro q hq
        have hc := hcl q hq q₀ hq₀
        by_cases hql : (offPt q.1).2 ≤ ((α : ℝ) : EReal)
        · simp only [cls, if_pos hql, if_neg hl₀, hz] at hc
          exact absurd hc.symm (EReal.coe_ne_bot _)
        · simp only [cls, if_neg hql, if_neg hl₀] at hc
          rw [hc, hz]
      refine hall_transfer (fun q : IMD (mult (rankFn (trS stageX α) (imJ φ))) α ε θ κ => q.1)
        (fun y : IDz (mult (rankFn (trS stageX α) (imJ φ))) κ z => y.1)
        (fun _ _ h => Subtype.ext h) (fun _ _ h => Subtype.ext h) _ _ s
        {y | y.1 ∈ (fun q : IMD (mult (rankFn (trS stageX α) (imJ φ))) α ε θ κ => q.1) '' s} ?_ ?_
        (mHall_z hLawX hLawY hTameX hTameY hε φ ψ hSq1 hSq3 hκ (by linarith) _
          (Set.Finite.preimage
            (f := fun y : IDz (mult (rankFn (trS stageX α) (imJ φ))) κ z => y.1)
            (fun _ _ _ _ h => Subtype.ext h) (hs.image (fun q : IMD (mult (rankFn (trS stageX α) (imJ φ))) α ε θ κ => q.1))))
      · ext c
        constructor
        · rintro ⟨q, hq, rfl⟩
          obtain ⟨b, hb, hlo | ⟨z', hz', hzθ', hzb⟩⟩ := q.2
          · exfalso
            have h1 := (hlow q).mp hlo.1
            rw [hall_z q hq] at h1
            have := EReal.coe_le_coe_iff.mp h1
            linarith
          · have hzz : z' = z := by
              have := hall_z q hq
              rw [hz'] at this
              exact EReal.coe_injective this
            subst hzz
            exact ⟨⟨q.1, b, Prod.ext hb hz', hzb⟩, ⟨q, hq, rfl⟩, rfl⟩
        · rintro ⟨y, ⟨q, hq, hqy⟩, rfl⟩
          exact ⟨q, hq, hqy⟩
      · intro q y hqy
        have hnl : ¬ ((offPt q.1).2 = ⊥ ∨ (offPt q.1).2 ≤ ((α : ℝ) : EReal)) := by
          intro h
          have h1 := (hlow q).mp h
          rw [hqy, (IDz.spec y).1] at h1
          have := EReal.coe_le_coe_iff.mp (show ((z : ℝ) : EReal) ≤ ((α : ℝ) : EReal) from h1)
          linarith
        ext w
        simp only [GM, Set.mem_setOf_eq, IDz.b, ← hqy]
        constructor
        · rintro ⟨h1, h2, -, h4⟩
          refine ⟨h1, h2, ?_⟩
          rw [h4 hnl, hqy, (IDz.spec y).1]
          simp
        · rintro ⟨h1, h2, h3⟩
          refine ⟨h1, h2, fun h => absurd h hnl, fun _ => ?_⟩
          rw [h3, hqy, (IDz.spec y).1]
          simp

theorem t5_prom_bar {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    {α ε : ℝ} {a : offD (mult (rankFn stage J))} (hprom : PromQNE α ε a) :
    ∃ b d : ℝ, offPt a = ((b : EReal), (d : EReal)) ∧ d < b ∧ d + 2 * ε < b ∧ α < d ∧
      mult (rankFn stage J) ((b : EReal), (d : EReal)) ≠ 0 := by
  obtain ⟨hqne, hdiag⟩ := hprom
  obtain ⟨-, hα2⟩ := hqne
  have hne : mult (rankFn stage J) (offPt a) ≠ 0 := by
    intro h
    have ha2 : ((a.1.2 : ℕ∞) < mult (rankFn stage J) (offPt a)) := a.2
    rw [h] at ha2
    exact absurd ha2 (by simp)
  have hb : (offPt a).1 ≠ ⊥ ∧ (offPt a).1 ≠ ⊤ := by
    by_contra hcon
    rw [mult, if_neg hcon] at hne
    exact hne rfl
  have hdbot : (offPt a).2 ≠ ⊥ := by
    intro h
    rw [h] at hα2
    exact absurd (hα2.trans_le bot_le) (lt_irrefl _)
  have hbar : (offPt a).2 < (offPt a).1 := by
    by_contra hcon
    rw [mult, if_pos hb, if_neg hdbot, if_neg hcon] at hne
    exact hne rfl
  have hdtop : (offPt a).2 ≠ ⊤ := by
    intro h
    rw [h] at hbar
    exact absurd (hbar.trans_le le_top) (lt_irrefl ⊤)
  have hd : (offPt a).2 = (((offPt a).2.toReal : EReal)) := (EReal.coe_toReal hdtop hdbot).symm
  have hb' : (offPt a).1 = (((offPt a).1.toReal : EReal)) := (EReal.coe_toReal hb.2 hb.1).symm
  have hpair : offPt a = (((offPt a).1.toReal : EReal), ((offPt a).2.toReal : EReal)) :=
    Prod.ext_iff.mpr ⟨hb', hd⟩
  rw [hpair] at hne
  have hdbd : (offPt a).2.toReal < (offPt a).1.toReal :=
    EReal.coe_lt_coe_iff.mp (by rw [← hd, ← hb']; exact hbar)
  refine ⟨(offPt a).1.toReal, (offPt a).2.toReal, hpair, hdbd, ?_, ?_, hne⟩
  · by_contra hcon
    push_neg at hcon
    refine hdiag ⟨(((offPt a).2.toReal + ε : ℝ) : EReal), ?_, ?_⟩
    · rw [hb']
      constructor
      · rw [← EReal.coe_add]
        exact EReal.coe_le_coe_iff.mpr (by linarith)
      · rw [← EReal.coe_add]
        exact EReal.coe_le_coe_iff.mpr (by linarith)
    · rw [hd]
      simp only [EReal.toReal_coe]
      constructor
      · rw [← EReal.coe_add]
        exact EReal.coe_le_coe_iff.mpr (by linarith)
      · rw [← EReal.coe_add]
  · exact EReal.coe_lt_coe_iff.mp (by rw [← hd]; exact hα2)


theorem copy_coords {D : EReal × EReal → ℕ∞} (hD : ∀ p, D p ≠ 0 →
      (p.1 ≠ ⊥ ∧ p.1 ≠ ⊤) ∧ (p.2 = ⊥ ∨ p.2 < p.1)) (a : offD D) :
    ∃ b : ℝ, (offPt a).1 = ((b : ℝ) : EReal) ∧ ((offPt a).2 = ⊥ ∨ (offPt a).2 < ((b : ℝ) : EReal)) := by
  have hne : D (offPt a) ≠ 0 := by
    intro h0
    have hlt : ((a.1.2 : ℕ) : ℕ∞) < D (offPt a) := a.2
    rw [h0] at hlt
    exact absurd hlt (not_lt.mpr zero_le)
  obtain ⟨⟨h1, h2⟩, h3⟩ := hD _ hne
  refine ⟨(offPt a).1.toReal, (EReal.coe_toReal h2 h1).symm, ?_⟩
  rwa [EReal.coe_toReal h2 h1]

theorem mult_support {ι : Type*} (stage : ℝ → Set ι) (J : ℝ → ι → ι → Prop)
    (p : EReal × EReal) (h : mult (rankFn stage J) p ≠ 0) :
    (p.1 ≠ ⊥ ∧ p.1 ≠ ⊤) ∧ (p.2 = ⊥ ∨ p.2 < p.1) := by
  unfold mult at h
  by_cases h1 : p.1 ≠ ⊥ ∧ p.1 ≠ ⊤
  · refine ⟨h1, ?_⟩
    rw [if_pos h1] at h
    by_cases h2 : p.2 = ⊥
    · exact Or.inl h2
    · rw [if_neg h2] at h
      by_cases h3 : p.2 < p.1
      · exact Or.inr h3
      · rw [if_neg h3] at h; exact absurd rfl h
  · rw [if_neg h1] at h; exact absurd rfl h

theorem qse_bar {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop} {α ε : ℝ}
    (a : offD (mult (rankFn stage J)))
    (hq : offPt a ∈ QSE α ∧ α + ε < (offPt a).1 ∧ 2 * ε < (offPt a).1 - (offPt a).2) :
    ∃ b : ℝ, (offPt a).1 = ((b : ℝ) : EReal) ∧ α + ε < b ∧
      ((offPt a).2 = ⊥ ∨ ∃ d : ℝ, (offPt a).2 = ((d : ℝ) : EReal) ∧ d ≤ α ∧ d + 2 * ε < b) := by
  obtain ⟨b, hb, -⟩ := copy_coords (mult_support stage J) a
  obtain ⟨⟨-, hdα⟩, hb1, hb2⟩ := hq
  refine ⟨b, hb, ?_, ?_⟩
  · rw [hb] at hb1
    exact EReal.coe_lt_coe_iff.mp (by exact_mod_cast hb1)
  · by_cases hbot : (offPt a).2 = ⊥
    · exact Or.inl hbot
    · right
      have htop : (offPt a).2 ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hdα
      refine ⟨(offPt a).2.toReal, (EReal.coe_toReal htop hbot).symm,
        EReal.coe_le_coe_iff.mp (by rw [EReal.coe_toReal htop hbot]; exact hdα), ?_⟩
      have h2 : ((2 * ε : ℝ) : EReal) = 2 * ((ε : ℝ) : EReal) := by
        rw [EReal.coe_mul]; norm_cast
      rw [hb, ← EReal.coe_toReal htop hbot, ← EReal.coe_sub, ← h2] at hb2
      have := EReal.coe_lt_coe_iff.mp hb2
      linarith

theorem exists_uniform_pos {T : Type} (P : T → ℝ → Prop)
    (hmono : ∀ x μ κ, 0 < κ → κ ≤ μ → P x μ → P x κ) (s : Set T) (hs : s.Finite)
    (hP : ∀ x ∈ s, ∃ μ > 0, P x μ) : ∃ κ > 0, ∀ x ∈ s, P x κ := by
  classical
  obtain ⟨t, rfl⟩ := hs.exists_finset_coe
  induction t using Finset.induction with
  | empty => exact ⟨1, one_pos, fun x hx => absurd hx (Finset.notMem_empty x)⟩
  | insert y t hyt ih =>
    obtain ⟨κ, hκ, hT⟩ := ih (Finset.finite_toSet t)
      (fun x hx => hP x (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp hx))))
    obtain ⟨μ, hμ, hPy⟩ := hP y (Finset.mem_coe.mpr (Finset.mem_insert_self y t))
    refine ⟨min κ μ, lt_min hκ hμ, fun x hx => ?_⟩
    rcases Finset.mem_insert.mp (Finset.mem_coe.mp hx) with rfl | hx
    · exact hmono x μ _ (lt_min hκ hμ) (min_le_right _ _) hPy
    · exact hmono x κ _ (lt_min hκ hμ) (min_le_left _ _) (hT x (Finset.mem_coe.mpr hx))

theorem copy_death_crit {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    (a : offD (mult (rankFn stage J))) {z : ℝ} (hz : (offPt a).2 = ((z : ℝ) : EReal)) :
    z ∈ (critSet hTame : Set ℝ) := by
  obtain ⟨b, hb, hd⟩ := copy_coords (mult_support stage J) a
  have hzb : z < b := by
    rcases hd with h | h
    · rw [hz] at h; exact absurd h (EReal.coe_ne_bot _)
    · rw [hz] at h; exact EReal.coe_lt_coe_iff.mp h
  by_contra hzn
  have h0 := t3_death_pin hLaw hTame (b := b) (d := z) hzb hzn
  have hpt : offPt a = (((b : ℝ) : EReal), ((z : ℝ) : EReal)) := Prod.ext hb hz
  have hlt : ((a.1.2 : ℕ) : ℕ∞) < mult (rankFn stage J) (offPt a) := a.2
  rw [hpt, h0] at hlt
  exact absurd hlt (not_lt.mpr zero_le)

theorem jhi_of_gt {α ε d : ℝ} {p : EReal × EReal} (hp : p.2 = ((d : ℝ) : EReal)) (h : α < d) :
    jhi α ε p = d + 2 * ε := by
  have hnb : p.2 ≠ ⊥ := by rw [hp]; exact EReal.coe_ne_bot d
  have hn : ¬ p.2 ≤ ((α : ℝ) : EReal) := by
    rw [hp]; exact not_le.mpr (EReal.coe_lt_coe_iff.mpr h)
  unfold jhi; rw [if_neg hnb, if_neg hn, hp, EReal.toReal_coe]

theorem jhi_of_le {α ε d : ℝ} {p : EReal × EReal} (hp : p.2 = ((d : ℝ) : EReal)) (h : d ≤ α) :
    jhi α ε p = max (α + ε) (d + 2 * ε) := by
  have hnb : p.2 ≠ ⊥ := by rw [hp]; exact EReal.coe_ne_bot d
  have hle : p.2 ≤ ((α : ℝ) : EReal) := by rw [hp]; exact EReal.coe_le_coe_iff.mpr h
  unfold jhi; rw [if_neg hnb, if_pos hle, hp, EReal.toReal_coe]

theorem jhi_of_bot {α ε : ℝ} {p : EReal × EReal} (hp : p.2 = ⊥) : jhi α ε p = α + ε := by
  unfold jhi; rw [if_pos hp]

theorem JDem_mono {α ε μ κ b : ℝ} {p : EReal × EReal} (hκμ : κ ≤ μ) (h : JDem α ε μ b p) :
    JDem α ε κ b p := by
  obtain ⟨h1, h2 | h2 | ⟨d, hd, hdα, hdb⟩⟩ := h
  · exact ⟨h1, Or.inl h2⟩
  · exact ⟨h1, Or.inr (Or.inl h2)⟩
  · exact ⟨h1, Or.inr (Or.inr ⟨d, hd, by linarith, by linarith⟩)⟩

theorem closeE_coe_iff (x y r : ℝ) :
    closeE ((x : ℝ) : EReal) ((y : ℝ) : EReal) r ↔ x ≤ y + r ∧ y ≤ x + r := by
  unfold closeE
  rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]

theorem ereal_between {e : EReal} {a c : ℝ} (ha : ((a : ℝ) : EReal) ≤ e)
    (hc : e ≤ ((c : ℝ) : EReal)) : ∃ r : ℝ, e = ((r : ℝ) : EReal) ∧ a ≤ r ∧ r ≤ c := by
  have h1 : e ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hc
  have h2 : e ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) ha
  refine ⟨e.toReal, (EReal.coe_toReal h1 h2).symm, ?_, ?_⟩
  · exact EReal.coe_le_coe_iff.mp (by rw [EReal.coe_toReal h1 h2]; exact ha)
  · exact EReal.coe_le_coe_iff.mp (by rw [EReal.coe_toReal h1 h2]; exact hc)

/-- Demand injection of the matching gate: prominent copies (Q^NE) inject eps-close in both
coordinates, high-far Q^SE copies birth-close (both-close when landing in Q^NE), via the
Bauer-Lesnick induced matching with a low class at virtual death alpha. -/
theorem solution {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameX : IsTameModule stageX JX) (hTameY : IsTameModule stageY JY)
    {α ε : ℝ} (hε : 0 ≤ ε)
    (hIL : StrongInterleavingAbove stageX JX stageY JY hLawX hLawY α ε hε) :
    ∃ F : {a : offD (mult (rankFn stageX JX)) // DemandsOff α ε a}
          → offD (mult (rankFn stageY JY)),
      Function.Injective F ∧
      (∀ a, PromQNE α ε a.1 → CloseCopy2 ε a.1 (F a)) ∧
      (∀ a, offPt a.1 ∈ QSE α → CloseCopy1 ε a.1 (F a) ∧
        (offPt (F a) ∈ QNE α → CloseCopy2 ε a.1 (F a))) := by
  classical
  obtain ⟨φ, ψ, hSq1, -, hSq3, hSq4⟩ := hIL
  have hLI := imLaw hLawX hLawY φ hSq1
  have hTI := imTame hLawX hLawY hTameX hTameY φ hSq1
  haveI : Finite (offD (mult (rankFn stageX JX))) :=
    Set.finite_univ_iff.mp (t5_offD_finite hLawX hTameX)
  
  let P : offD (mult (rankFn stageX JX)) → ℝ → Prop := fun a κ =>
    ∃ b : ℝ, α + ε < b ∧ JDem α ε κ b (offPt a) ∧ jhi α ε (offPt a) + κ ≤ b
  have hmono : ∀ a μ κ, 0 < κ → κ ≤ μ → P a μ → P a κ := by
    rintro a μ κ - hκμ ⟨b, hb, hJ, hhi⟩
    exact ⟨b, hb, JDem_mono hκμ hJ, by linarith⟩
  have hP : ∀ a ∈ {a : offD (mult (rankFn stageX JX)) | DemandsOff α ε a}, ∃ μ > 0, P a μ := by
    intro a ha
    rcases ha with hprom | hqse
    · obtain ⟨b, d, hpt, -, hd2b, hαd, -⟩ := t5_prom_bar hprom
      have hd : (offPt a).2 = ((d : ℝ) : EReal) := congrArg Prod.snd hpt
      have m1 : min (d - α) (b - d - 2 * ε) ≤ d - α := min_le_left _ _
      have m2 : min (d - α) (b - d - 2 * ε) ≤ b - d - 2 * ε := min_le_right _ _
      have hm : 0 < min (d - α) (b - d - 2 * ε) := lt_min (by linarith) (by linarith)
      refine ⟨min (d - α) (b - d - 2 * ε) / 2, by linarith, b, by linarith,
        ⟨congrArg Prod.fst hpt, Or.inr (Or.inr ⟨d, hd, by linarith, by linarith⟩)⟩, ?_⟩
      rw [jhi_of_gt hd hαd]
      linarith
    · obtain ⟨b, hb, hbα, hdd⟩ := qse_bar a hqse
      have hJ1 : ∀ κ : ℝ, JDem α ε κ b (offPt a) := fun κ => ⟨hb, by
        rcases hdd with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)⟩
      have hlt := (jdem_facts hε one_pos hbα (hJ1 1)).2.1
      refine ⟨(b - jhi α ε (offPt a)) / 2, by linarith, b, hbα, hJ1 _, by linarith⟩
  obtain ⟨κ, hκ, hκP⟩ := exists_uniform_pos P hmono _ (Set.toFinite _) hP
  
  obtain ⟨δI, hδI, -, hgI⟩ := t3_gapEx (critSet hTI) one_pos α
  obtain ⟨δY1, hδY1, -, hgY1⟩ := t3_gapEx (critSet hTameY) one_pos (α - ε)
  obtain ⟨δY2, hδY2, -, hgY2⟩ := t3_gapEx (critSet hTameY) one_pos α
  set m := min (min δI δY1) (min δY2 κ) with hmdef
  have n1 : m ≤ min δI δY1 := min_le_left _ _
  have n2 : m ≤ min δY2 κ := min_le_right _ _
  have n3 : min δI δY1 ≤ δI := min_le_left _ _
  have n4 : min δI δY1 ≤ δY1 := min_le_right _ _
  have n5 : min δY2 κ ≤ δY2 := min_le_left _ _
  have n6 : min δY2 κ ≤ κ := min_le_right _ _
  have hm : 0 < m := lt_min (lt_min hδI hδY1) (lt_min hδY2 hκ)
  set θ := m / 2 with hθdef
  have hθ : 0 < θ := by linarith
  have hgapI : ∀ τ ∈ critSet hTI, τ ≤ α ∨ α + θ < τ := by
    intro τ hτ
    by_cases h : τ ≤ α
    · exact Or.inl h
    · push_neg at h
      have := hgI τ hτ (ne_of_gt h)
      rw [abs_of_pos (by linarith)] at this
      exact Or.inr (by linarith)
  have hgY : α + θ - ε ∉ (critSet hTameY : Set ℝ) := by
    intro hc
    have := hgY1 _ (Finset.mem_coe.mp hc) (by intro h; linarith)
    rw [show α + θ - ε - (α - ε) = θ by ring, abs_of_pos hθ] at this
    linarith
  
  obtain ⟨E, hEinj, hEspec⟩ := eGlobal hLawX hLawY hTameX hTameY hε φ ψ hSq1 hSq4 hκ
  obtain ⟨M, hMinj, hMmem⟩ := mGlobal hLawX hLawY hTameX hTameY hε φ ψ hSq1 hSq3 hθ hκ
    (by linarith) hgapI hgY
  have hJD : ∀ a : {a : offD (mult (rankFn stageX JX)) // DemandsOff α ε a},
      ∃ b : ℝ, α + ε < b ∧ JDem α ε κ b (offPt a.1) := fun a => by
    obtain ⟨b, hb, hJ, -⟩ := hκP a.1 a.2
    exact ⟨b, hb, hJ⟩
  let toJD : {a : offD (mult (rankFn stageX JX)) // DemandsOff α ε a} →
      JD (mult (rankFn stageX JX)) α ε κ := fun a => ⟨a.1, hJD a⟩
  
  have hEfacts : ∀ a : {a : offD (mult (rankFn stageX JX)) // DemandsOff α ε a},
      ∃ b : ℝ, (offPt a.1).1 = ((b : ℝ) : EReal) ∧ (offPt (E (toJD a))).1 = ((b : ℝ) : EReal) ∧
        JDem α ε κ b (offPt a.1) ∧ jhi α ε (offPt a.1) + κ ≤ b ∧
        jlo α (offPt a.1) ≤ jlo α (offPt (E (toJD a))) ∧
        jlo α (offPt (E (toJD a))) ≤ jhi α ε (offPt a.1) := by
    intro a
    obtain ⟨b, -, hJ, hhi⟩ := hκP a.1 a.2
    obtain ⟨h1, h2, h3⟩ := hEspec (toJD a)
    exact ⟨b, hJ.1, h1.trans hJ.1, hJ, hhi, h2, h3⟩
  
  have hEfin : ∀ a : {a : offD (mult (rankFn stageX JX)) // DemandsOff α ε a},
      ¬ (offPt (E (toJD a))).2 ≤ ((α : ℝ) : EReal) →
      ∃ z : ℝ, (offPt (E (toJD a))).2 = ((z : ℝ) : EReal) ∧ α + θ < z ∧
        jlo α (offPt (E (toJD a))) = z := by
    intro a hnl
    obtain ⟨bE, -, hdE⟩ := copy_coords (mult_support _ _) (E (toJD a))
    have hnb : (offPt (E (toJD a))).2 ≠ ⊥ := by intro h; rw [h] at hnl; exact hnl bot_le
    have hnt : (offPt (E (toJD a))).2 ≠ ⊤ := by
      rcases hdE with h | h
      · exact absurd h hnb
      · exact ne_top_of_lt h
    set z := (offPt (E (toJD a))).2.toReal with hzdef
    have hz : (offPt (E (toJD a))).2 = ((z : ℝ) : EReal) := (EReal.coe_toReal hnt hnb).symm
    have hzα : α < z := by
      rw [hz] at hnl; exact EReal.coe_lt_coe_iff.mp (not_le.mp hnl)
    have hzc := copy_death_crit hLI hTI (E (toJD a)) hz
    rcases hgapI z hzc with h | h
    · linarith
    · exact ⟨z, hz, h, jlo_of_gt hz hzα⟩
  have hIMD : ∀ a : {a : offD (mult (rankFn stageX JX)) // DemandsOff α ε a},
      ∃ b : ℝ, (offPt (E (toJD a))).1 = ((b : ℝ) : EReal) ∧
        ((((offPt (E (toJD a))).2 = ⊥ ∨ (offPt (E (toJD a))).2 ≤ ((α : ℝ) : EReal)) ∧
            α + ε + κ ≤ b) ∨
          (∃ z : ℝ, (offPt (E (toJD a))).2 = ((z : ℝ) : EReal) ∧ α + θ < z ∧ z + κ ≤ b)) := by
    intro a
    obtain ⟨b, -, hbE, hJ, hhi, -, hup⟩ := hEfacts a
    refine ⟨b, hbE, ?_⟩
    by_cases hlow : (offPt (E (toJD a))).2 ≤ ((α : ℝ) : EReal)
    · have := jhi_ge hε hκ hJ
      exact Or.inl ⟨Or.inr hlow, by linarith⟩
    · obtain ⟨z, hz, hzθ, hjz⟩ := hEfin a hlow
      rw [hjz] at hup
      exact Or.inr ⟨z, hz, hzθ, by linarith⟩
  refine ⟨fun a => M ⟨E (toJD a), hIMD a⟩, ?_, ?_, ?_⟩
  · 
    intro a a' h
    have h1 := congrArg Subtype.val (hMinj h)
    have h2 := hEinj h1
    exact Subtype.ext (congrArg (fun x : JD (mult (rankFn stageX JX)) α ε κ => x.1) h2)
  · 
    intro a hprom
    obtain ⟨b', d, hpt, -, hd2b, hαd, -⟩ := t5_prom_bar hprom
    obtain ⟨b, hb, hbE, hJ, hhi, hlo, hup⟩ := hEfacts a
    have hbb : b' = b := by
      have := congrArg Prod.fst hpt
      rw [hb] at this
      exact (EReal.coe_injective this).symm
    subst hbb
    have hd : (offPt a.1).2 = ((d : ℝ) : EReal) := congrArg Prod.snd hpt
    rw [jlo_of_gt hd hαd] at hlo
    rw [jhi_of_gt hd hαd] at hup
    have hnl : ¬ (offPt (E (toJD a))).2 ≤ ((α : ℝ) : EReal) := by
      intro h
      rw [jlo_of_le h] at hlo
      linarith
    obtain ⟨z, hz, -, hjz⟩ := hEfin a hnl
    rw [hjz] at hlo hup
    obtain ⟨hy1, hy2, -, hy4⟩ := hMmem ⟨E (toJD a), hIMD a⟩
    have hy4' := hy4 (fun h => hnl (h.elim (fun h0 => by rw [h0]; exact bot_le) id))
    simp only [hbE, hz, EReal.toReal_coe] at hy1 hy2 hy4'
    obtain ⟨r, hr, hr1, hr2⟩ := ereal_between hy1 hy2
    refine ⟨?_, ?_⟩
    · rw [hb, hr, closeE_coe_iff]
      exact ⟨by linarith, by linarith⟩
    · rw [hd, hy4', closeE_coe_iff]
      exact ⟨by linarith, by linarith⟩
  · 
    intro a hqse
    obtain ⟨b, hb, hbE, hJ, hhi, hlo, hup⟩ := hEfacts a
    obtain ⟨hy1, hy2, hy3, hy4⟩ := hMmem ⟨E (toJD a), hIMD a⟩
    simp only [hbE, EReal.toReal_coe] at hy1 hy2
    obtain ⟨r, hr, hr1, hr2⟩ := ereal_between hy1 hy2
    refine ⟨?_, fun hQNE => ?_⟩
    · show closeE _ _ ε
      rw [hb, hr, closeE_coe_iff]
      exact ⟨by linarith, by linarith⟩
    · refine ⟨?_, ?_⟩
      · rw [hb, hr, closeE_coe_iff]
        exact ⟨by linarith, by linarith⟩
      · 
        have hαy : ((α : ℝ) : EReal) < (offPt (M ⟨E (toJD a), hIMD a⟩)).2 := hQNE.2
        by_cases hlow : (offPt (E (toJD a))).2 ≤ ((α : ℝ) : EReal)
        · exfalso
          rcases hy3 (Or.inr hlow) with h | h
          · rw [h] at hαy; exact not_lt.mpr bot_le hαy
          · obtain ⟨w, hw, hw1, hw2⟩ := ereal_between hαy.le h.le
            have hwc := copy_death_crit hLawY hTameY (M ⟨E (toJD a), hIMD a⟩) hw
            have hwα : α < w := by rw [hw] at hαy; exact EReal.coe_lt_coe_iff.mp hαy
            have hwθ : w < α + θ - ε := by rw [hw] at h; exact EReal.coe_lt_coe_iff.mp h
            have := hgY2 w (Finset.mem_coe.mp hwc) (ne_of_gt hwα)
            rw [abs_of_pos (by linarith)] at this
            linarith
        · obtain ⟨z, hz, -, hjz⟩ := hEfin a hlow
          have hy4' := hy4 (fun h => hlow (h.elim (fun h0 => by rw [h0]; exact bot_le) id))
          rw [hz, EReal.toReal_coe] at hy4'
          have hzα : α + ε < z := by
            rw [hy4'] at hαy
            have := EReal.coe_lt_coe_iff.mp hαy
            linarith
          rw [hjz] at hup
          obtain ⟨-, hbot | ⟨d, hd, hdα, hdb⟩ | ⟨d, hd, hdα, -⟩⟩ := hJ
          · rw [jhi_of_bot hbot] at hup; linarith
          · rw [jhi_of_le hd hdα] at hup
            have hzd : z ≤ d + 2 * ε := by
              rcases le_max_iff.mp hup with h | h
              · linarith
              · exact h
            rw [hd, hy4', closeE_coe_iff]
            exact ⟨by linarith, by linarith⟩
          · exfalso
            have hq : (offPt a.1).2 ≤ ((α : ℝ) : EReal) := hqse.2
            rw [hd] at hq
            have := EReal.coe_le_coe_iff.mp hq
            linarith
