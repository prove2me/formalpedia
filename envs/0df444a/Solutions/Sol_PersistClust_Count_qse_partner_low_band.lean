-- Prove2me | solution 1 for PersistClust.Count.qse_partner_low_band
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-14T18:10:30.940419+00:00
-- url     : https://prove2.me/submissions/18b9f1dd-a2d1-44b5-9dce-c6b6bc1a17e6

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

theorem t5_census_absorb {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {b v δ₀ : ℝ} (hbd : v < b)
    (hδ₀0 : 0 < δ₀) (hδ₀le : δ₀ ≤ (b - v) / 2)
    (hgap : (∀ τ ∈ critSet hTame, τ ≠ b → δ₀ < |τ - b|) ∧
      (∀ τ ∈ critSet hTame, τ ≠ v → δ₀ < |τ - v|))
    (hthr : ∀ η : ℝ, η ∈ Set.Ioo (0 : ℝ) δ₀ →
        ∃ C : comps stage J (v + η), birthSup hLaw (v + η) C = b ∧
          ∀ hle : v - η ≤ v + η, birthSup hLaw (v - η) (structMap hLaw hle C) ≠ b) :
    mult (rankFn stage J) ((b : EReal), (v : EReal)) ≠ 0 := by
  obtain ⟨δ', hδ'0, hδ'le, hstab⟩ := t3_comb_stable hLaw hTame hbd
  have hmin0 : 0 < min δ₀ δ' := lt_min hδ₀0 hδ'0
  have hmin1 : min δ₀ δ' ≤ δ₀ := min_le_left _ _
  have hmin2 : min δ₀ δ' ≤ δ' := min_le_right _ _
  set ηp := min δ₀ δ' / 2 with hηpdef
  have hηp0 : 0 < ηp := by linarith
  have hηpδ₀ : ηp < δ₀ := by linarith
  have hηplim : ηp < (b - v) / 2 := by linarith
  have hcomb : mult (rankFn stage J) ((b : EReal), (v : EReal))
      = t3_comb stage J b v ηp := by
    rw [t3_mult_unfold hLaw hbd]
    refine le_antisymm (iInf₂_le ηp ⟨hηp0, hηplim⟩) (le_iInf₂ fun η hη => ?_)
    rcases lt_or_ge η ηp with hlt | hge
    · have hηδ' : η < δ' := by linarith
      have hηpδ' : ηp < δ' := by linarith
      exact (hstab η ⟨hη.1, hηδ'⟩ ηp ⟨hηp0, hηpδ'⟩).symm.le
    · exact t3_comb_ge hLaw hTame hbd hηp0 hge hη.2
  obtain ⟨C₀, hC₀b, hC₀d⟩ := hthr ηp ⟨hηp0, hηpδ₀⟩
  have hle : v - ηp ≤ v + ηp := by linarith
  have hβb : v + ηp < b := by linarith
  -- every below-census cell lifts to an above-census cell descending back onto it
  have hlift : ∀ C : comps stage J (v - ηp), birthSup hLaw (v - ηp) C = b →
      ∃ A : comps stage J (v + ηp), birthSup hLaw (v + ηp) A = b ∧
        structMap hLaw hle A = C := fun C hC => t5_aliveUp hLaw hTame hC hle hβb
  -- choose one lift per cell; off the below-census the choice is irrelevant
  haveI hNE : Nonempty (comps stage J (v + ηp)) := ⟨C₀⟩
  set g : comps stage J (v - ηp) → comps stage J (v + ηp) := fun C =>
    Classical.epsilon (fun A => birthSup hLaw (v + ηp) A = b ∧
      structMap hLaw hle A = C) with hgdef
  have hgspec : ∀ C : comps stage J (v - ηp), birthSup hLaw (v - ηp) C = b →
      birthSup hLaw (v + ηp) (g C) = b ∧ structMap hLaw hle (g C) = C :=
    fun C hC => Classical.epsilon_spec (hlift C hC)
  -- the below-census injects into the above-census minus the thread's own cell
  have hinjle : ({C : comps stage J (v - ηp) | birthSup hLaw (v - ηp) C = b} :
      Set (comps stage J (v - ηp))).encard ≤
      ({A : comps stage J (v + ηp) | birthSup hLaw (v + ηp) A = b} \ {C₀} :
      Set (comps stage J (v + ηp))).encard := by
    refine Set.encard_le_encard_of_injOn (f := g) (fun C hC => ?_)
      (fun C₁ h₁ C₂ h₂ heq => ?_)
    · have hCb : birthSup hLaw (v - ηp) C = b := hC
      refine ⟨(hgspec C hCb).1, ?_⟩
      intro hmem
      have heq : g C = C₀ := Set.mem_singleton_iff.mp hmem
      have h1 : structMap hLaw hle (g C) = C := (hgspec C hCb).2
      exact hC₀d hle (by rw [← heq, h1]; exact hCb)
    · have h₁b : birthSup hLaw (v - ηp) C₁ = b := h₁
      have h₂b : birthSup hLaw (v - ηp) C₂ = b := h₂
      exact calc C₁ = structMap hLaw hle (g C₁) := (hgspec C₁ h₁b).2.symm
        _ = structMap hLaw hle (g C₂) := congrArg (structMap hLaw hle) heq
        _ = C₂ := (hgspec C₂ h₂b).2
  -- strictness: removing the thread's cell leaves a strict subset of the above-census
  haveI hcompFin : Finite (comps stage J (v + ηp)) := (hTame.1 (v + ηp)).to_subtype
  have hfinS : ({A : comps stage J (v + ηp) | birthSup hLaw (v + ηp) A = b} :
      Set (comps stage J (v + ηp))).Finite :=
    Set.finite_univ.subset (Set.subset_univ _)
  have hfinSdiff : ({A : comps stage J (v + ηp) | birthSup hLaw (v + ηp) A = b} \ {C₀} :
      Set (comps stage J (v + ηp))).Finite := hfinS.sdiff
  have hssub : ({A : comps stage J (v + ηp) | birthSup hLaw (v + ηp) A = b} \ {C₀} :
      Set (comps stage J (v + ηp))) ⊂
      ({A : comps stage J (v + ηp) | birthSup hLaw (v + ηp) A = b} :
      Set (comps stage J (v + ηp))) :=
    ⟨Set.sdiff_subset, fun h =>
      have hmem : C₀ ∈ ({A : comps stage J (v + ηp) | birthSup hLaw (v + ηp) A = b} :
        Set (comps stage J (v + ηp))) := hC₀b
      (h hmem).2 (Set.mem_singleton_iff.mpr rfl)⟩
  rw [hcomb, t3_comb_small hLaw hTame hbd hgap ⟨hηp0, hηpδ₀⟩ hηplim]
  exact (tsub_pos_iff_lt.mpr (hinjle.trans_lt (hfinSdiff.encard_lt_encard hssub))).ne'

theorem t3_essential_mult {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {T e : ℝ} (E : comps stage J T) (he : birthSup hLaw T E = e)
    (hfull : ∀ (w : ℝ) (hw : w ≤ T), birthSup hLaw w (structMap hLaw hw E) = e) :
    mult (rankFn stage J) ((e : EReal), (⊥ : EReal)) ≠ 0 := by
  classical
  obtain ⟨s₀, hs₀⟩ := hTame.2.2
  -- (0) every ancestor-level set is bounded above by s₀ (cells are nonempty ⊆ their stage)
  have hAncBdd : ∀ {t : ℝ} (C : comps stage J t), BddAbove (AncSet hLaw t C) := by
    intro t C
    refine ⟨s₀, fun u hu => ?_⟩
    obtain ⟨-, C', -⟩ := hu
    have hstage : (stage u).Nonempty := by
      obtain ⟨x, hx, -⟩ := C'.property
      exact ⟨x, hx⟩
    by_contra hle
    push_neg at hle
    exact hstage.ne_empty (hs₀ u hle.le)
  -- (1) the census witness: for every (η, t) a level-t cell with birth-sup in (e−η, e]
  have hwit : ∀ (η : ℝ), 0 < η → ∀ (t : ℝ), t ≤ e - η →
      ∃ (F : comps stage J t), e - η < birthSup hLaw t F ∧ birthSup hLaw t F ≤ e := by
    intro η hη t ht
    by_cases hTt : t ≤ T
    · refine ⟨structMap hLaw hTt E, ?_, ?_⟩
      · rw [hfull t hTt]; linarith
      · rw [hfull t hTt]
    · have hTt2 : T ≤ t := (lt_of_not_ge hTt).le
      have hBne : (AncSet hLaw T E).Nonempty := ⟨T, le_refl T, E, t3_structMap_id hLaw T E⟩
      have hsup : sSup (AncSet hLaw T E) = e :=
        (rfl : sSup (AncSet hLaw T E) = birthSup hLaw T E).symm.trans he
      have hlt : e - η < sSup (AncSet hLaw T E) := by rw [hsup]; linarith
      obtain ⟨u, huB, huη⟩ := (lt_csSup_iff (hAncBdd E) hBne).mp hlt
      obtain ⟨hu, C', hC'⟩ := huB
      have htu : t ≤ u := (lt_of_le_of_lt ht huη).le
      have hdesc : structMap hLaw hTt2 (structMap hLaw htu C') = E := by
        rw [structMap_comp hLaw hTt2 htu C']
        exact hC'
      refine ⟨structMap hLaw htu C', ?_, ?_⟩
      · have hmem : u ∈ AncSet hLaw t (structMap hLaw htu C') := ⟨htu, C', rfl⟩
        have hle : u ≤ birthSup hLaw t (structMap hLaw htu C') :=
          (rfl : birthSup hLaw t (structMap hLaw htu C') =
              sSup (AncSet hLaw t (structMap hLaw htu C'))).symm ▸
            le_csSup (hAncBdd _) hmem
        linarith
      · have hball : ∀ w ∈ AncSet hLaw t (structMap hLaw htu C'), w ≤ e := by
          intro w hw
          obtain ⟨hw, C'', hC''⟩ := hw
          have hC''E : structMap hLaw (le_trans hTt2 hw) C'' = E := by
            rw [← structMap_comp hLaw hTt2 hw C'', hC'']
            exact hdesc
          have hr : birthSup hLaw w C'' ≤ e := by
            have hrun := rungB_bSup_descend_ge hLaw hTame (le_trans hTt2 hw) C''
            rw [hC''E, he] at hrun
            exact hrun
          have hwle : w ≤ birthSup hLaw w C'' :=
            (rfl : birthSup hLaw w C'' = sSup (AncSet hLaw w C'')).symm ▸
              le_csSup (hAncBdd _) ⟨le_refl w, C'', t3_structMap_id hLaw w C''⟩
          linarith
        have hBne2 : (AncSet hLaw t (structMap hLaw htu C')).Nonempty :=
          ⟨t, le_refl t, _, t3_structMap_id hLaw t _⟩
        exact csSup_le hBne2 hball
  -- (2) the rank difference is ≥ 1 for every (η, t)
  have hge : ∀ (η : ℝ), 0 < η → ∀ (t : ℝ), t ≤ e - η →
      1 ≤ rankFn stage J (e - η) t - rankFn stage J (e + η) t := by
    intro η hη t ht
    obtain ⟨F, hFhi, hFlo⟩ := hwit η hη t ht
    haveI hfinT : Finite (comps stage J t) := (hTame.1 t).to_subtype
    -- F meets stage (e − η): an ancestor level above e − η contributes a point
    have hBneF : (AncSet hLaw t F).Nonempty := ⟨t, le_refl t, F, t3_structMap_id hLaw t F⟩
    have hsupF : sSup (AncSet hLaw t F) = birthSup hLaw t F := rfl
    have hltF : e - η < sSup (AncSet hLaw t F) := by rw [hsupF]; exact hFhi
    obtain ⟨u, huB, huη⟩ := (lt_csSup_iff (hAncBdd F) hBneF).mp hltF
    obtain ⟨hu, C', hC'⟩ := huB
    have hspec := compRep_spec stage J u C'
    have hz : compRep stage J u C' ∈ C'.val := by
      rw [← hspec.2]
      exact hLaw.refl hspec.1
    obtain ⟨hcls, -⟩ := t3_desc_point hLaw hu hC' hz
    have hFS₁ : F ∈ {C : comps stage J t |
        C.val ∈ ((fun x => {y | J t x y}) '' stage (e - η))} :=
      ⟨compRep stage J u C', hLaw.antitone (show (e - η) ≤ u by linarith) hspec.1, hcls⟩
    -- F does not meet stage (e + η): a meeting point would put e + η into F's AncSet
    have hF2 : F ∉ {C : comps stage J t |
        C.val ∈ ((fun x => {y | J t x y}) '' stage (e + η))} := by
      intro hF
      obtain ⟨x, hx, hxcls⟩ := hF
      have hprop : {y | J (e + η) x y} ∈
          ((fun x => {y | J (e + η) x y}) '' stage (e + η)) := ⟨x, hx, rfl⟩
      have hdesc : structMap hLaw (show t ≤ e + η by linarith)
          ⟨{y | J (e + η) x y}, hprop⟩ = F := by
        have hspec := compRep_spec stage J (e + η) ⟨{y | J (e + η) x y}, hprop⟩
        have hJsx : J (e + η) (compRep stage J (e + η) ⟨{y | J (e + η) x y}, hprop⟩) x :=
          (Set.ext_iff.mp hspec.2 x).mpr (hLaw.refl hx)
        have hJtx : J t (compRep stage J (e + η) ⟨{y | J (e + η) x y}, hprop⟩) x :=
          hLaw.compat (show t ≤ e + η by linarith) hJsx
        refine Subtype.ext ?_
        rw [structMap_val, ← hxcls]
        ext y
        exact ⟨fun hy => hLaw.trans (hLaw.symm hJtx) hy, fun hy => hLaw.trans hJtx hy⟩
      have hmem : (e + η) ∈ AncSet hLaw t F :=
        ⟨show t ≤ e + η by linarith, _, hdesc⟩
      have hle : (e + η) ≤ birthSup hLaw t F :=
        (rfl : birthSup hLaw t F = sSup (AncSet hLaw t F)).symm ▸
          le_csSup (hAncBdd F) hmem
      linarith
    -- the strict count: the (e + η)-meeters are a proper subset of the (e − η)-meeters
    have hsub : {C : comps stage J t | C.val ∈ ((fun x => {y | J t x y}) '' stage (e + η))}
        ⊆ {C : comps stage J t | C.val ∈ ((fun x => {y | J t x y}) '' stage (e - η))} := by
      intro C hC
      obtain ⟨x, hx, hxcls⟩ := hC
      exact ⟨x, hLaw.antitone (show (e - η) ≤ (e + η) by linarith) hx, hxcls⟩
    have hfinS : {C : comps stage J t |
        C.val ∈ ((fun x => {y | J t x y}) '' stage (e + η))}.Finite :=
      Set.Finite.subset Set.finite_univ (Set.subset_univ _)
    have hssub : {C : comps stage J t | C.val ∈ ((fun x => {y | J t x y}) '' stage (e + η))}
        ⊂ {C : comps stage J t | C.val ∈ ((fun x => {y | J t x y}) '' stage (e - η))} :=
      ⟨hsub, fun heq => hF2 (heq hFS₁)⟩
    have hlt := hfinS.encard_lt_encard hssub
    have hne : {C : comps stage J t | C.val ∈ ((fun x => {y | J t x y}) '' stage (e - η))}.encard -
        {C : comps stage J t | C.val ∈ ((fun x => {y | J t x y}) '' stage (e + η))}.encard ≠ 0 :=
      fun hzero => not_le.mpr hlt (tsub_eq_zero_iff_le.mp hzero)
    rw [t3_rank_meets hLaw (show t ≤ e - η by linarith),
        t3_rank_meets hLaw (show t ≤ e + η by linarith)]
    exact ENat.one_le_iff_ne_zero.mpr hne
  -- (3) the ⊥-branch of `mult` is ≥ 1
  have hopen : mult (rankFn stage J) ((e : EReal), (⊥ : EReal)) =
      ⨅ (η : ℝ) (_ : 0 < η), ⨅ (t : ℝ) (_ : t ≤ e - η),
        (rankFn stage J (e - η) t - rankFn stage J (e + η) t) := by
    simp only [mult]
    rw [if_pos (⟨EReal.coe_ne_bot e, EReal.coe_ne_top e⟩ :
        ((e : EReal) ≠ (⊥ : EReal)) ∧ ((e : EReal) ≠ (⊤ : EReal))),
      if_pos (trivial : True)]
    simp only [EReal.toReal_coe]
  have h1 : 1 ≤ mult (rankFn stage J) ((e : EReal), (⊥ : EReal)) := by
    rw [hopen]
    exact le_iInf₂ fun η hη => le_iInf₂ fun t ht => hge η hη t ht
  exact ENat.one_le_iff_ne_zero.mp h1

theorem t5_imageBirthStrongLower {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameY : IsTameModule stageY JY) {α ε : ℝ}
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x))
    {β : ℝ} (hβ : α ≤ β) (C : comps stageX JX β) :
    birthSup hLawX β C - ε ≤ birthSup hLawY (β - ε) (φ β hβ C) := by
  obtain ⟨s₀, hs₀⟩ := hTameY.2.2
  have hBddY : BddAbove (AncSet hLawY (β - ε) (φ β hβ C)) := by
    refine ⟨s₀, fun w hw => ?_⟩
    obtain ⟨-, C₂, -⟩ := hw
    have hstage : (stageY w).Nonempty := by
      obtain ⟨x, hx, -⟩ := C₂.property
      exact ⟨x, hx⟩
    by_contra hle
    push_neg at hle
    exact hstage.ne_empty (hs₀ w hle.le)
  have hneX : (AncSet hLawX β C).Nonempty := ⟨β, le_rfl, C, t3_structMap_id hLawX β C⟩
  have hmain : birthSup hLawX β C ≤ birthSup hLawY (β - ε) (φ β hβ C) + ε := by
    refine csSup_le hneX ?_
    intro u hu
    obtain ⟨huβ, C_u, hCu⟩ := hu
    have hαu : α ≤ u := le_trans hβ huβ
    have hpull : structMap hLawY (show β - ε ≤ u - ε by linarith) (φ u hαu C_u)
        = φ β hβ C := by
      have h1 := hSq1 β u hβ hαu huβ C_u
      rw [← hCu]
      exact h1.symm
    have hmemY : (u - ε) ∈ AncSet hLawY (β - ε) (φ β hβ C) :=
      ⟨show β - ε ≤ u - ε by linarith, φ u hαu C_u, hpull⟩
    have hle : u - ε ≤ birthSup hLawY (β - ε) (φ β hβ C) :=
      (rfl : birthSup hLawY (β - ε) (φ β hβ C)
        = sSup (AncSet hLawY (β - ε) (φ β hβ C))).symm ▸
        (le_csSup hBddY hmemY)
    linarith
  linarith

theorem t5_imageBirthUpper {ιX ιY : Type*}
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

theorem t5_l3_dichotomy {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
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

theorem t5_census_cell {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {b d η δ₀ : ℝ} (hbd : d < b)
    (hmult : mult (rankFn stage J) ((b : EReal), (d : EReal)) ≠ 0)
    (hgap : (∀ τ ∈ critSet hTame, τ ≠ b → δ₀ < |τ - b|) ∧
      (∀ τ ∈ critSet hTame, τ ≠ d → δ₀ < |τ - d|))
    (hη0 : 0 < η) (hηδ : η < δ₀) (hηbd : η < (b - d) / 2) :
    ∃ C₀ : comps stage J (d + η), birthSup hLaw (d + η) C₀ = b := by
  have h1 : 1 ≤ mult (rankFn stage J) ((b : EReal), (d : EReal)) :=
    Order.one_le_iff_ne_zero.mpr hmult
  rw [t3_mult_unfold hLaw hbd] at h1
  have h2 : 1 ≤ t3_comb stage J b d η := h1.trans (iInf₂_le η ⟨hη0, hηbd⟩)
  rw [t3_comb_small hLaw hTame hbd hgap ⟨hη0, hηδ⟩ hηbd] at h2
  have hA : 1 ≤ ({C : comps stage J (d + η) | birthSup hLaw (d + η) C = b} :
      Set (comps stage J (d + η))).encard := h2.trans tsub_le_self
  have hne : ({C : comps stage J (d + η) | birthSup hLaw (d + η) C = b} :
      Set (comps stage J (d + η))).Nonempty := by
    by_contra hcon
    rcases Set.eq_empty_or_nonempty ({C : comps stage J (d + η) |
        birthSup hLaw (d + η) C = b} : Set (comps stage J (d + η))) with hempty | ⟨C₁, hC₁⟩
    · rw [hempty, Set.encard_empty] at hA
      exact absurd hA (by simp)
    · exact hcon ⟨C₁, hC₁⟩
  obtain ⟨C₀, hC₀⟩ := hne
  exact ⟨C₀, hC₀⟩

theorem t5_partnerAbsorb {ιY : Type*} {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawY : FiltrationLaw stageY JY) (hTameY : IsTameModule stageY JY)
    {α ε b e aw v : ℝ} {J : comps stageY JY ((α + ε) - ε)}
    (heα : α < e) (hband_lo : b - ε ≤ e) (hband_hi : e ≤ b + ε)
    (haw : aw ≤ α - 1) (hvlo : aw ≤ v) (hvhi : v ≤ (α + ε) - ε)
    (hAbove : ∀ (ξ : ℝ) (hξ : ξ ≤ (α + ε) - ε), v < ξ →
      birthSup hLawY ξ (structMap hLawY hξ J) = e)
    (hBelow : ∀ (ξ : ℝ) (hξ : ξ ≤ (α + ε) - ε), aw ≤ ξ → ξ < v →
      birthSup hLawY ξ (structMap hLawY hξ J) ≠ e)
    (hbot : ∀ (hvle : aw ≤ (α + ε) - ε), v ≤ aw →
      birthSup hLawY aw (structMap hLawY hvle J) ≠ e)
    (he : birthSup hLawY ((α + ε) - ε) J = e) :
    ∃ m : EReal, m ≤ (α : EReal) ∧ closeE ((b : EReal)) ((e : EReal)) ((ε : ℝ)) ∧
      mult (rankFn stageY JY) ((e : EReal), m) ≠ 0 := by
  refine ⟨(v : EReal), EReal.coe_le_coe_iff.mpr (show v ≤ α by linarith), ?_, ?_⟩
  · show (b : EReal) ≤ (e : EReal) + (ε : EReal) ∧
      (e : EReal) ≤ (b : EReal) + (ε : EReal)
    refine ⟨?_, ?_⟩
    · rw [← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (by linarith)
    · rw [← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (by linarith)
  · -- the census absorb at (e, v)
    obtain ⟨δ₁, hδ₁0, hδ₁le, hgapbe, hgapbv⟩ :=
      t3_stable_delta hLawY hTameY (show v < e by linarith)
    by_cases hvw : v = (α + ε) - ε
    · -- (i) boundary at the top: hthr-cells are the aliveUp-ancestors above the level
      have hδm : min δ₁ 1 ≤ δ₁ := min_le_left _ _
      have hδ1 : min δ₁ 1 ≤ 1 := min_le_right _ _
      have hδe : min δ₁ 1 ≤ (e - v) / 2 := le_trans hδm hδ₁le
      refine t5_census_absorb hLawY hTameY (show v < e by linarith)
        (lt_min hδ₁0 one_pos) hδe
        ⟨fun τ hτ hτne => lt_of_le_of_lt hδm (hgapbe τ hτ hτne),
          fun τ hτ hτne => lt_of_le_of_lt hδm (hgapbv τ hτ hτne)⟩ ?_
      intro η hη
      obtain ⟨hη0', hηδ⟩ := hη
      obtain ⟨C, hCb, hCd⟩ := t5_aliveUp hLawY hTameY he
        (show (α + ε) - ε ≤ v + η by linarith) (show v + η < e by linarith)
      refine ⟨C, hCb, ?_⟩
      intro hle
      have h1 := hBelow (v - η) (show v - η ≤ (α + ε) - ε by linarith)
        (show aw ≤ v - η by linarith) (show v - η < v by linarith)
      have hdesc : structMap hLawY hle C
          = structMap hLawY (show v - η ≤ (α + ε) - ε by linarith) J :=
        (structMap_comp hLawY (show v - η ≤ (α + ε) - ε by linarith)
            (show (α + ε) - ε ≤ v + η by linarith) C).symm.trans
          (congrArg (structMap hLawY (show v - η ≤ (α + ε) - ε by linarith)) hCd)
      rw [hdesc]
      exact h1
    · by_cases hvb : v = aw
      · -- (ii) boundary at the window bottom: bottom-value conjunct + monotonicity
        subst v
        have hδm : min δ₁ 1 ≤ δ₁ := min_le_left _ _
        have hδ1 : min δ₁ 1 ≤ 1 := min_le_right _ _
        have hδe : min δ₁ 1 ≤ (e - aw) / 2 := le_trans hδm hδ₁le
        refine t5_census_absorb hLawY hTameY (show aw < e by linarith)
          (lt_min hδ₁0 one_pos) hδe
          ⟨fun τ hτ hτne => lt_of_le_of_lt hδm (hgapbe τ hτ hτne),
            fun τ hτ hτne => lt_of_le_of_lt hδm (hgapbv τ hτ hτne)⟩ ?_
        intro η hη
        obtain ⟨hη0', hηδ⟩ := hη
        have hvηw₀ : aw + η ≤ (α + ε) - ε := by linarith
        refine ⟨structMap hLawY hvηw₀ J, hAbove (aw + η) hvηw₀ (by linarith), ?_⟩
        intro hle
        have hEv : birthSup hLawY aw (structMap hLawY hvhi J) ≠ e := hbot hvhi le_rfl
        have hEvge : e ≤ birthSup hLawY aw (structMap hLawY hvhi J) := by
          have h1 := hAbove (aw + η) hvηw₀ (by linarith)
          have h2 := rungB_bSup_descend_ge hLawY hTameY
            (show aw ≤ aw + η by linarith) (structMap hLawY hvηw₀ J)
          rw [structMap_comp hLawY (show aw ≤ aw + η by linarith) hvηw₀ J] at h2
          rw [h1] at h2
          exact h2
        have hdesc : structMap hLawY hle (structMap hLawY hvηw₀ J)
            = structMap hLawY (show aw - η ≤ aw by linarith)
                (structMap hLawY hvhi J) :=
          (structMap_comp hLawY hle hvηw₀ J).trans
            (structMap_comp hLawY (show aw - η ≤ aw by linarith) hvhi J).symm
        rw [hdesc]
        have h3 := rungB_bSup_descend_ge hLawY hTameY
          (show aw - η ≤ aw by linarith) (structMap hLawY hvhi J)
        exact ne_of_gt (lt_of_lt_of_le (lt_of_le_of_ne hEvge (Ne.symm hEv)) h3)
      · -- (iii) interior boundary: chain-cells above, hBelow below
        have hvawlt : aw < v := by
          rcases lt_or_eq_of_le hvlo with h | h
          · exact h
          · exact absurd h.symm hvb
        have hvwlt : v < (α + ε) - ε := by
          rcases lt_or_eq_of_le hvhi with h | h
          · exact h
          · exact absurd h hvw
        have hδm : min δ₁ (min (v - aw) ((α + ε) - ε - v)) ≤ δ₁ :=
          min_le_left _ _
        have hδa : min δ₁ (min (v - aw) ((α + ε) - ε - v)) ≤ v - aw :=
          le_trans (min_le_right _ _) (min_le_left _ _)
        have hδw : min δ₁ (min (v - aw) ((α + ε) - ε - v)) ≤ (α + ε) - ε - v :=
          le_trans (min_le_right _ _) (min_le_right _ _)
        have hδe : min δ₁ (min (v - aw) ((α + ε) - ε - v)) ≤ (e - v) / 2 :=
          le_trans hδm hδ₁le
        refine t5_census_absorb hLawY hTameY (show v < e by linarith)
          (lt_min hδ₁0 (lt_min (by linarith) (by linarith))) hδe
          ⟨fun τ hτ hτne => lt_of_le_of_lt hδm (hgapbe τ hτ hτne),
            fun τ hτ hτne => lt_of_le_of_lt hδm (hgapbv τ hτ hτne)⟩ ?_
        intro η hη
        obtain ⟨hη0', hηδ⟩ := hη
        have hvηw₀ : v + η ≤ (α + ε) - ε := by linarith
        refine ⟨structMap hLawY hvηw₀ J, hAbove (v + η) hvηw₀ (by linarith), ?_⟩
        intro hle
        rw [structMap_comp hLawY hle hvηw₀ J]
        exact hBelow (v - η) (le_trans hle hvηw₀) (by linarith) (by linarith)


/-- T3a-ii(a): no bar dies at a non-critical level — the death-pinning. -/
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

/-- qseDry12: the LEVEL-GENERIC partner absorb — `t5_partnerAbsorb` with the image level
`(α+ε)−ε` abstracted to `wtop` and the window bottom `α−1` abstracted to `aw` (no death pin — the callers assemble the QSE death
disjunction at the raw break `v` themselves). The
hQP high-lift fill runs its dichotomy at the image level `β−ε > α`, where the hardwired
version no longer applies; the three boundary cases (break at the window top / bottom /
interior) mirror `t5_partnerAbsorb` verbatim. `hawlen : 1 ≤ wtop − aw` carries the
template's implicit `aw = (α+ε)−ε − 1` fact (the `min δ₁ 1` probe craft needs probe radii
below the window length). -/
theorem t5_partnerAbsorbGen {ιY : Type*} {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawY : FiltrationLaw stageY JY) (hTameY : IsTameModule stageY JY)
    {ε b e aw wtop v : ℝ} {J : comps stageY JY wtop}
    (hband_lo : b - ε ≤ e) (hband_hi : e ≤ b + ε)
    (hwtope : wtop < e) (hawlen : 1 ≤ wtop - aw)
    (hvlo : aw ≤ v) (hvhi : v ≤ wtop)
    (hAbove : ∀ (ξ : ℝ) (hξ : ξ ≤ wtop), v < ξ →
      birthSup hLawY ξ (structMap hLawY hξ J) = e)
    (hBelow : ∀ (ξ : ℝ) (hξ : ξ ≤ wtop), aw ≤ ξ → ξ < v →
      birthSup hLawY ξ (structMap hLawY hξ J) ≠ e)
    (hbot : ∀ (hvle : aw ≤ wtop), v ≤ aw →
      birthSup hLawY aw (structMap hLawY hvle J) ≠ e)
    (he : birthSup hLawY wtop J = e) :
    closeE ((b : EReal)) ((e : EReal)) ((ε : ℝ)) ∧
      mult (rankFn stageY JY) ((e : EReal), ((v : EReal))) ≠ 0 := by
  refine ⟨?_, ?_⟩
  · show (b : EReal) ≤ (e : EReal) + (ε : EReal) ∧
      (e : EReal) ≤ (b : EReal) + (ε : EReal)
    refine ⟨?_, ?_⟩
    · rw [← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (by linarith)
    · rw [← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr hband_hi
  · -- the census absorb at (e, v)
    obtain ⟨δ₁, hδ₁0, hδ₁le, hgapbe, hgapbv⟩ :=
      t3_stable_delta hLawY hTameY (show v < e by linarith)
    by_cases hvw : v = wtop
    · -- (i) boundary at the top: hthr-cells are the aliveUp-ancestors above the level
      have hδm : min δ₁ 1 ≤ δ₁ := min_le_left _ _
      have hδ1 : min δ₁ 1 ≤ 1 := min_le_right _ _
      have hδe : min δ₁ 1 ≤ (e - v) / 2 := le_trans hδm hδ₁le
      refine t5_census_absorb hLawY hTameY (show v < e by linarith)
        (lt_min hδ₁0 one_pos) hδe
        ⟨fun τ hτ hτne => lt_of_le_of_lt hδm (hgapbe τ hτ hτne),
          fun τ hτ hτne => lt_of_le_of_lt hδm (hgapbv τ hτ hτne)⟩ ?_
      intro η hη
      obtain ⟨hη0', hηδ⟩ := hη
      obtain ⟨C, hCb, hCd⟩ := t5_aliveUp hLawY hTameY he
        (show wtop ≤ v + η by linarith) (show v + η < e by linarith)
      refine ⟨C, hCb, ?_⟩
      intro hle
      have h1 := hBelow (v - η) (show v - η ≤ wtop by linarith)
        (show aw ≤ v - η by linarith) (show v - η < v by linarith)
      have hdesc : structMap hLawY hle C
          = structMap hLawY (show v - η ≤ wtop by linarith) J :=
        (structMap_comp hLawY (show v - η ≤ wtop by linarith)
            (show wtop ≤ v + η by linarith) C).symm.trans
          (congrArg (structMap hLawY (show v - η ≤ wtop by linarith)) hCd)
      rw [hdesc]
      exact h1
    · by_cases hvb : v = aw
      · -- (ii) boundary at the window bottom: bottom-value conjunct + monotonicity
        subst v
        have hδm : min δ₁ 1 ≤ δ₁ := min_le_left _ _
        have hδ1 : min δ₁ 1 ≤ 1 := min_le_right _ _
        have hδe : min δ₁ 1 ≤ (e - aw) / 2 := le_trans hδm hδ₁le
        refine t5_census_absorb hLawY hTameY (show aw < e by linarith)
          (lt_min hδ₁0 one_pos) hδe
          ⟨fun τ hτ hτne => lt_of_le_of_lt hδm (hgapbe τ hτ hτne),
            fun τ hτ hτne => lt_of_le_of_lt hδm (hgapbv τ hτ hτne)⟩ ?_
        intro η hη
        obtain ⟨hη0', hηδ⟩ := hη
        have hvηw₀ : aw + η ≤ wtop := by linarith
        refine ⟨structMap hLawY hvηw₀ J, hAbove (aw + η) hvηw₀ (by linarith), ?_⟩
        intro hle
        have hEv : birthSup hLawY aw (structMap hLawY hvhi J) ≠ e := hbot hvhi le_rfl
        have hEvge : e ≤ birthSup hLawY aw (structMap hLawY hvhi J) := by
          have h1 := hAbove (aw + η) hvηw₀ (by linarith)
          have h2 := rungB_bSup_descend_ge hLawY hTameY
            (show aw ≤ aw + η by linarith) (structMap hLawY hvηw₀ J)
          rw [structMap_comp hLawY (show aw ≤ aw + η by linarith) hvηw₀ J] at h2
          rw [h1] at h2
          exact h2
        have hdesc : structMap hLawY hle (structMap hLawY hvηw₀ J)
            = structMap hLawY (show aw - η ≤ aw by linarith)
                (structMap hLawY hvhi J) :=
          (structMap_comp hLawY hle hvηw₀ J).trans
            (structMap_comp hLawY (show aw - η ≤ aw by linarith) hvhi J).symm
        rw [hdesc]
        have h3 := rungB_bSup_descend_ge hLawY hTameY
          (show aw - η ≤ aw by linarith) (structMap hLawY hvhi J)
        exact ne_of_gt (lt_of_lt_of_le (lt_of_le_of_ne hEvge (Ne.symm hEv)) h3)
      · -- (iii) interior boundary: chain-cells above, hBelow below
        have hvawlt : aw < v := by
          rcases lt_or_eq_of_le hvlo with h | h
          · exact h
          · exact absurd h.symm hvb
        have hvwlt : v < wtop := by
          rcases lt_or_eq_of_le hvhi with h | h
          · exact h
          · exact absurd h hvw
        have hδm : min δ₁ (min (v - aw) (wtop - v)) ≤ δ₁ :=
          min_le_left _ _
        have hδa : min δ₁ (min (v - aw) (wtop - v)) ≤ v - aw :=
          le_trans (min_le_right _ _) (min_le_left _ _)
        have hδw : min δ₁ (min (v - aw) (wtop - v)) ≤ wtop - v :=
          le_trans (min_le_right _ _) (min_le_right _ _)
        have hδe : min δ₁ (min (v - aw) (wtop - v)) ≤ (e - v) / 2 :=
          le_trans hδm hδ₁le
        refine t5_census_absorb hLawY hTameY (show v < e by linarith)
          (lt_min hδ₁0 (lt_min (by linarith) (by linarith))) hδe
          ⟨fun τ hτ hτne => lt_of_le_of_lt hδm (hgapbe τ hτ hτne),
            fun τ hτ hτne => lt_of_le_of_lt hδm (hgapbv τ hτ hτne)⟩ ?_
        intro η hη
        obtain ⟨hη0', hηδ⟩ := hη
        have hvηw₀ : v + η ≤ wtop := by linarith
        refine ⟨structMap hLawY hvηw₀ J, hAbove (v + η) hvηw₀ (by linarith), ?_⟩
        intro hle
        rw [structMap_comp hLawY hle hvηw₀ J]
        exact hBelow (v - η) (le_trans hle hvηw₀) (by linarith) (by linarith)

/-- REPAIR-QSE-2 (RQSE-3 lane, 2026-10-14): the LOW-BAND elder trap — `t5_elderTrap`
with the `α ≤ v − ε` pin DROPPED. That hypothesis is vestigial in `t5_elderTrap`'s proof
(the ancestor chase runs ψ at the probe level `v ≥ α` and the X-side pin is the hypothesis
`hbC₀`; neither touches `v − ε`'s relation to `α`), but it is unprovable in the LOW band
`d ≤ α`, where the interleaved Y-ray carries probes `v ∈ (d + ε, α + ε)` with `v − ε < α`.
Everything else is `t5_elderTrap` verbatim. -/
theorem t5_elderTrapLo {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
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
    (hvα : α ≤ v) (hs₀v : s₀ ≤ v - ε)
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

/-- Route B (design §8.16.9): the LOW-band QSE partner — the death lies INSIDE the band
[α−ε, α], where `t5_qsePartnerHi`'s floor pin (η < α−ε−d) cannot be placed. PORT-LANE
PORT (2026-10-13): the trunk's two internal open sites are carried over as NAMED port
seals — `loHole1` (P0: the ε = 0 degenerate branch) and `loHole2` (P3b: the upper band
e ≤ b + ε, sealed NOT derivable from the stated hypotheses; the in-proof note documents
the counterexample). All other glue (census pin at d+η, aliveUp to the floor-source lift
level α+ε, image-birth lower band, dichotomy at [α−1, α], partnerAbsorb /
essential-mult finish) is verbatim.
Ported verbatim from the qseDry1 trunk for the rankKill essB seal (port_lane). -/
theorem solution {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameX : IsTameModule stageX JX) (hTameY : IsTameModule stageY JY)
    {α ε : ℝ} (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x))
    (hSq2 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (y : comps stageY JY β'),
      ψ β hβ (structMap hLawY hle y) =
        structMap hLawX (show β - ε ≤ β' - ε by linarith) (ψ β' hβ' y))
    (hSq4 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (x : comps stageX JX β),
      ψ (β - ε) hβε (φ β hβ x) =
        structMap hLawX (show (β - ε) - ε ≤ β by linarith) x)
    {b d : ℝ} (hbd : d < b) (hdlo : α - ε ≤ d) (hdhi : d ≤ α) (hbαε : α + ε < b)
    (hpx : mult (rankFn stageX JX) ((b : EReal), (d : EReal)) ≠ 0)
    (hgate : 2 * ε < b - d)
    -- REPAIR-QSE (2026-10-14, banked repair map Entry 22): `hband_hi` ORPHANED —
    -- REFUTED by the ε-shift interleaving (hgate-VALID; all four squares hold):
    -- the value-b cell's φ-image may carry an ELDER's birth (e = 6 > b+ε = 3.5
    -- in the banked counterexample), so the upper band e ≤ b+ε is UNDERIVABLE
    -- in general. The conclusion's partner conjunct is restated DISJUNCTIVELY:
    -- the partner either stays in QSE (m ≤ α) or crosses into QNE death-ε-close
    -- to the tracked thread's death d (the ε-shift honest partner is (b+ε, d+ε)
    -- — the SAME thread tracked to its death; birth-closeness stays the separate
    -- closeE conjunct either way).
    :
    ∃ e : ℝ, ∃ m : EReal, (α : EReal) < (e : EReal) ∧
      (m ≤ (α : EReal) ∨ ((α : EReal) < m ∧ closeE ((d : EReal)) m ((ε : ℝ)))) ∧
      closeE ((b : EReal)) ((e : EReal)) ((ε : ℝ)) ∧
      mult (rankFn stageY JY) ((e : EReal), m) ≠ 0 := by
  -- ROUTE B (low band d ∈ [α−ε, α]), restructured onto the FLOOR-source lift
  -- (β := α+ε): the in-file census machinery (`t5_partnerAbsorb`,
  -- `t3_essential_mult`) is hardwired to the level-α image cell, so the Hi
  -- template's steps (2)–(7) mirror verbatim; the ONLY step that does not
  -- transfer is the UPPER band (imageBirthUpper's hDesc pin at α−ε needs
  -- d+η ≤ α−2ε, i.e. the Hi `hroom` d < α−ε, excluded by the low band).
  rcases eq_or_lt_of_le hε with rfl | hεpos
  · -- (P0) ε = 0 DEGENERATE: d = α. LOH-4 green extraction: census cell C₀ at
    --   level d+η with value b (η below the stability window), then BOTH bands
    --   for the level-(d+η) image cell φ (d+η) C₀ — at ε = 0 the double-descent
    --   pin level (β-0)-0 = β = d+η coincides with the census level itself, so
    --   imageBirthUpper applies at β = d+η (no crossing INTO d, no floor lift).
    -- PORT-HOLE(loHole1): trunk hole site (qseDry1 L4361) ported verbatim as a
    --   NAMED seal — the ε = 0 degenerate branch (P0) of this band lemma.
    have hP0d : d = α := by linarith
    have hP0ba : α < b := by linarith
    obtain ⟨δ₀, hδ0, hδle, hgap⟩ := t3_stable_delta hLawX hTameX hbd
    obtain ⟨η, hη0, hηδ, hηbd⟩ : ∃ η : ℝ, 0 < η ∧ η < δ₀ ∧ η < (b - d) / 2 := by
      refine ⟨min (δ₀ / 2) ((b - d) / 4), ?_, ?_, ?_⟩
      · exact lt_min (by linarith) (by linarith)
      · have h1 : min (δ₀ / 2) ((b - d) / 4) ≤ δ₀ / 2 := min_le_left _ _
        linarith
      · have h1 : min (δ₀ / 2) ((b - d) / 4) ≤ (b - d) / 4 := min_le_right _ _
        linarith
    obtain ⟨C₀, hC₀⟩ := t5_census_cell hLawX hTameX hbd hpx hgap hη0 hηδ hηbd
    have hβα : α ≤ d + η := by linarith
    -- (P0a) lower band: strong lower at the census level (ε = 0 mirror of P3).
    have hband_lo : b - 0 ≤
        birthSup hLawY ((d + η) - 0) (φ (d + η) hβα C₀) := by
      rw [← hC₀]
      exact t5_imageBirthStrongLower hLawX hLawY hTameY φ hSq1 hβα C₀
    -- (P0b) the ε = 0 double-descent pin: at β = d+η the pin level (β-0)-0 = β
    --   coincides with the census level, so t5_hDescPin runs with s₀ = β = d+η
    --   and the identity descent (no crossing INTO the critical level d).
    have hP0pin : birthSup hLawX ((d + η) - 0 - 0)
        (structMap hLawX (show (d + η) - 0 - 0 ≤ d + η by linarith) C₀) = b :=
      t5_hDescPin hLawX hTameX hC₀ le_rfl
        (show (d + η) - 0 - 0 ≤ d + η by linarith)
        (show d + η ≤ (d + η) - 0 - 0 by linarith) hC₀
        (t3_structMap_id hLawX (d + η) C₀)
    -- (P0c) upper band: imageBirthUpper at the census level — GREEN at ε = 0
    --   (unlike the P1 floor-source level α+ε, which needs d+η ≤ α-2ε).
    have hP0hi : birthSup hLawY ((d + η) - 0) (φ (d + η) hβα C₀) ≤ b + 0 :=
      t5_imageBirthUpper hLawX hLawY hTameX hε φ ψ hSq2 hSq4 hβα
        (show α ≤ (d + η) - 0 by linarith) C₀ hP0pin
    obtain ⟨e, he⟩ : ∃ e : ℝ,
        birthSup hLawY ((d + η) - 0) (φ (d + η) hβα C₀) = e := ⟨_, rfl⟩
    rw [he] at hband_lo hP0hi
    have heα : α < e := by linarith
    -- (P0d) INTERIOR VALUE PIN (LOH-4): the ε = 0 image thread carries value
    --   EXACTLY e = b at every level t ∈ (α, d+η]: the X-thread pin holds there
    --   (t3_bSupThread — (d, d+η] is crit-free by the δ₀-gap around d), and
    --   at ε = 0 imageBirthUpper's double-descent pin is the identity at β = t.
    have hQ : ∀ (t : ℝ) (ht1 : α < t) (ht2 : t ≤ d + η) (hle : t - 0 ≤ (d + η) - 0),
        birthSup hLawY (t - 0)
          (structMap hLawY hle (φ (d + η) hβα C₀)) = e := by
      intro t ht1 ht2 hle
      have hfree : ∀ τ ∈ critSet hTameX, τ < t ∨ d + η < τ := by
        intro τ hτ
        by_contra hcon
        push_neg at hcon
        have hτd : τ ≠ d := by
          by_contra hτe
          rw [hτe] at hcon
          linarith
        have h2 := hgap.2 τ hτ hτd
        rw [abs_of_nonneg (show (0 : ℝ) ≤ τ - d by linarith)] at h2
        linarith
      have hXpin : birthSup hLawX t
          (structMap hLawX (show t ≤ d + η by linarith) C₀) = b :=
        (t3_bSupThread hLawX hTameX (show t ≤ d + η by linarith) hfree rfl).trans hC₀
      have hlo := t5_imageBirthStrongLower hLawX hLawY hTameY φ hSq1
        (show α ≤ t by linarith) (structMap hLawX (show t ≤ d + η by linarith) C₀)
      rw [hXpin] at hlo
      have hpin2 : birthSup hLawX ((t - 0) - 0)
          (structMap hLawX (show (t - 0) - 0 ≤ t by linarith)
            (structMap hLawX (show t ≤ d + η by linarith) C₀)) = b :=
        t5_hDescPin hLawX hTameX hXpin le_rfl
          (show (t - 0) - 0 ≤ t by linarith)
          (show t ≤ (t - 0) - 0 by linarith) hXpin
          (t3_structMap_id hLawX t (structMap hLawX (show t ≤ d + η by linarith) C₀))
      have hup := t5_imageBirthUpper hLawX hLawY hTameX hε φ ψ hSq2 hSq4
        (show α ≤ t by linarith) (show α ≤ t - 0 by linarith)
        (structMap hLawX (show t ≤ d + η by linarith) C₀) hpin2
      rw [← hSq1 t (d + η) (show α ≤ t by linarith) hβα
        (show t ≤ d + η by linarith) C₀]
      refine le_antisymm ?_ ?_ <;> linarith
    have hclose : closeE ((b : ℝ) : EReal) ((e : ℝ) : EReal) ((0 : ℝ)) :=
      ⟨by rw [← EReal.coe_add]; exact EReal.coe_le_coe_iff.mpr (by linarith),
       by rw [← EReal.coe_add]; exact EReal.coe_le_coe_iff.mpr hP0hi⟩
    -- (P0e) value identity + GENERIC BREAK-ABSORB (LOH-4): a break of the image
    --   cell's value-ray at an INTERIOR level v of a window (aw, ·] — value e
    --   above, ≠ e below — yields the Y-bar (b, v) via t5_census_absorb. The
    --   per-η thread cells come from the ray (hAbove) below the census level
    --   and from the aliveUp-lift above it; their below-descents compose onto
    --   the ray's ≠-e data.
    have hbe : e = b := le_antisymm (by linarith) (by linarith)
    have habsorb : ∀ (vv aw : ℝ), aw < vv → vv ≤ α →
        (∀ (ξ : ℝ) (hξ1 : ξ ≤ (d + η) - 0) (hξ2 : aw ≤ ξ) (hξ3 : ξ < vv),
          birthSup hLawY ξ (structMap hLawY hξ1 (φ (d + η) hβα C₀)) ≠ e) →
        (∀ (ξ : ℝ) (hξ1 : ξ ≤ (d + η) - 0) (hξ2 : vv < ξ),
          birthSup hLawY ξ (structMap hLawY hξ1 (φ (d + η) hβα C₀)) = e) →
        mult (rankFn stageY JY) ((b : EReal), (vv : EReal)) ≠ 0 := by
      intro vv aw hawv hvvα hBelow hAbove
      have hvb : vv < b := by linarith
      obtain ⟨δ₁, hδ₁0, hδ₁le, hgap₁⟩ := t3_stable_delta hLawY hTameY hvb
      have hδ₁ : min δ₁ (vv - aw) ≤ δ₁ := min_le_left _ _
      have hδ₂ : min δ₁ (vv - aw) ≤ vv - aw := min_le_right _ _
      refine t5_census_absorb hLawY hTameY hvb (lt_min hδ₁0 (by linarith))
        (le_trans hδ₁ hδ₁le)
        ⟨fun τ hτ hτb => lt_of_le_of_lt hδ₁ (hgap₁.1 τ hτ hτb),
         fun τ hτ hτv => lt_of_le_of_lt hδ₁ (hgap₁.2 τ hτ hτv)⟩ ?_
      intro ρ hρ
      obtain ⟨hρ0, hρδ⟩ := hρ
      by_cases hcase : vv + ρ ≤ (d + η) - 0
      · refine ⟨structMap hLawY hcase (φ (d + η) hβα C₀), ?_, ?_⟩
        · rw [← hbe]
          exact hAbove (vv + ρ) hcase (by linarith)
        · intro hle
          have hlo1 : vv - ρ ≤ (d + η) - 0 := by linarith
          rw [structMap_comp hLawY hle hcase (φ (d + η) hβα C₀)]
          have hne := hBelow (vv - ρ) hlo1 (show aw ≤ vv - ρ by linarith)
            (show vv - ρ < vv by linarith)
          rw [hbe] at hne
          exact hne
      · obtain ⟨A, hAval, hAdesc⟩ := t5_aliveUp hLawY hTameY (he.trans hbe)
          (show (d + η) - 0 ≤ vv + ρ by linarith)
          (show vv + ρ < b by linarith)
        refine ⟨A, hAval, ?_⟩
        intro hle
        have hlo1 : vv - ρ ≤ (d + η) - 0 := by linarith
        have hcell : structMap hLawY hle A = structMap hLawY hlo1
            (φ (d + η) hβα C₀) :=
          Eq.trans (structMap_comp hLawY hlo1
            (show (d + η) - 0 ≤ vv + ρ by linarith) A).symm
            (congrArg (structMap hLawY hlo1) hAdesc)
        rw [hcell]
        have hne := hBelow (vv - ρ) hlo1 (show aw ≤ vv - ρ by linarith)
          (show vv - ρ < vv by linarith)
        rw [hbe] at hne
        exact hne
    -- PORT-HOLE(loHole1) core — CLEARED (REPAIR-LO, 2026-10-14): the LOH-4 blocker
    --   ("extracting a Y-bar (e, m) with m ≤ α resists") is resolved by porting the
    --   P3 tail's P6 pattern onto the level-(d+η) image cell: `t5_l3_dichotomy` at
    --   window-bottom α−1; hQ forces the break v ≤ α (an hQ/hBelow clash above α);
    --   the in-branch `habsorb` (NOT level-α-hardwired, unlike `t5_partnerAbsorb`)
    --   finishes the in-window break; the boundary v = window-bottom dies via the
    --   hbot off-value + one dichotomy re-run one level lower; the everywhere-e
    --   residue closes by `t3_essential_mult` (the essential bar (e, ⊥)).
    have hP0_witness : ∃ m : EReal, m ≤ (α : EReal) ∧
        mult (rankFn stageY JY) ((e : EReal), m) ≠ 0 := by
      -- LOH-4 CLEARED (REPAIR-LO, 2026-10-14): the P6 dichotomy/absorb pattern
      --   ported onto the level-(d+η) image cell — the in-branch `habsorb` is NOT
      --   level-α-hardwired; hQ forces the dichotomy's break v ≤ α (an hQ/hBelow
      --   clash above α); the boundary v = window-bottom dies via the hbot
      --   off-value + one dichotomy re-run one level lower.
      rcases t5_l3_dichotomy hLawY hTameY (φ (d + η) hβα C₀) he
          (show α - 1 ≤ (d + η) - 0 by linarith) with hfull | hout
      · -- (F1) full ray on [α−1, d+η]: probe below the window (P6 pattern).
        by_cases hoff : ∃ (w : ℝ) (hw : w ≤ (d + η) - 0), w ≤ α - 1 ∧
            birthSup hLawY w (structMap hLawY hw (φ (d + η) hβα C₀)) ≠ e
        · obtain ⟨w, hw, hwle, hwne⟩ := hoff
          rcases t5_l3_dichotomy hLawY hTameY (φ (d + η) hβα C₀) he
              (show w - 1 ≤ (d + η) - 0 by linarith) with hfull₂ | hout₂
          · exact absurd (hfull₂ w hw (show w - 1 ≤ w by linarith)) hwne
          · obtain ⟨v, hvlo, hvhi, hAbove, hBelow, hbot⟩ := hout₂
            by_cases hva : α < v
            · have hQv := hQ ((α + v) / 2) (show α < (α + v) / 2 by linarith)
                (show (α + v) / 2 ≤ d + η by linarith)
                (show (α + v) / 2 - 0 ≤ (d + η) - 0 by linarith)
              exact absurd hQv (hBelow ((α + v) / 2 - 0)
                (show (α + v) / 2 - 0 ≤ (d + η) - 0 by linarith)
                (show w - 1 ≤ (α + v) / 2 - 0 by linarith)
                (show (α + v) / 2 - 0 < v by linarith))
            · by_cases hvb : w - 1 < v
              · have hmult := habsorb v (w - 1) hvb (by linarith) hBelow hAbove
                exact ⟨(v : EReal), EReal.coe_le_coe_iff.mpr (by linarith),
                  by rw [hbe]; exact hmult⟩
              · exact absurd (hAbove w hw (show v < w by linarith)) hwne
        · -- everywhere-e below α−1: the partner is the essential bar (e, ⊥).
          have hevery : ∀ (w : ℝ) (hw : w ≤ (d + η) - 0),
              birthSup hLawY w (structMap hLawY hw (φ (d + η) hβα C₀)) = e := by
            intro w hw
            by_cases hw1 : α - 1 ≤ w
            · exact hfull w hw hw1
            · by_contra hne
              exact hoff ⟨w, hw, (show w ≤ α - 1 by linarith), hne⟩
          exact ⟨⊥, bot_le,
            t3_essential_mult hLawY hTameY (φ (d + η) hβα C₀) he hevery⟩
      · -- (F2) break branch: hQ forces v ≤ α; boundary v = α−1 via hbot re-run.
        obtain ⟨v, hvlo, hvhi, hAbove, hBelow, hbot⟩ := hout
        by_cases hva : α < v
        · have hQv := hQ ((α + v) / 2) (show α < (α + v) / 2 by linarith)
            (show (α + v) / 2 ≤ d + η by linarith)
            (show (α + v) / 2 - 0 ≤ (d + η) - 0 by linarith)
          exact absurd hQv (hBelow ((α + v) / 2 - 0)
            (show (α + v) / 2 - 0 ≤ (d + η) - 0 by linarith)
            (show α - 1 ≤ (α + v) / 2 - 0 by linarith)
            (show (α + v) / 2 - 0 < v by linarith))
        · by_cases hvb : α - 1 < v
          · have hmult := habsorb v (α - 1) hvb (by linarith) hBelow hAbove
            exact ⟨(v : EReal), EReal.coe_le_coe_iff.mpr (by linarith),
              by rw [hbe]; exact hmult⟩
          · -- v = α−1: hbot pins the off-value at α−1; re-run one level lower.
            have hwne : birthSup hLawY (α - 1)
                (structMap hLawY (show α - 1 ≤ (d + η) - 0 by linarith)
                  (φ (d + η) hβα C₀)) ≠ e :=
              hbot (show α - 1 ≤ (d + η) - 0 by linarith) (by linarith)
            rcases t5_l3_dichotomy hLawY hTameY (φ (d + η) hβα C₀) he
                (show α - 2 ≤ (d + η) - 0 by linarith) with hfull₂ | hout₂
            · exact absurd (hfull₂ (α - 1)
                (show α - 1 ≤ (d + η) - 0 by linarith)
                (show α - 2 ≤ α - 1 by linarith)) hwne
            · obtain ⟨v₂, hvlo₂, hvhi₂, hAbove₂, hBelow₂, hbot₂⟩ := hout₂
              by_cases hva₂ : α < v₂
              · have hQv := hQ ((α + v₂) / 2) (show α < (α + v₂) / 2 by linarith)
                  (show (α + v₂) / 2 ≤ d + η by linarith)
                  (show (α + v₂) / 2 - 0 ≤ (d + η) - 0 by linarith)
                exact absurd hQv (hBelow₂ ((α + v₂) / 2 - 0)
                  (show (α + v₂) / 2 - 0 ≤ (d + η) - 0 by linarith)
                  (show α - 2 ≤ (α + v₂) / 2 - 0 by linarith)
                  (show (α + v₂) / 2 - 0 < v₂ by linarith))
              · by_cases hvb₂ : α - 2 < v₂
                · have hmult := habsorb v₂ (α - 2) hvb₂ (by linarith) hBelow₂ hAbove₂
                  exact ⟨(v₂ : EReal), EReal.coe_le_coe_iff.mpr (by linarith),
                    by rw [hbe]; exact hmult⟩
                · exact absurd (hAbove₂ (α - 1)
                    (show α - 1 ≤ (d + η) - 0 by linarith)
                    (show v₂ < α - 1 by linarith)) hwne
    obtain ⟨m, hmα, hmult⟩ := hP0_witness
    exact ⟨e, m, EReal.coe_lt_coe_iff.mpr heα, Or.inl hmα, hclose, hmult⟩
  · -- (P1) census pin at d+η, with the floor-lift room η < α+ε−d (> 0 since
    --   d ≤ α < α+ε) alongside the ceiling conditions.
    obtain ⟨δ₀, hδ0, hδle, hgap⟩ := t3_stable_delta hLawX hTameX hbd
    have hbdε : 0 < b - d - ε := by linarith
    have hαεd : 0 < α + ε - d := by linarith
    obtain ⟨η, hη0, hηδ, hηbd, hηe, hηfl⟩ :
        ∃ η : ℝ, 0 < η ∧ η < δ₀ ∧ η < (b - d) / 2 ∧ η < b - d - ε ∧
          η < α + ε - d := by
      refine ⟨min (min (δ₀ / 2) ((b - d - ε) / 4)) ((α + ε - d) / 2),
        ?_, ?_, ?_, ?_, ?_⟩
      · exact lt_min (lt_min (by linarith) (by linarith)) (by linarith)
      · have h1 : min (min (δ₀ / 2) ((b - d - ε) / 4)) ((α + ε - d) / 2)
            ≤ min (δ₀ / 2) ((b - d - ε) / 4) := min_le_left _ _
        have h2 : min (δ₀ / 2) ((b - d - ε) / 4) ≤ δ₀ / 2 := min_le_left _ _
        linarith
      · have h1 : min (min (δ₀ / 2) ((b - d - ε) / 4)) ((α + ε - d) / 2)
            ≤ min (δ₀ / 2) ((b - d - ε) / 4) := min_le_left _ _
        have h2 : min (δ₀ / 2) ((b - d - ε) / 4) ≤ (b - d - ε) / 4 := min_le_right _ _
        linarith
      · have h1 : min (min (δ₀ / 2) ((b - d - ε) / 4)) ((α + ε - d) / 2)
            ≤ min (δ₀ / 2) ((b - d - ε) / 4) := min_le_left _ _
        have h2 : min (δ₀ / 2) ((b - d - ε) / 4) ≤ (b - d - ε) / 4 := min_le_right _ _
        linarith
      · have h1 : min (min (δ₀ / 2) ((b - d - ε) / 4)) ((α + ε - d) / 2)
            ≤ (α + ε - d) / 2 := min_le_right _ _
        linarith
    obtain ⟨C₀, hC₀⟩ := t5_census_cell hLawX hTameX hbd hpx hgap hη0 hηδ hηbd
    -- (P2) alive-up to the floor-source level α+ε: value b, descending to C₀
    --   (d+η ≤ α+ε by η < α+ε−d; α+ε < b is hbαε).
    obtain ⟨A₁, hA₁b, hA₁d⟩ := t5_aliveUp hLawX hTameX hC₀
      (show d + η ≤ α + ε by linarith) hbαε
    -- (P3) the level-α image cell J' := φ (α+ε) A₁; LOWER band e ≥ b−ε.
    have hβα : α ≤ α + ε := by linarith
    have hband_lo : b - ε ≤
        birthSup hLawY ((α + ε) - ε) (φ (α + ε) hβα A₁) := by
      rw [← hA₁b]
      exact t5_imageBirthStrongLower hLawX hLawY hTameY φ hSq1 hβα A₁
    obtain ⟨e, he⟩ : ∃ e : ℝ,
        birthSup hLawY ((α + ε) - ε) (φ (α + ε) hβα A₁) = e := ⟨_, rfl⟩
    rw [he] at hband_lo
    have heα : α < e := by linarith
    -- REPAIR-QSE (2026-10-14): the P3b upper band is RETIRED with `hband_hi`
    -- (orphaned — the ε-shift counterexample: the φ-image carries an ELDER's
    -- birth, so e ≤ b+ε fails, and with it the absorb/(e,⊥) partners' closeE
    -- b e ε). The disjunct's second arm is the TRACKED THREAD's DEATH: the
    -- honest partner is (b+ε, d+ε) — the SAME thread tracked to its death
    -- (birth b±ε from the ε-shift; death d±ε at the thread's death level).
    -- Death-pin attempts (both resisted, on record above):
    -- (1) t5_imageBirthUpper — needs the hDesc pin s₀ = d+η ≤ α−ε, impossible
    --     in the low band (α−ε ≤ d < d+η) [route (a), LOH-6 record];
    -- (2) t5_l3_dichotomy + t5_partnerAbsorb — the absorb's outputs and the
    --     (e,⊥) finish all consume hP3b (e ≤ b+ε) itself [route (b), LOH-6].
    -- Per the repair map's fallback: sealed as ONE named blocker. The first
    -- arm stays green via the P0 route; the assembly below is mechanical.
    have hTrackDeath : ∃ e : ℝ, ∃ m : EReal, (α : EReal) < (e : EReal) ∧
      (m ≤ (α : EReal) ∨ ((α : EReal) < m ∧ closeE ((d : EReal)) m ((ε : ℝ)))) ∧
      closeE ((b : EReal)) ((e : EReal)) ((ε : ℝ)) ∧
      mult (rankFn stageY JY) ((e : EReal), m) ≠ 0 := by
      -- REPAIR-QSE-2 (RQSE-3 lane, 2026-10-14): the tracked thread's honest
      -- partner — the seal BELOW closes it; see the step comments (S1)–(S8).
      -- (S1) the Y-stability gap at the honest pair (d+ε, b+ε): no Y-critical
      --   level within δ₁ of the honest death d+ε except possibly itself.
      obtain ⟨δ₁, hδ₁0, hδ₁le, hgapY⟩ :=
        t3_stable_delta hLawY hTameY (show d + ε < b + ε by linarith)
      -- (S2) the probe offset μ: inside the δ₁-gap (the shallow window that
      --   refutes in-window breaks) and inside the gate slack b−d−2ε (so the
      --   probe level (d+2ε+μ)−ε stays strictly below the birth-band floor
      --   b−ε ≤ b*, the census absorb's level-below-value side condition).
      obtain ⟨μ, hμ0, hμδ, hμslack⟩ :
          ∃ μ : ℝ, 0 < μ ∧ μ < δ₁ ∧ μ < b - d - 2 * ε := by
        refine ⟨min δ₁ (b - d - 2 * ε) / 2, ?_, ?_, ?_⟩
        · have h1 : 0 < min δ₁ (b - d - 2 * ε) := lt_min hδ₁0 (by linarith)
          linarith
        · have h1 : min δ₁ (b - d - 2 * ε) ≤ δ₁ := min_le_left _ _
          linarith
        · have h1 : min δ₁ (b - d - 2 * ε) ≤ b - d - 2 * ε := min_le_right _ _
          linarith
      -- (S3) the transport level β: above the double-shift floor d+2ε+μ (so
      --   the probe cell's level and pin live inside the X-ray window (d, β]),
      --   below b (the aliveUp lift bound).
      obtain ⟨β, hβlo, hβb⟩ : ∃ β : ℝ, d + 2 * ε + μ < β ∧ β < b := by
        refine ⟨(d + 2 * ε + μ + b) / 2, ?_, ?_⟩
        · linarith
        · linarith
      have hβαβ : α ≤ β := by linarith
      have hβεβ : α ≤ β - ε := by linarith
      have hηβ : d + η ≤ β := by linarith
      -- (S4) the aliveUp-lift A of the census cell at level β, with the flat
      --   X-ray pin family on [d+η, β] (Rung-D: the descent value is exactly
      --   b at every level between the census level and the lift level).
      obtain ⟨A, hA, hAd⟩ := t5_aliveUp hLawX hTameX hC₀
        (show d + η ≤ β by linarith) (show β < b by linarith)
      have hpin : ∀ s : ℝ, d + η ≤ s → ∀ hsβ : s ≤ β,
          birthSup hLawX s (structMap hLawX hsβ A) = b := by
        intro s hs₀ hsb
        exact t5_hDescPin hLawX hTameX hC₀ (show d + η ≤ β by linarith)
          hsb hs₀ hA hAd
      -- (S5) the flat X-ray pin on the FULL window (d, β]: the hDescPin family
      --   on [d+η, β], and the crit-free `t3_bSupThread` transport on (d, d+η]
      --   (any X-critical τ there has 0 < τ − d ≤ η < δ₀, contradicting the
      --   stable-δ₀ gap at d) — the pin's composition through the census cell.
      have hXpin : ∀ s : ℝ, d < s → ∀ hsβ : s ≤ β,
          birthSup hLawX s (structMap hLawX hsβ A) = b := by
        intro s hs hsb
        by_cases hcase : d + η ≤ s
        · exact hpin s hcase hsb
        · have hfree : ∀ τ ∈ critSet hTameX, τ < s ∨ d + η < τ := by
            intro τ hτ
            by_contra hcon
            push_neg at hcon
            have hτd : τ ≠ d := by
              by_contra hτe
              rw [hτe] at hcon
              linarith
            have h2 := hgap.2 τ hτ hτd
            rw [abs_of_nonneg (show (0 : ℝ) ≤ τ - d by linarith)] at h2
            linarith
          have hjoin : structMap hLawX (show s ≤ β by linarith) A =
              structMap hLawX (show s ≤ d + η by linarith) C₀ := by
            rw [(structMap_comp hLawX (show s ≤ d + η by linarith)
              (show d + η ≤ β by linarith) A).symm, hAd]
          rw [hjoin]
          exact (t3_bSupThread hLawX hTameX (show s ≤ d + η by linarith) hfree
            (C'' := C₀) rfl).trans hC₀
      -- (S6) the probe cell: the descent of the image cell φ β A at the probe
      --   level w* := (d+2ε+μ)−ε. Its φ-source d+2ε+μ sits in the X-ray window
      --   (d, β] (hXpin pins the descent at b); the probe level sits strictly
      --   inside elderTrapLo's capped zone (d+ε, β−ε] and strictly below the
      --   birth-band floor b−ε (μ < b−d−2ε — the absorb's level-below-value
      --   side condition); and the whole probe window (d+ε, w*] is Y-crit-free
      --   (μ < δ₁, S1) — the death-control zone.
      have hβu : α ≤ d + 2 * ε + μ := by linarith
      have hle : d + 2 * ε + μ ≤ β := by linarith
      have hwε : (d + 2 * ε + μ) - ε ≤ β - ε := by linarith
      have hApin : birthSup hLawX (d + 2 * ε + μ)
          (structMap hLawX hle A) = b :=
        hXpin (d + 2 * ε + μ) (show d < d + 2 * ε + μ by linarith) hle
      have hDimage : φ (d + 2 * ε + μ) hβu (structMap hLawX hle A) =
          structMap hLawY (show (d + 2 * ε + μ) - ε ≤ β - ε by linarith)
            (φ β hβαβ A) :=
        hSq1 (d + 2 * ε + μ) β hβu hβαβ hle A
      have hband_lo : b - ε ≤ birthSup hLawY ((d + 2 * ε + μ) - ε)
          (structMap hLawY hwε (φ β hβαβ A)) := by
        have h := t5_imageBirthStrongLower hLawX hLawY hTameY φ hSq1 hβu
          (structMap hLawX hle A)
        rw [hDimage] at h
        rw [hApin] at h
        exact h
      have hband_hi : birthSup hLawY ((d + 2 * ε + μ) - ε)
          (structMap hLawY hwε (φ β hβαβ A)) ≤ b + ε :=
        t5_elderTrapLo hLawX hLawY hTameX hTameY hε φ ψ hSq2 hSq4 hβαβ hβεβ hA
          (hXpin (d + μ) (show d < d + μ by linarith) (show d + μ ≤ β by linarith))
          (show d + μ ≤ β by linarith) rfl (show d + 2 * ε < β by linarith)
          (show d + ε < (d + 2 * ε + μ) - ε by linarith)
          (show (d + 2 * ε + μ) - ε ≤ β - ε by linarith)
          (show α ≤ (d + 2 * ε + μ) - ε by linarith)
          (show d + μ ≤ (d + 2 * ε + μ) - ε - ε by linarith) rfl
      obtain ⟨e, he⟩ : ∃ e : ℝ, birthSup hLawY ((d + 2 * ε + μ) - ε)
          (structMap hLawY hwε (φ β hβαβ A)) = e := ⟨_, rfl⟩
      rw [he] at hband_lo hband_hi
      have heα : α < e := by linarith
      have hwtop : (d + 2 * ε + μ) - ε < e := by linarith
      -- (S7) the dichotomy on the probe cell at window-bottom d+ε−1 (the
      --   Hi template's α−1 window mirrored; the absorb's length-1 side
      --   condition holds since w*−(d+ε−1) = μ+1 ≥ 1).
      rcases t5_l3_dichotomy hLawY hTameY (structMap hLawY hwε (φ β hβαβ A)) he
          (show d + ε - 1 ≤ (d + 2 * ε + μ) - ε by linarith) with
        hfull | hout
      · -- the full window [d+ε−1, w*]: the thread either breaks strictly
        -- below the window bottom (the hoff re-run) or never breaks at
        -- all (the essential bar (e, ⊥)).
        by_cases hoff : ∃ (w : ℝ) (hw : w ≤ (d + 2 * ε + μ) - ε),
            w ≤ d + ε - 1 ∧
            birthSup hLawY w (structMap hLawY hw
              (structMap hLawY hwε (φ β hβαβ A))) ≠ e
        · obtain ⟨w, hw, hwle, hwne⟩ := hoff
          rcases t5_l3_dichotomy hLawY hTameY (structMap hLawY hwε (φ β hβαβ A)) he
              (show w - 1 ≤ (d + 2 * ε + μ) - ε by linarith) with
            hfull₂ | hout₂
          · exact absurd (hfull₂ w hw (show w - 1 ≤ w by linarith)) hwne
          · obtain ⟨v, hvlo, hvhi, hAbove, hBelow, hbot⟩ := hout₂
            obtain ⟨hcloseE, hmult⟩ :=
              t5_partnerAbsorbGen hLawY hTameY hband_lo hband_hi hwtop
                (show 1 ≤ (d + 2 * ε + μ) - ε - (w - 1) by linarith)
                hvlo hvhi hAbove hBelow hbot he
            have hvle : v ≤ d + ε := by
              by_contra hcon
              push_neg at hcon
              have hvnc : v ∉ critSet hTameY := by
                intro hvC
                have hg := hgapY.2 v hvC (show v ≠ d + ε by linarith)
                rw [abs_of_nonneg (show 0 ≤ v - (d + ε) by linarith)] at hg
                linarith
              exact absurd (t3_death_pin hLawY hTameY
                (show v < e by linarith) hvnc) hmult
            rcases lt_or_ge α v with hvalt | hval
            · exact ⟨e, (v : EReal), EReal.coe_lt_coe_iff.mpr heα,
                Or.inr ⟨EReal.coe_lt_coe_iff.mpr hvalt,
                  ⟨by rw [← EReal.coe_add]; exact EReal.coe_le_coe_iff.mpr (by linarith),
                   by rw [← EReal.coe_add]; exact EReal.coe_le_coe_iff.mpr (by linarith)⟩⟩,
                hcloseE, hmult⟩
            · exact ⟨e, (v : EReal), EReal.coe_lt_coe_iff.mpr heα,
                Or.inl (EReal.coe_le_coe_iff.mpr hval), hcloseE, hmult⟩
        · -- never breaks below the window: the full ray — the essential
          -- bar (e, ⊥), with ⊥ ≤ α the goal's first disjunct.
          have hevery : ∀ (w : ℝ) (hw : w ≤ (d + 2 * ε + μ) - ε),
              birthSup hLawY w (structMap hLawY hw
                (structMap hLawY hwε (φ β hβαβ A))) = e := by
            intro w hw
            by_cases hw1 : d + ε - 1 ≤ w
            · exact hfull w hw hw1
            · by_contra hne
              exact hoff ⟨w, hw, (show w ≤ d + ε - 1 by linarith), hne⟩
          exact ⟨e, ⊥, EReal.coe_lt_coe_iff.mpr heα, Or.inl bot_le,
            ⟨by rw [← EReal.coe_add]; exact EReal.coe_le_coe_iff.mpr (by linarith),
             by rw [← EReal.coe_add]; exact EReal.coe_le_coe_iff.mpr hband_hi⟩,
            t3_essential_mult hLawY hTameY (structMap hLawY hwε (φ β hβαβ A)) he
              hevery⟩
      · -- a break inside the probe window: the absorb at (e, v), then the
        -- death control — a shallow break v ∈ (d+ε, w*] is Y-uncritical
        -- (the δ₁-gap, μ < δ₁) so t3_death_pin would force mult (e, v) = 0,
        -- contradicting the absorb; hence v ≤ d+ε, and the goal's death
        -- disjunct holds (m ≤ α, or α < m ≤ d+ε with closeE d m ε
        -- automatic in the low band d ≤ α).
        obtain ⟨v, hvlo, hvhi, hAbove, hBelow, hbot⟩ := hout
        obtain ⟨hcloseE, hmult⟩ :=
          t5_partnerAbsorbGen hLawY hTameY hband_lo hband_hi hwtop
            (show 1 ≤ (d + 2 * ε + μ) - ε - (d + ε - 1) by linarith)
            hvlo hvhi hAbove hBelow hbot he
        have hvle : v ≤ d + ε := by
          by_contra hcon
          push_neg at hcon
          have hvnc : v ∉ critSet hTameY := by
            intro hvC
            have hg := hgapY.2 v hvC (show v ≠ d + ε by linarith)
            rw [abs_of_nonneg (show 0 ≤ v - (d + ε) by linarith)] at hg
            linarith
          exact absurd (t3_death_pin hLawY hTameY
            (show v < e by linarith) hvnc) hmult
        rcases lt_or_ge α v with hvalt | hval
        · exact ⟨e, (v : EReal), EReal.coe_lt_coe_iff.mpr heα,
            Or.inr ⟨EReal.coe_lt_coe_iff.mpr hvalt,
              ⟨by rw [← EReal.coe_add]; exact EReal.coe_le_coe_iff.mpr (by linarith),
               by rw [← EReal.coe_add]; exact EReal.coe_le_coe_iff.mpr (by linarith)⟩⟩,
            hcloseE, hmult⟩
        · exact ⟨e, (v : EReal), EReal.coe_lt_coe_iff.mpr heα,
            Or.inl (EReal.coe_le_coe_iff.mpr hval), hcloseE, hmult⟩
    exact hTrackDeath
    -- (P4)–(P6) dichotomy/absorb tail RETIRED with hP3b (all its finishes
    -- consumed the refuted upper band); see the hTrackDeath record above.
  -- PLAN (route B, low band d ∈ [α−ε, α]):
  -- (P1) HIGH TRANSPORT CENSUS PIN. `t3_stable_delta` gives gaps δ₀ around (d,b);
  --   take η with 0 < η < δ₀, η < (b−d)/2 AND η < b − d − ε (the last uses
  --   α+ε < b, d ≤ α). Census C₀ at level d+η with value b via `t5_census_cell`.
  --   NOTE: no η < α−ε−d is required — that is the break in the Hi template.
  -- (P2) ALIVE-UP PAST THE BAND TOP. `t5_aliveUp` lifts C₀ to A₁ at level
  --   β := b − ε (d+η ≤ b−ε by η < b−d−ε; b−ε < b), birthSup = b, descending to C₀.
  -- (P3) IMAGE CELL + LOWER BAND. `t5_imageBirthStrongLower` (hSq1 only, no floor
  --   hypotheses): J' := φ_{b−ε} A₁ lives at level b−2ε with birthSup e ≥ b−ε > α
  --   (α+ε < b). So e > α unconditionally. Upper band e ≤ b+ε: try
  --   `t5_elderTrap` at a HIGH transport level (hyps: d+2ε < β, v ∈ (d+ε, β−ε]) or
  --   `t5_imageThread_band`; fallback: state variant with e ≤ b+ε as an extra
  --   hypothesis documented as call-site-derivable.
  -- (P4) DICHOTOMY WINDOW. `t5_l3_dichotomy` on J'’s value-ray with window
  --   [α−1, b−2ε] (need α−1 ≤ b−2ε: from α+ε < b, i.e. α ≤ b−ε... CHECK).
  -- (P5) RIGHT BRANCH (ray breaks at v ∈ (α−1, b−2ε], value drops below v):
  --   feed `t5_partnerAbsorb` (J sits at level b−2ε; window-top v) or finish on
  --   the Y-module with `t5_census_absorb`/`t5_census_back` at (e, v); death bound
  --   m ≤ α from the dichotomy's v ≤ window-bottom+ε bookkeeping (v ≤ α−1+ε ≤ α).
  -- (P6) LEFT BRANCH (full ray value-e down to α−1): thread alive at level α
  --   (α ≤ b−2ε) with value e. hSq2-then-hSq4: ψ_α(descendant of J' from level α)
  --   = structMap of A₁ at level b−2ε... CHECK exact composition; aim: an X-cell
  --   alive at level α−ε ≤ d with birthSup ≥ b−ε while the X b-band census DROPPED
  --   at death d (t3_comb_small / hpx / window_ineq_X) — chase contradiction —
  --   OR conclude the essential partner bar (e, ⊥) via `t3_essential_mult`
  --   (mirror of the template's residual branch).
  -- GREEN TOOLS: t3_stable_delta, t5_census_cell, t5_aliveUp, t5_imageBirthStrongLower,
  --   t5_imageBirthUpper, t5_hDescPin (maybe unusable), t5_l3_dichotomy,
  --   t5_partnerAbsorb, t3_essential_mult, t5_elderTrap, t5_imageThread_band,
  --   t5_census_absorb, t5_census_back, window_ineq_X, t3_comb_small.
