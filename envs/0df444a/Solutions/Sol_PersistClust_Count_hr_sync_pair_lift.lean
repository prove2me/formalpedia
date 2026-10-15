-- Prove2me | solution 1 for PersistClust.Count.hr_sync_pair_lift
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-14T15:16:45.857348+00:00
-- url     : https://prove2.me/submissions/fad8a568-84ff-4f70-aaea-1ff119acbced

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

theorem t3_mult_unfold {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) {b d : ℝ} (hbd : d < b) :
    mult (rankFn stage J) ((b : EReal), (d : EReal)) =
      ⨅ (η : ℝ) (_ : η ∈ Set.Ioo (0 : ℝ) ((b - d) / 2)), t3_comb stage J b d η := by
  unfold mult t3_comb
  rw [if_pos ⟨EReal.coe_ne_bot b, EReal.coe_ne_top b⟩,
      if_neg (EReal.coe_ne_bot d), if_pos (EReal.coe_lt_coe_iff.mpr hbd)]
  simp only [EReal.toReal_coe]

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

/-- hr1 — CARRIER ELDER (the census-surplus pigeonhole, the ONLY new content of the sync
route; 2026-10-12).  Given a bar `(b, d)` of the X-module with `mult (b, d) ≠ 0` and the
critSet gaps `δx` at `b` and `d` (witnessed by `hgap`), and a pin offset `0 < η₀ < δx`
below half the bar width: the b-band cells at the pin `d + η₀` OUTNUMBER the b-band cells
below (`t3_comb_small` surplus, since `mult ≠ 0` forces `comb ≠ 0`), so the surplus is
accounted for by a CO-MERGE of two DISTINCT pin cells at the below level `d − η₀` — the
census-surplus pigeonhole.

WORKING FORM (carrierE2 fill, 2026-10-12; RECORDED PRECISELY — the skeleton's at-d form
with BOTH cells b-band is UNPROVABLE, see the change note): there are DISTINCT cells
`C₁`, `C₂` at the pin `d + η₀`, `C₁` b-band (`birthSup = b`), `C₂` with `b ≤ birthSup`
(the ELDER: b-band in the merge branch, strictly off-band in the absorb branch), whose
`d − η₀`-descents COINCIDE.  The sync-pair wiring consumes this directly:
`t5_hr_syncCoMerge` at `δ := d − η₀` gives image threads one class by `d − η₀ − ε` (the
wiring accepts arbitrary merge levels), and the `t5_syncHigh` distinctness above `d + ε`
is read off the pin-level sources (crit-free on `(d, d + η₀]` once β is off-critSet).

CHANGE NOTE (why the at-d merge-pair is NOT provable from these hypotheses): the surplus
`pin > below` can be realized entirely by ABSORPTION — a single b-band pin cell whose
below-descent is off-band (`birthSup > b` by `rungB_bSup_descend_ge`), with the b-band
pin census of size exactly ONE; this is the shape `t5_census_absorb`'s own hypothesis
`hthr` describes (GREEN), so a second b-band pin cell need not exist at all.  The honest
dichotomy, proved below (both branches deliver the working form):
  * MERGE (every b-band pin cell descends b-band below): the below-descent map
    pin census → below census is non-injective by the surplus (`Set.encard_le_encard_of_injOn`
    contrapositive — `t5_census_absorb`'s lift/inject idiom L2951–L2967 run in reverse):
    two DISTINCT b-band pin cells with EQUAL `d − η₀`-descents;
  * ABSORB (some b-band pin cell `C` descends off-band below): the below-cell's ancestor
    ray (`AncSet`, sup `> b`) furnishes an ancestor `D` at a level `u₀ > b`; its
    `d + η₀`-descent is an ELDER `≠ C` with `u₀ ≤ birthSup`, co-merging with `C` at
    `d − η₀`.  (Equal `d`-descents do NOT follow even here: `d ∈ critSet` blocks
    `t3_crit_inj` on `[d − η₀, d]`, and `structMap_comp` only factors the common descent
    through `d − η₀`; the at-d lift was the predecessor's step 5 and is dropped.) -/
theorem t5_hr_carrierElder {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {b d δx η₀ : ℝ} (hbd : d < b)
    (hgap : (∀ τ ∈ critSet hTame, τ ≠ b → δx < |τ - b|) ∧
      (∀ τ ∈ critSet hTame, τ ≠ d → δx < |τ - d|))
    (hη₀ : η₀ ∈ Set.Ioo (0 : ℝ) δx) (hη₀bd : η₀ < (b - d) / 2)
    (hmult : mult (rankFn stage J) ((b : EReal), (d : EReal)) ≠ 0) :
    ∃ C₁ C₂ : comps stage J (d + η₀),
      birthSup hLaw (d + η₀) C₁ = b ∧ b ≤ birthSup hLaw (d + η₀) C₂ ∧ C₁ ≠ C₂ ∧
      structMap hLaw (show d - η₀ ≤ d + η₀ by linarith [hη₀.1]) C₁
        = structMap hLaw (show d - η₀ ≤ d + η₀ by linarith [hη₀.1]) C₂ := by
  -- hpos (route step 1) + positivity (step 2), the `hdrop` idiom of `t5_deathBar`
  -- (L3713–L3719): `mult ≠ 0` forces `1 ≤ comb` at the pin, hence `comb ≠ 0`/`0 < comb`.
  have h1 : 1 ≤ mult (rankFn stage J) ((b : EReal), (d : EReal)) :=
    Order.one_le_iff_ne_zero.mpr hmult
  rw [t3_mult_unfold hLaw hbd] at h1
  have h2 : 1 ≤ t3_comb stage J b d η₀ := h1.trans (iInf₂_le η₀ ⟨hη₀.1, hη₀bd⟩)
  rw [t3_comb_small hLaw hTame hbd hgap hη₀ hη₀bd] at h2
  -- hpinsurplus (route step 3): b-band census at the pin strictly exceeds the one below
  -- (truncated ℕ∞ subtraction: `pin ≤ below` would force `pin − below = 0`).
  have hs : ({C : comps stage J (d - η₀) | birthSup hLaw (d - η₀) C = b} :
      Set (comps stage J (d - η₀))).encard <
      ({C : comps stage J (d + η₀) | birthSup hLaw (d + η₀) C = b} :
        Set (comps stage J (d + η₀))).encard :=
    tsub_pos_iff_lt.mp (zero_lt_one.trans_le h2)
  have hF : d - η₀ ≤ d + η₀ := by linarith [hη₀.1]
  -- hpigeonhole + hlift (route steps 4–5), via the honest MERGE/ABSORB dichotomy on the
  -- below-descents of the b-band pin census (see the change note above):
  by_cases hcase : ∀ C ∈ ({C : comps stage J (d + η₀) | birthSup hLaw (d + η₀) C = b} :
      Set (comps stage J (d + η₀))),
      birthSup hLaw (d - η₀) (structMap hLaw hF C) = b
  · -- MERGE branch: all below-descents land in the below census; the surplus makes the
    -- descent map non-injective (`Set.encard_le_encard_of_injOn` contrapositive).
    by_contra hno
    have hinj : ∀ C₁ ∈ ({C : comps stage J (d + η₀) | birthSup hLaw (d + η₀) C = b} :
        Set (comps stage J (d + η₀))), ∀ C₂ ∈ ({C : comps stage J (d + η₀) |
          birthSup hLaw (d + η₀) C = b} : Set (comps stage J (d + η₀))),
        structMap hLaw hF C₁ = structMap hLaw hF C₂ → C₁ = C₂ := by
      intro C₁ h₁ C₂ h₂ heq
      by_cases hne : C₁ = C₂
      · exact hne
      · have hC₂b : birthSup hLaw (d + η₀) C₂ = b := h₂
        exact absurd ⟨C₁, C₂, h₁, hC₂b.symm.le, hne, heq⟩ hno
    have hle : ({C : comps stage J (d + η₀) | birthSup hLaw (d + η₀) C = b} :
        Set (comps stage J (d + η₀))).encard ≤
        ({C : comps stage J (d - η₀) | birthSup hLaw (d - η₀) C = b} :
          Set (comps stage J (d - η₀))).encard :=
      Set.encard_le_encard_of_injOn (f := fun C : comps stage J (d + η₀) =>
        structMap hLaw hF C) (fun C hC => hcase C hC) hinj
    exact absurd hle (not_le.2 hs)
  · -- ABSORB branch: some b-band pin cell descends off-band below (bSup > b by
    -- monotonicity); its below-cell's ancestor ray furnishes the elder.
    push_neg at hcase
    obtain ⟨C, hCmem, hCoff⟩ := hcase
    have hCb : birthSup hLaw (d + η₀) C = b := hCmem
    have hCge : birthSup hLaw (d + η₀) C ≤
        birthSup hLaw (d - η₀) (structMap hLaw hF C) :=
      rungB_bSup_descend_ge hLaw hTame hF C
    rw [hCb] at hCge
    have hgt : b < birthSup hLaw (d - η₀) (structMap hLaw hF C) := by
      by_contra hcon
      push_neg at hcon
      exact hCoff (le_antisymm hcon hCge)
    have hne : (AncSet hLaw (d - η₀) (structMap hLaw hF C)).Nonempty :=
      ⟨d - η₀, le_rfl, structMap hLaw hF C,
        t3_structMap_id hLaw (d - η₀) (structMap hLaw hF C)⟩
    obtain ⟨u₀, hu₀, hu₀b⟩ :
        ∃ u₀, u₀ ∈ AncSet hLaw (d - η₀) (structMap hLaw hF C) ∧ b < u₀ := by
      by_contra hcon
      push_neg at hcon
      have hle : sSup (AncSet hLaw (d - η₀) (structMap hLaw hF C)) ≤ b :=
        csSup_le hne hcon
      rw [(show birthSup hLaw (d - η₀) (structMap hLaw hF C)
          = sSup (AncSet hLaw (d - η₀) (structMap hLaw hF C)) from rfl)] at hgt
      exact absurd hle (not_le.2 hgt)
    obtain ⟨hdu, D, hD⟩ := hu₀
    have hleu : d + η₀ ≤ u₀ := by linarith
    -- the elder: the `d + η₀`-descent of the above-`b` ancestor `D`, co-merging with `C`
    have hEeq : structMap hLaw hF (structMap hLaw hleu D) = structMap hLaw hF C :=
      (structMap_comp hLaw hF hleu D).trans hD
    have hEne : structMap hLaw hleu D ≠ C := by
      intro heq
      obtain ⟨s₀, hs₀⟩ := hTame.2.2
      have hBdd : BddAbove (AncSet hLaw (d + η₀) C) := by
        refine ⟨s₀, fun u hu => ?_⟩
        obtain ⟨-, D', -⟩ := hu
        have hstage : (stage u).Nonempty := by
          obtain ⟨x, hx, -⟩ := D'.property
          exact ⟨x, hx⟩
        by_contra hle
        push_neg at hle
        exact hstage.ne_empty (hs₀ u hle.le)
      have hmem : u₀ ∈ AncSet hLaw (d + η₀) C := ⟨hleu, D, heq⟩
      have hle2 : u₀ ≤ sSup (AncSet hLaw (d + η₀) C) := le_csSup hBdd hmem
      rw [(show birthSup hLaw (d + η₀) C
          = sSup (AncSet hLaw (d + η₀) C) from rfl)] at hCb
      exact absurd (hle2.trans hCb.le) (not_le.2 hu₀b)
    have hEge : u₀ ≤ birthSup hLaw (d + η₀) (structMap hLaw hleu D) :=
      (rungB_level_le_bSup hLaw hTame D).trans
        (rungB_bSup_descend_ge hLaw hTame hleu D)
    exact ⟨C, structMap hLaw hleu D, hCb, hu₀b.le.trans hEge, hEne.symm, hEeq.symm⟩

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




theorem t5_hr_syncCoMerge {ιX ιY : Type*}
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


theorem t5_syncHigh {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    {α ε : ℝ} (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq4 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (x : comps stageX JX β),
      ψ (β - ε) hβε (φ β hβ x) =
        structMap hLawX (show (β - ε) - ε ≤ β by linarith) x)
    {u : ℝ} (hαu : α ≤ u) (hβε : α ≤ u - ε) (hle : u - ε - ε ≤ u)
    (C₁ C₂ : comps stageX JX u)
    (hne : structMap hLawX hle C₁ ≠ structMap hLawX hle C₂) :
    φ u hαu C₁ ≠ φ u hαu C₂ := by
  intro heq
  apply hne
  have h₁ := hSq4 u hαu hβε C₁
  have h₂ := hSq4 u hαu hβε C₂
  calc structMap hLawX hle C₁
      = ψ (u - ε) hβε (φ u hαu C₁) := h₁.symm
    _ = ψ (u - ε) hβε (φ u hαu C₂) := by rw [heq]
    _ = structMap hLawX hle C₂ := h₂


/-- hr1 SATELLITE (carrierE2 fill, 2026-10-12): the per-copy SYNC-PAIR CORE of hr-route
step (3), packaged GREEN from `t5_hr_carrierElder` (above) + the green lift/birth/sync
machinery.  For a bar `(b, d)` of X with the critSet gaps `δx` at `b`, `d` and a pin `η₀`
below the gap, the half-width, the bar-separation slack (`η₀ < b − d − 2ε`, so the probe
`β := d + η₀ + 2ε` stays below `b`) and the α-slack (`η₀ < d − α`, so `α ≤ d − η₀`), it
delivers at the canonical probe `β`:
  * the carrier/elder pair `C₁`, `C₂` of `t5_hr_carrierElder` (b-band resp. elder-band,
    co-merging at `d − η₀`);
  * their alive-up lifts `A₁`, `A₂` at `β` (bSup-preserving: `b` resp. the elder value);
  * the carrier image `I₁ = φ_β A₁` with `birthSup_Y ∈ [b − ε, b + ε]` — the `b₂` of the
    value cases (`t5_deathBar`'s rung-B sandwich, L3675–L3696, mirrored);
  * DISTINCT image cells `I₁ ≠ I₂` (`t5_syncHigh`; the source distinctness at `β − 2ε` is
    FREE from `C₁ ≠ C₂` via `structMap_comp` — NO `t3_crit_inj` window needed);
  * the image CO-MERGE by `d − η₀ − ε` (`t5_hr_syncCoMerge` at `δ := d − η₀`; the wiring
    accepts the merge level `d − η₀` in place of `d`, per the carrierElder change note).
REMAINING RESIDUE for hr-route step (3) (the next lane, per the step-3 seal): the
merge-level extraction `m′` from the pair (distinct at `β − ε`, co-merged at
`d − η₀ − ε`; `t5_l3_dichotomy`-style up-set boundary), the three value cases at
`(b₂, m′)` (`t5_census_absorb` / direct comb / `t5_census_back`), and the canonical
`P a := ((b₂ : EReal), (m′ : EReal))`; then step (4)'s canonicity chains. -/
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
    {b d δx η₀ : ℝ} (hbd : d < b) (hαd : α < d)
    (hgap : (∀ τ ∈ critSet hTameX, τ ≠ b → δx < |τ - b|) ∧
      (∀ τ ∈ critSet hTameX, τ ≠ d → δx < |τ - d|))
    (hη₀0 : 0 < η₀) (hη₀δ : η₀ < δx) (hη₀bd : η₀ < (b - d) / 2)
    (hη₀sep : η₀ < b - d - 2 * ε) (hη₀α : η₀ < d - α)
    (hmult : mult (rankFn stageX JX) ((b : EReal), (d : EReal)) ≠ 0) :
    ∃ (C₁ C₂ : comps stageX JX (d + η₀)) (A₁ A₂ : comps stageX JX (d + η₀ + 2 * ε)),
      birthSup hLawX (d + η₀) C₁ = b ∧
      b ≤ birthSup hLawX (d + η₀) C₂ ∧ C₁ ≠ C₂ ∧
      structMap hLawX (show d - η₀ ≤ d + η₀ by linarith) C₁
        = structMap hLawX (show d - η₀ ≤ d + η₀ by linarith) C₂ ∧
      birthSup hLawX (d + η₀ + 2 * ε) A₁ = b ∧
      birthSup hLawX (d + η₀ + 2 * ε) A₂ = birthSup hLawX (d + η₀) C₂ ∧
      structMap hLawX (show d + η₀ ≤ d + η₀ + 2 * ε by linarith) A₁ = C₁ ∧
      structMap hLawX (show d + η₀ ≤ d + η₀ + 2 * ε by linarith) A₂ = C₂ ∧
      b - ε ≤ birthSup hLawY ((d + η₀ + 2 * ε) - ε)
          (φ (d + η₀ + 2 * ε) (show α ≤ d + η₀ + 2 * ε by linarith) A₁) ∧
      birthSup hLawY ((d + η₀ + 2 * ε) - ε)
          (φ (d + η₀ + 2 * ε) (show α ≤ d + η₀ + 2 * ε by linarith) A₁) ≤ b + ε ∧
      φ (d + η₀ + 2 * ε) (show α ≤ d + η₀ + 2 * ε by linarith) A₁
        ≠ φ (d + η₀ + 2 * ε) (show α ≤ d + η₀ + 2 * ε by linarith) A₂ ∧
      structMap hLawY (show (d - η₀) - ε ≤ (d + η₀ + 2 * ε) - ε by linarith)
          (φ (d + η₀ + 2 * ε) (show α ≤ d + η₀ + 2 * ε by linarith) A₁)
        = structMap hLawY (show (d - η₀) - ε ≤ (d + η₀ + 2 * ε) - ε by linarith)
          (φ (d + η₀ + 2 * ε) (show α ≤ d + η₀ + 2 * ε by linarith) A₂) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hne, hdesc⟩ :=
    t5_hr_carrierElder hLawX hTameX hbd hgap ⟨hη₀0, hη₀δ⟩ hη₀bd hmult
  have hβlt : d + η₀ + 2 * ε < b := by linarith
  have hαβ : α ≤ d + η₀ + 2 * ε := by linarith
  have hαβε : α ≤ (d + η₀ + 2 * ε) - ε := by linarith
  have hs : d + η₀ ≤ d + η₀ + 2 * ε := by linarith
  have hβe : d + η₀ + 2 * ε < birthSup hLawX (d + η₀) C₂ := by linarith
  obtain ⟨A₁, hA₁b, hA₁d⟩ := t5_aliveUp hLawX hTameX hC₁ hs hβlt
  obtain ⟨A₂, hA₂b, hA₂d⟩ :=
    t5_aliveUp hLawX hTameX (rfl : birthSup hLawX (d + η₀) C₂
      = birthSup hLawX (d + η₀) C₂) hs hβe
  -- carrier image birth ∈ [b − ε, b + ε] (the `t5_deathBar` sandwich, L3675–L3696)
  have hL : (d + η₀ + 2 * ε) - ε - ε ≤ d + η₀ + 2 * ε := by linarith
  have hd1 : d + η₀ ≤ (d + η₀ + 2 * ε) - ε - ε := by linarith
  have hlo : b ≤ birthSup hLawX ((d + η₀ + 2 * ε) - ε - ε)
      (structMap hLawX hL A₁) := by
    have hr := rungB_bSup_descend_ge hLawX hTameX hL A₁
    linarith
  have hhi : birthSup hLawX ((d + η₀ + 2 * ε) - ε - ε)
      (structMap hLawX hL A₁) ≤ b := by
    have hr2 := rungB_bSup_descend_ge hLawX hTameX hd1 (structMap hLawX hL A₁)
    have hcomp : structMap hLawX hd1 (structMap hLawX hL A₁) = C₁ := by
      rw [structMap_comp hLawX hd1 hL A₁]
      exact hA₁d
    rw [hcomp, hC₁] at hr2
    exact hr2
  have hdescβ : birthSup hLawX ((d + η₀ + 2 * ε) - ε - ε)
      (structMap hLawX (show (d + η₀ + 2 * ε) - ε - ε ≤ d + η₀ + 2 * ε by linarith) A₁) = b :=
    le_antisymm hhi hlo
  have hIhi : birthSup hLawY ((d + η₀ + 2 * ε) - ε)
      (φ (d + η₀ + 2 * ε) hαβ A₁) ≤ b + ε :=
    t5_imageBirthUpper hLawX hLawY hTameX hε φ ψ hSq2 hSq4 hαβ hαβε A₁ hdescβ
  have hIlo : b - ε ≤ birthSup hLawY ((d + η₀ + 2 * ε) - ε)
      (φ (d + η₀ + 2 * ε) hαβ A₁) := by
    have hr := t5_imageBirthStrongLower hLawX hLawY hTameY φ hSq1 hαβ A₁
    linarith
  -- distinct image cells: the 2ε-descent distinctness is FREE from `C₁ ≠ C₂`
  have hne2ε : structMap hLawX hL A₁ ≠ structMap hLawX hL A₂ := by
    intro heq
    have hc₁ : structMap hLawX hd1 (structMap hLawX hL A₁) = C₁ := by
      rw [structMap_comp hLawX hd1 hL A₁]
      exact hA₁d
    have hc₂ : structMap hLawX hd1 (structMap hLawX hL A₂) = C₂ := by
      rw [structMap_comp hLawX hd1 hL A₂]
      exact hA₂d
    rw [heq] at hc₁
    exact hne (hc₁.symm.trans hc₂)
  have hIeq : φ (d + η₀ + 2 * ε) hαβ A₁ ≠ φ (d + η₀ + 2 * ε) hαβ A₂ :=
    t5_syncHigh hLawX hLawY hε φ ψ hSq4 hαβ hαβε hL A₁ A₂ hne2ε
  -- image co-merge by `d − η₀ − ε` (`t5_hr_syncCoMerge` at `δ := d − η₀`)
  have hαδ : α ≤ d - η₀ := by linarith
  have hF' : d - η₀ ≤ d + η₀ := by linarith
  have hdA₁ : structMap hLawX (le_trans hF' hs) A₁ = structMap hLawX hF' C₁ := by
    rw [← structMap_comp hLawX hF' hs A₁, hA₁d]
  have hdA₂ : structMap hLawX (le_trans hF' hs) A₂ = structMap hLawX hF' C₂ := by
    rw [← structMap_comp hLawX hF' hs A₂, hA₂d]
  obtain ⟨hm1, hm2⟩ := t5_hr_syncCoMerge hLawX hLawY φ hSq1 hαδ hαβ (le_trans hF' hs)
    A₁ A₂ (structMap hLawX hF' C₁) hdA₁ (hdA₂.trans hdesc.symm)
  exact ⟨C₁, C₂, A₁, A₂, hC₁, hC₂, hne, hdesc, hA₁b, hA₂b, hA₁d, hA₂d,
    hIlo, hIhi, hIeq, hm1.trans hm2.symm⟩
