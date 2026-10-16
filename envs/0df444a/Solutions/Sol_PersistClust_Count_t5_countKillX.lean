-- Prove2me | solution 1 for PersistClust.Count.t5_countKillX
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-15T12:39:15.976973+00:00
-- url     : https://prove2.me/submissions/32358d45-b1dd-4e98-a7f8-e6989f40b4ee

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus
import Definitions.Def_PersistClust_Count_MatchingGate

open PersistClust.Count
open scoped ENNReal

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

/-- Count-gap lemma, psi-side dual (the sides-swapped count-gap):
if every X-cell at the pullback level beta - eps is born
above s, no Y-cell at level beta is born exactly at
s - eps, and the Y-cells at level beta born above
s - eps inject under psi into the X-cells at level
beta - eps with one outliver removed, then the Y-window
rank at (s - eps, beta) is STRICTLY below the X-window rank
at (s, beta - eps). Supplies the essential-top kill of the
rank calculus: a strictly smaller counted side against a
counted-else injection with an outliver. -/
theorem solution {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop} {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
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
    (hSq3 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (y : comps stageY JY β),
      φ (β - ε) hβε (ψ β hβ y) =
        structMap hLawY (show (β - ε) - ε ≤ β by linarith) y)
    (hSq4 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (x : comps stageX JX β),
      ψ (β - ε) hβε (φ β hβ x) =
        structMap hLawX (show (β - ε) - ε ≤ β by linarith) x)
    {s β : ℝ} (hβα : α ≤ β) (hwin : β - ε + 2 * ε ≤ s)
    (hcountX : ∀ C : comps stageX JX (β - ε), s < birthSup hLawX (β - ε) C)
    (hgenY : ∀ D : comps stageY JY β, s - ε ≠ birthSup hLawY β D)
    (hO : ∃ O : comps stageX JX (β - ε), ∀ D : comps stageY JY β,
        s - ε < birthSup hLawY β D → ψ β hβα D ≠ O)
    (hinj : ∀ D₁ D₂ : comps stageY JY β, s - ε < birthSup hLawY β D₁ →
        s - ε < birthSup hLawY β D₂ → ψ β hβα D₁ = ψ β hβα D₂ → D₁ = D₂) :
    rankFn stageY JY (s - ε) β < rankFn stageX JX s (β - ε) := by
  -- X side: every X-cell counts (hcountX), so the X-rank is the full census at level β−ε.
  have hstX : β - ε ≤ s := by linarith
  have hsX : ∀ C : comps stageX JX (β - ε), s ≠ birthSup hLawX (β - ε) C := by
    intro C hC
    exact absurd (hC ▸ hcountX C) (lt_irrefl s)
  have hRX : rankFn stageX JX s (β - ε) =
      {C : comps stageX JX (β - ε) | s < birthSup hLawX (β - ε) C}.encard :=
    t3_rank_orig hLawX hTameX hstX hsX
  have huniv : {C : comps stageX JX (β - ε) | s < birthSup hLawX (β - ε) C}
      = (Set.univ : Set (comps stageX JX (β - ε))) := by
    ext C
    simp only [Set.mem_ofPred_eq, Set.mem_univ]
    exact ⟨fun _ => trivial, fun _ => hcountX C⟩
  have hRX' : rankFn stageX JX s (β - ε)
      = (Set.univ : Set (comps stageX JX (β - ε))).encard := by
    rw [hRX, huniv]
  -- Y side: the rank counts the Y-cells alive past s−ε.
  have hstY : β ≤ s - ε := by linarith
  have hRY : rankFn stageY JY (s - ε) β =
      {D : comps stageY JY β | s - ε < birthSup hLawY β D}.encard :=
    t3_rank_orig hLawY hTameY hstY hgenY
  obtain ⟨O, hO⟩ := hO
  -- the counted Y-cells map into `univ \ {O}` and the map is injective there
  have hle : {D : comps stageY JY β | s - ε < birthSup hLawY β D}.encard ≤
      (Set.univ \ {O} : Set (comps stageX JX (β - ε))).encard := by
    refine Set.encard_le_encard_of_injOn (f := fun D => ψ β hβα D) (fun D hD => ?_)
      (fun D₁ hD₁ D₂ hD₂ heq => ?_)
    · exact ⟨Set.mem_univ _, fun hmem => hO D hD (Set.mem_singleton_iff.mp hmem)⟩
    · exact hinj D₁ D₂ hD₁ hD₂ heq
  -- strictness: the full census exceeds the census minus the outliver
  haveI hfinX : Finite (comps stageX JX (β - ε)) := (hTameX.1 (β - ε)).to_subtype
  have hfin : (Set.univ \ {O} : Set (comps stageX JX (β - ε))).Finite :=
    Set.finite_univ.sdiff
  have hsub : (Set.univ \ {O} : Set (comps stageX JX (β - ε)))
      ⊂ (Set.univ : Set (comps stageX JX (β - ε))) :=
    Set.ssubset_univ_iff.mpr (by
      intro h
      have hu : O ∈ (Set.univ : Set (comps stageX JX (β - ε))) := Set.mem_univ _
      rw [← h] at hu
      exact hu.2 (Set.mem_singleton_iff.mpr rfl))
  have hlt := hfin.encard_lt_encard hsub
  calc rankFn stageY JY (s - ε) β
      = {D : comps stageY JY β | s - ε < birthSup hLawY β D}.encard := hRY
    _ ≤ (Set.univ \ {O} : Set (comps stageX JX (β - ε))).encard := hle
    _ < (Set.univ : Set (comps stageX JX (β - ε))).encard := hlt
    _ = rankFn stageX JX s (β - ε) := hRX'.symm
