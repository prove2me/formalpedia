-- Prove2me | solution 1 for PersistClust.Count.t5_deathKill
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-15T12:41:30.646329+00:00
-- url     : https://prove2.me/submissions/097f2498-3e5d-4b81-80f2-ec1fda3c957e

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

theorem rankFn_eq_structImage {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) {s t : ℝ} (hst : t ≤ s) :
    rankFn stage J s t =
      (Set.univ.image (fun C : comps stage J s => (structMap hLaw hst C).val)).encard := by
  unfold rankFn
  congr 1
  ext S
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hprop : {y | J s x y} ∈ (fun x => {y | J s x y}) '' stage s := ⟨x, hx, rfl⟩
    refine ⟨⟨{y | J s x y}, hprop⟩, trivial, ?_⟩
    simp only [structMap_val]
    have hrep : J s (compRep stage J s ⟨{y | J s x y}, hprop⟩) x := by
      have h2 : (fun x => {y | J s x y}) (compRep stage J s ⟨{y | J s x y}, hprop⟩) =
          {y | J s x y} := (compRep_spec stage J s ⟨{y | J s x y}, hprop⟩).2
      have h3 : x ∈ (fun x => {y | J s x y}) (compRep stage J s ⟨{y | J s x y}, hprop⟩) := by
        rw [h2]; exact hLaw.refl hx
      exact h3
    ext y
    constructor
    · intro hy
      exact hLaw.trans (hLaw.symm (hLaw.compat hst hrep)) hy
    · intro hy
      exact hLaw.trans (hLaw.compat hst hrep) hy
  · rintro ⟨C, -, rfl⟩
    exact ⟨compRep stage J s C, (compRep_spec stage J s C).1, (structMap_val hLaw hst C).symm⟩

theorem rankFn_eq_structImage' {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) {s t : ℝ} (hst : t ≤ s) :
    rankFn stage J s t =
      (Set.univ.image (fun C : comps stage J s => structMap hLaw hst C)).encard := by
  rw [rankFn_eq_structImage hLaw hst]
  rw [show (Set.univ.image (fun C : comps stage J s => (structMap hLaw hst C).val))
        = Subtype.val '' (Set.univ.image (fun C : comps stage J s => structMap hLaw hst C)) from by
      ext S; constructor
      · rintro ⟨C, -, rfl⟩; exact ⟨structMap hLaw hst C, ⟨C, trivial, rfl⟩, rfl⟩
      · rintro ⟨C, ⟨C', -, rfl⟩, rfl⟩; exact ⟨C', trivial, rfl⟩]
  exact Subtype.val_injective.encard_image
    ((fun C : comps stage J s => structMap hLaw hst C) '' Set.univ)

theorem window_ineq_Y {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop} {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    {α ε : ℝ} (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq2 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (y : comps stageY JY β'),
      ψ β hβ (structMap hLawY hle y) =
        structMap hLawX (show β - ε ≤ β' - ε by linarith) (ψ β' hβ' y))
    (hSq3 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (y : comps stageY JY β),
      φ (β - ε) hβε (ψ β hβ y) =
        structMap hLawY (show (β - ε) - ε ≤ β by linarith) y)
    {s t : ℝ} (hst : t ≤ s) (hα : α ≤ t - ε) :
    rankFn stageY JY s ((t - ε) - ε) ≤ rankFn stageX JX (s - ε) (t - ε) := by
  have hβ : α ≤ t := by linarith
  have hαs : α ≤ s := by linarith
  have hX : (t - ε) - ε ≤ s := by linarith
  have hY : t - ε ≤ s - ε := by linarith
  have hgt : (t - ε) - ε ≤ t := by linarith
  rw [rankFn_eq_structImage' hLawY hX]
  have hA : (Set.univ.image (fun C : comps stageY JY s => structMap hLawY hX C))
      = (fun v : comps stageY JY t => structMap hLawY hgt v) ''
        (Set.univ.image (fun C : comps stageY JY s => structMap hLawY hst C)) := by
    ext R; constructor
    · rintro ⟨C, -, rfl⟩
      refine ⟨structMap hLawY hst C, ⟨C, trivial, rfl⟩, ?_⟩
      show structMap hLawY hgt (structMap hLawY hst C) = structMap hLawY hX C
      rw [structMap_comp hLawY hgt hst C]
    · rintro ⟨v, ⟨C, -, rfl⟩, rfl⟩
      refine ⟨C, trivial, ?_⟩
      show structMap hLawY hX C = structMap hLawY hgt (structMap hLawY hst C)
      exact (structMap_comp hLawY hgt hst C).symm
  have hB : (fun v : comps stageY JY t => structMap hLawY hgt v) ''
        (Set.univ.image (fun C : comps stageY JY s => structMap hLawY hst C))
      = (fun w : comps stageX JX (t - ε) => φ (t - ε) hα w) ''
        ((fun v : comps stageY JY t => ψ t hβ v) ''
          (Set.univ.image (fun C : comps stageY JY s => structMap hLawY hst C))) := by
    ext R; constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨ψ t hβ v, ⟨v, hv, rfl⟩, ?_⟩
      show φ (t - ε) hα (ψ t hβ v) = structMap hLawY hgt v
      rw [hSq3 t hβ hα v]
    · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
      refine ⟨v, hv, ?_⟩
      show structMap hLawY hgt v = φ (t - ε) hα (ψ t hβ v)
      rw [hSq3 t hβ hα v]
  have hD : ((fun v : comps stageY JY t => ψ t hβ v) ''
        (Set.univ.image (fun C : comps stageY JY s => structMap hLawY hst C)))
      ⊆ (fun C' : comps stageX JX (s - ε) => structMap hLawX hY C') '' Set.univ := by
    rintro R ⟨v, ⟨C, -, rfl⟩, rfl⟩
    refine ⟨ψ s hαs C, trivial, ?_⟩
    show structMap hLawX hY (ψ s hαs C) = ψ t hβ (structMap hLawY hst C)
    exact (hSq2 t s hβ hαs hst C).symm
  calc (Set.univ.image (fun C : comps stageY JY s => structMap hLawY hX C)).encard
      = ((fun v : comps stageY JY t => structMap hLawY hgt v) ''
          (Set.univ.image (fun C : comps stageY JY s => structMap hLawY hst C))).encard := by
        rw [hA]
    _ = ((fun w : comps stageX JX (t - ε) => φ (t - ε) hα w) ''
          ((fun v : comps stageY JY t => ψ t hβ v) ''
            (Set.univ.image (fun C : comps stageY JY s => structMap hLawY hst C)))).encard := by
        rw [hB]
    _ ≤ ((fun v : comps stageY JY t => ψ t hβ v) ''
          (Set.univ.image (fun C : comps stageY JY s => structMap hLawY hst C))).encard :=
        Set.encard_image_le _ _
    _ ≤ ((fun C' : comps stageX JX (s - ε) => structMap hLawX hY C') '' Set.univ).encard :=
        Set.encard_le_encard hD
    _ = rankFn stageX JX (s - ε) (t - ε) := (rankFn_eq_structImage' hLawX hY).symm

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

theorem t5_countKill {ιX ιY : Type*}
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
    (hcountY : ∀ C : comps stageY JY (β - ε), s < birthSup hLawY (β - ε) C)
    (hgenX : ∀ D : comps stageX JX β, s - ε ≠ birthSup hLawX β D)
    (hO : ∃ O : comps stageY JY (β - ε), ∀ D : comps stageX JX β,
        s - ε < birthSup hLawX β D → φ β hβα D ≠ O)
    (hinj : ∀ D₁ D₂ : comps stageX JX β, s - ε < birthSup hLawX β D₁ →
        s - ε < birthSup hLawX β D₂ → φ β hβα D₁ = φ β hβα D₂ → D₁ = D₂) :
    rankFn stageX JX (s - ε) β < rankFn stageY JY s (β - ε) := by
  -- Y side: every Y-cell counts (hcountY), so the Y-rank is the full census at level β−ε.
  have hstY : β - ε ≤ s := by linarith
  have hsY : ∀ C : comps stageY JY (β - ε), s ≠ birthSup hLawY (β - ε) C := by
    intro C hC
    exact absurd (hC ▸ hcountY C) (lt_irrefl s)
  have hRY : rankFn stageY JY s (β - ε) =
      {C : comps stageY JY (β - ε) | s < birthSup hLawY (β - ε) C}.encard :=
    t3_rank_orig hLawY hTameY hstY hsY
  have huniv : {C : comps stageY JY (β - ε) | s < birthSup hLawY (β - ε) C}
      = (Set.univ : Set (comps stageY JY (β - ε))) := by
    ext C
    simp only [Set.mem_ofPred_eq, Set.mem_univ]
    exact ⟨fun _ => trivial, fun _ => hcountY C⟩
  have hRY' : rankFn stageY JY s (β - ε)
      = (Set.univ : Set (comps stageY JY (β - ε))).encard := by
    rw [hRY, huniv]
  -- X side: the rank counts the X-cells alive past s−ε.
  have hstX : β ≤ s - ε := by linarith
  have hRX : rankFn stageX JX (s - ε) β =
      {D : comps stageX JX β | s - ε < birthSup hLawX β D}.encard :=
    t3_rank_orig hLawX hTameX hstX hgenX
  obtain ⟨O, hO⟩ := hO
  -- the counted X-cells map into `univ \ {O}` and the map is injective there
  have hle : {D : comps stageX JX β | s - ε < birthSup hLawX β D}.encard ≤
      (Set.univ \ {O} : Set (comps stageY JY (β - ε))).encard := by
    refine Set.encard_le_encard_of_injOn (f := fun D => φ β hβα D) (fun D hD => ?_)
      (fun D₁ hD₁ D₂ hD₂ heq => ?_)
    · exact ⟨Set.mem_univ _, fun hmem => hO D hD (Set.mem_singleton_iff.mp hmem)⟩
    · exact hinj D₁ D₂ hD₁ hD₂ heq
  -- strictness: the full census exceeds the census minus the outliver
  haveI hfinY : Finite (comps stageY JY (β - ε)) := (hTameY.1 (β - ε)).to_subtype
  have hfin : (Set.univ \ {O} : Set (comps stageY JY (β - ε))).Finite :=
    Set.finite_univ.sdiff
  have hsub : (Set.univ \ {O} : Set (comps stageY JY (β - ε)))
      ⊂ (Set.univ : Set (comps stageY JY (β - ε))) :=
    Set.ssubset_univ_iff.mpr (by
      intro h
      have hu : O ∈ (Set.univ : Set (comps stageY JY (β - ε))) := Set.mem_univ _
      rw [← h] at hu
      exact hu.2 (Set.mem_singleton_iff.mpr rfl))
  have hlt := hfin.encard_lt_encard hsub
  calc rankFn stageX JX (s - ε) β
      = {D : comps stageX JX β | s - ε < birthSup hLawX β D}.encard := hRX
    _ ≤ (Set.univ \ {O} : Set (comps stageY JY (β - ε))).encard := hle
    _ < (Set.univ : Set (comps stageY JY (β - ε))).encard := hlt
    _ = rankFn stageY JY s (β - ε) := hRY'.symm

/-- Death-kill (phi-side configuration elimination): the census
configuration of the count-gap lemma -- every Y-cell at the
pullback level born above s, no X-cell at level beta born
at s - eps, and the counted X-cells injecting under phi
into the Y-cells minus one outliver -- is IMPOSSIBLE. The
count-gap lemma makes the X-window rank strictly below the
Y-window rank, while the psi-side window inequality over
the same window bounds the Y-rank by the X-rank: together a
contradiction. -/
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
    (hcountY : ∀ C : comps stageY JY (β - ε), s < birthSup hLawY (β - ε) C)
    (hgenX : ∀ D : comps stageX JX β, s - ε ≠ birthSup hLawX β D)
    (hO : ∃ O : comps stageY JY (β - ε), ∀ D : comps stageX JX β,
        s - ε < birthSup hLawX β D → φ β hβα D ≠ O)
    (hinj : ∀ D₁ D₂ : comps stageX JX β, s - ε < birthSup hLawX β D₁ →
        s - ε < birthSup hLawX β D₂ → φ β hβα D₁ = φ β hβα D₂ → D₁ = D₂) : False := by
  have h1 := t5_countKill hLawX hLawY hTameX hTameY hε φ ψ hSq1 hSq2 hSq3 hSq4 hβα hwin
    hcountY hgenX hO hinj
  have h2 : rankFn stageY JY s (β - ε) ≤ rankFn stageX JX (s - ε) β := by
    have h2 := window_ineq_Y hLawX hLawY hε φ ψ hSq2 hSq3
      (show β + ε ≤ s by linarith) (show α ≤ β + ε - ε by linarith)
    rw [show β + ε - ε = β from by ring] at h2
    exact h2
  exact lt_irrefl _ (h1.trans_le h2)
