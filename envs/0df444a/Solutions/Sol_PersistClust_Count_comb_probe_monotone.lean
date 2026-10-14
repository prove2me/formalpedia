-- Prove2me | solution 1 for PersistClust.Count.comb_probe_monotone
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-12T20:14:24.611301+00:00
-- url     : https://prove2.me/submissions/feb59a1d-20c8-40e3-a5f9-324dd5e9c065

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

theorem t3_add_sub {a b : ℕ∞} (hfin : a ≠ ⊤) : (a + b) - a = b := by
  cases a with
  | top => exact absurd rfl hfin
  | coe m =>
      cases b with
      | top => simp
      | coe n => exact_mod_cast Nat.add_sub_cancel_left m n

theorem solution {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
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

/-! ## T3a final rungs: the beta = b census reduction at small eta. -/
