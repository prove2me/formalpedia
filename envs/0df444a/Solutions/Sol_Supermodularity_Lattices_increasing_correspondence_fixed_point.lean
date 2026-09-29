-- Prove2me | solution 1 for Supermodularity.Lattices.increasing_correspondence_fixed_point
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T21:04:49.291322+00:00
-- url     : https://prove2.me/submissions/dd87fae4-eaf9-4504-a4cf-f461d333c0f1

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_Supermodularity_Lattices_Subcomplete

set_option autoImplicit false

open Supermodularity.Lattices in
/-- A subcomplete set contains the infimum of each of its nonempty subsets. -/
lemma zhou_sInf_mem_f2e385ae {X : Type*} [CompleteLattice X] {S W : Set X}
    (h : Subcomplete S) (hW : W ⊆ S) (hne : W.Nonempty) : sInf W ∈ S := by
  obtain ⟨i, hi, hiS⟩ := (h.2 hW hne).2
  rwa [hi.sInf_eq]

open Supermodularity.Lattices in
/-- A subcomplete set contains the supremum of each of its nonempty subsets. -/
lemma zhou_sSup_mem_f2e385ae {X : Type*} [CompleteLattice X] {S W : Set X}
    (h : Subcomplete S) (hW : W ⊆ S) (hne : W.Nonempty) : sSup W ∈ S := by
  obtain ⟨i, hi, hiS⟩ := (h.2 hW hne).1
  rwa [hi.sSup_eq]

open Supermodularity.Lattices in
/-- Greatest fixed point below `s` (Zhou's construction). -/
lemma zhou_gfp_below_f2e385ae {X : Type*} [CompleteLattice X] (Y : X → Set X)
    (hinc : ∀ ⦃x x' : X⦄, x ≤ x' → InducedSetOrder (Y x) (Y x'))
    (hsub : ∀ x : X, Subcomplete (Y x)) (s : X)
    (hs : ∀ x, x ≤ s → ∃ y ∈ Y x, y ≤ s) (a : X)
    (ha : a = sSup {x | x ≤ s ∧ ∃ y ∈ Y x, x ≤ y ∧ y ≤ s}) :
    a ∈ Y a ∧ a ≤ s ∧ ∀ x, x ∈ Y x → x ≤ s → x ≤ a := by
  have hA : ∀ x, x ≤ s → (∃ y ∈ Y x, x ≤ y ∧ y ≤ s) → x ≤ a := by
    intro x hx1 hx2
    rw [ha]
    exact le_sSup ⟨hx1, hx2⟩
  have has : a ≤ s := by
    rw [ha]
    exact sSup_le (fun x hx => hx.1)
  obtain ⟨z0, hz0, hz0s⟩ := hs a has
  have hWsub : Y a ∩ Set.Iic s ⊆ Y a := Set.inter_subset_left
  have hWne : (Y a ∩ Set.Iic s).Nonempty := ⟨z0, hz0, hz0s⟩
  set w := sSup (Y a ∩ Set.Iic s) with hw
  have hwY : w ∈ Y a := zhou_sSup_mem_f2e385ae (hsub a) hWsub hWne
  have hws : w ≤ s := sSup_le (fun y hy => hy.2)
  have haw : a ≤ w := by
    rw [ha]
    refine sSup_le ?_
    rintro x ⟨hxs, y, hy, hxy, hys⟩
    have hxa : x ≤ a := hA x hxs ⟨y, hy, hxy, hys⟩
    have h1 : y ⊔ w ∈ Y a := ((hinc hxa) hy hwY).2
    have h2 : y ⊔ w ≤ w := le_sSup ⟨h1, sup_le hys hws⟩
    exact hxy.trans (le_sup_left.trans h2)
  have hwa : w ≤ a := by
    obtain ⟨z, hz, hzs⟩ := hs w hws
    have h1 : w ⊔ z ∈ Y w := ((hinc haw) hwY hz).2
    exact hA w hws ⟨w ⊔ z, h1, le_sup_left, sup_le hws hzs⟩
  have hEq : a = w := le_antisymm haw hwa
  refine ⟨?_, has, ?_⟩
  · rw [hEq] at hwY ⊢
    exact hwY
  · intro x hx hxs
    exact hA x hxs ⟨x, hx, le_rfl, hxs⟩

open Supermodularity.Lattices in
/-- Least fixed point above `s` (Zhou's construction). -/
lemma zhou_lfp_above_f2e385ae {X : Type*} [CompleteLattice X] (Y : X → Set X)
    (hinc : ∀ ⦃x x' : X⦄, x ≤ x' → InducedSetOrder (Y x) (Y x'))
    (hsub : ∀ x : X, Subcomplete (Y x)) (s : X)
    (hs : ∀ x, s ≤ x → ∃ y ∈ Y x, s ≤ y) (b : X)
    (hb : b = sInf {x | s ≤ x ∧ ∃ y ∈ Y x, s ≤ y ∧ y ≤ x}) :
    b ∈ Y b ∧ s ≤ b ∧ ∀ x, x ∈ Y x → s ≤ x → b ≤ x := by
  have hB : ∀ x, s ≤ x → (∃ y ∈ Y x, s ≤ y ∧ y ≤ x) → b ≤ x := by
    intro x hx1 hx2
    rw [hb]
    exact sInf_le ⟨hx1, hx2⟩
  have hsb : s ≤ b := by
    rw [hb]
    exact le_sInf (fun x hx => hx.1)
  obtain ⟨z0, hz0, hz0s⟩ := hs b hsb
  have hWsub : Y b ∩ Set.Ici s ⊆ Y b := Set.inter_subset_left
  have hWne : (Y b ∩ Set.Ici s).Nonempty := ⟨z0, hz0, hz0s⟩
  set w := sInf (Y b ∩ Set.Ici s) with hw
  have hwY : w ∈ Y b := zhou_sInf_mem_f2e385ae (hsub b) hWsub hWne
  have hsw : s ≤ w := le_sInf (fun y hy => hy.2)
  have hwb : w ≤ b := by
    rw [hb]
    refine le_sInf ?_
    rintro x ⟨hsx, y, hy, hsy, hyx⟩
    have hbx : b ≤ x := hB x hsx ⟨y, hy, hsy, hyx⟩
    have h1 : w ⊓ y ∈ Y b := ((hinc hbx) hwY hy).1
    have h2 : w ≤ w ⊓ y := sInf_le ⟨h1, le_inf hsw hsy⟩
    exact (h2.trans inf_le_right).trans hyx
  have hbw : b ≤ w := by
    obtain ⟨z, hz, hsz⟩ := hs w hsw
    have h1 : z ⊓ w ∈ Y w := ((hinc hwb) hz hwY).1
    exact hB w hsw ⟨z ⊓ w, h1, le_inf hsz hsw, inf_le_right⟩
  have hEq : b = w := le_antisymm hbw hwb
  refine ⟨?_, hsb, ?_⟩
  · rw [hEq] at hwY ⊢
    exact hwY
  · intro x hx hsx
    exact hB x hsx ⟨x, hx, hsx, le_rfl⟩

open Supermodularity.Lattices in
theorem solution {X : Type*} [CompleteLattice X] (Y : X → Set X)
    (hinc : ∀ ⦃x x' : X⦄, x ≤ x' → InducedSetOrder (Y x) (Y x'))
    (hne : ∀ x : X, (Y x).Nonempty) (hsub : ∀ x : X, Subcomplete (Y x)) :
    {x : X | x ∈ Y x}.Nonempty ∧
      IsGreatest {x : X | x ∈ Y x} (sSup {x : X | (Y x ∩ Set.Ici x).Nonempty}) ∧
      IsLeast {x : X | x ∈ Y x} (sInf {x : X | (Y x ∩ Set.Iic x).Nonempty}) ∧
      (∀ F : Set {x : X // x ∈ Y x}, F.Nonempty → ∃ m, IsLUB F m) ∧
      (∀ F : Set {x : X // x ∈ Y x}, F.Nonempty → ∃ m, IsGLB F m) := by
  have hAeq : {x : X | x ≤ ⊤ ∧ ∃ y ∈ Y x, x ≤ y ∧ y ≤ ⊤}
      = {x : X | (Y x ∩ Set.Ici x).Nonempty} := by
    ext x
    constructor
    · rintro ⟨-, y, hy, hxy, -⟩
      exact ⟨y, hy, hxy⟩
    · rintro ⟨y, hy, hxy⟩
      exact ⟨le_top, y, hy, hxy, le_top⟩
  have hBeq : {x : X | ⊥ ≤ x ∧ ∃ y ∈ Y x, ⊥ ≤ y ∧ y ≤ x}
      = {x : X | (Y x ∩ Set.Iic x).Nonempty} := by
    ext x
    constructor
    · rintro ⟨-, y, hy, -, hyx⟩
      exact ⟨y, hy, hyx⟩
    · rintro ⟨y, hy, hyx⟩
      exact ⟨bot_le, y, hy, bot_le, hyx⟩
  have hsTop : ∀ x, x ≤ (⊤ : X) → ∃ y ∈ Y x, y ≤ ⊤ := by
    intro x _
    obtain ⟨y, hy⟩ := hne x
    exact ⟨y, hy, le_top⟩
  have hsBot : ∀ x, (⊥ : X) ≤ x → ∃ y ∈ Y x, ⊥ ≤ y := by
    intro x _
    obtain ⟨y, hy⟩ := hne x
    exact ⟨y, hy, bot_le⟩
  obtain ⟨ha1, -, ha3⟩ := zhou_gfp_below_f2e385ae Y hinc hsub ⊤ hsTop
    (sSup {x : X | (Y x ∩ Set.Ici x).Nonempty}) (by rw [hAeq])
  obtain ⟨hb1, -, hb3⟩ := zhou_lfp_above_f2e385ae Y hinc hsub ⊥ hsBot
    (sInf {x : X | (Y x ∩ Set.Iic x).Nonempty}) (by rw [hBeq])
  refine ⟨⟨_, ha1⟩, ⟨ha1, fun x hx => ha3 x hx le_top⟩,
    ⟨hb1, fun x hx => hb3 x hx bot_le⟩, ?_, ?_⟩
  · intro F _
    set s := sSup (Subtype.val '' F) with hsdef
    have hs : ∀ x, s ≤ x → ∃ y ∈ Y x, s ≤ y := by
      intro x hsx
      have hm : sSup (Y x) ∈ Y x :=
        zhou_sSup_mem_f2e385ae (hsub x) subset_rfl (hne x)
      refine ⟨sSup (Y x), hm, ?_⟩
      refine sSup_le ?_
      rintro _ ⟨f, hf, rfl⟩
      have hfx : f.1 ≤ x := (le_sSup (Set.mem_image_of_mem Subtype.val hf)).trans hsx
      have h1 : f.1 ⊔ sSup (Y x) ∈ Y x := ((hinc hfx) f.2 hm).2
      exact le_sup_left.trans (le_sSup h1)
    obtain ⟨hc1, hc2, hc3⟩ := zhou_lfp_above_f2e385ae Y hinc hsub s hs _ rfl
    refine ⟨⟨_, hc1⟩, ?_, ?_⟩
    · intro f hf
      show f.1 ≤ _
      exact (le_sSup (Set.mem_image_of_mem Subtype.val hf)).trans hc2
    · intro u hu
      show _ ≤ u.1
      refine hc3 u.1 u.2 ?_
      refine sSup_le ?_
      rintro _ ⟨f, hf, rfl⟩
      exact hu hf
  · intro F _
    set s := sInf (Subtype.val '' F) with hsdef
    have hs : ∀ x, x ≤ s → ∃ y ∈ Y x, y ≤ s := by
      intro x hxs
      have hm : sInf (Y x) ∈ Y x :=
        zhou_sInf_mem_f2e385ae (hsub x) subset_rfl (hne x)
      refine ⟨sInf (Y x), hm, ?_⟩
      refine le_sInf ?_
      rintro _ ⟨f, hf, rfl⟩
      have hxf : x ≤ f.1 := hxs.trans (sInf_le (Set.mem_image_of_mem Subtype.val hf))
      have h1 : sInf (Y x) ⊓ f.1 ∈ Y x := ((hinc hxf) hm f.2).1
      exact (sInf_le h1).trans inf_le_right
    obtain ⟨hc1, hc2, hc3⟩ := zhou_gfp_below_f2e385ae Y hinc hsub s hs _ rfl
    refine ⟨⟨_, hc1⟩, ?_, ?_⟩
    · intro f hf
      show _ ≤ f.1
      exact hc2.trans (sInf_le (Set.mem_image_of_mem Subtype.val hf))
    · intro u hu
      show u.1 ≤ _
      refine hc3 u.1 u.2 ?_
      refine le_sInf ?_
      rintro _ ⟨f, hf, rfl⟩
      exact hu hf
