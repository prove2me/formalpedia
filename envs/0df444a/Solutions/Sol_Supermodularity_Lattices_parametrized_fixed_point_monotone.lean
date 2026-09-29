-- Prove2me | solution 1 for Supermodularity.Lattices.parametrized_fixed_point_monotone
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T22:33:05.074242+00:00
-- url     : https://prove2.me/submissions/0e293111-07e9-4e1c-9102-2ac4ff7ada97

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_Supermodularity_Lattices_Subcomplete

set_option autoImplicit false

open Supermodularity.Lattices in
/-- A subcomplete set contains the infimum of each of its nonempty subsets. -/
lemma zhou_sInf_mem_f4999b4b {X : Type*} [CompleteLattice X] {S W : Set X}
    (h : Subcomplete S) (hW : W ⊆ S) (hne : W.Nonempty) : sInf W ∈ S := by
  obtain ⟨i, hi, hiS⟩ := (h.2 hW hne).2
  rwa [hi.sInf_eq]

open Supermodularity.Lattices in
/-- A subcomplete set contains the supremum of each of its nonempty subsets. -/
lemma zhou_sSup_mem_f4999b4b {X : Type*} [CompleteLattice X] {S W : Set X}
    (h : Subcomplete S) (hW : W ⊆ S) (hne : W.Nonempty) : sSup W ∈ S := by
  obtain ⟨i, hi, hiS⟩ := (h.2 hW hne).1
  rwa [hi.sSup_eq]

open Supermodularity.Lattices in
/-- Greatest fixed point below `s` (Zhou's construction). -/
lemma zhou_gfp_below_f4999b4b {X : Type*} [CompleteLattice X] (Y : X → Set X)
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
  have hwY : w ∈ Y a := zhou_sSup_mem_f4999b4b (hsub a) hWsub hWne
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
lemma zhou_lfp_above_f4999b4b {X : Type*} [CompleteLattice X] (Y : X → Set X)
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
  have hwY : w ∈ Y b := zhou_sInf_mem_f4999b4b (hsub b) hWsub hWne
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
/-- Greatest fixed point of an increasing correspondence. -/
lemma zhou_gfp_top_f4999b4b {X : Type*} [CompleteLattice X] (Y : X → Set X)
    (hinc : ∀ ⦃x x' : X⦄, x ≤ x' → InducedSetOrder (Y x) (Y x'))
    (hne : ∀ x : X, (Y x).Nonempty) (hsub : ∀ x : X, Subcomplete (Y x)) :
    sSup {x : X | (Y x ∩ Set.Ici x).Nonempty} ∈ Y (sSup {x : X | (Y x ∩ Set.Ici x).Nonempty}) ∧
      ∀ x, x ∈ Y x → x ≤ sSup {x : X | (Y x ∩ Set.Ici x).Nonempty} := by
  have hAeq : {x : X | x ≤ ⊤ ∧ ∃ y ∈ Y x, x ≤ y ∧ y ≤ ⊤}
      = {x : X | (Y x ∩ Set.Ici x).Nonempty} := by
    ext x
    constructor
    · rintro ⟨-, y, hy, hxy, -⟩
      exact ⟨y, hy, hxy⟩
    · rintro ⟨y, hy, hxy⟩
      exact ⟨le_top, y, hy, hxy, le_top⟩
  have hsTop : ∀ x, x ≤ (⊤ : X) → ∃ y ∈ Y x, y ≤ ⊤ := by
    intro x _
    obtain ⟨y, hy⟩ := hne x
    exact ⟨y, hy, le_top⟩
  obtain ⟨ha1, -, ha3⟩ := zhou_gfp_below_f4999b4b Y hinc hsub ⊤ hsTop
    (sSup {x : X | (Y x ∩ Set.Ici x).Nonempty}) (by rw [hAeq])
  exact ⟨ha1, fun x hx => ha3 x hx le_top⟩

open Supermodularity.Lattices in
/-- Least fixed point of an increasing correspondence. -/
lemma zhou_lfp_bot_f4999b4b {X : Type*} [CompleteLattice X] (Y : X → Set X)
    (hinc : ∀ ⦃x x' : X⦄, x ≤ x' → InducedSetOrder (Y x) (Y x'))
    (hne : ∀ x : X, (Y x).Nonempty) (hsub : ∀ x : X, Subcomplete (Y x)) :
    sInf {x : X | (Y x ∩ Set.Iic x).Nonempty} ∈ Y (sInf {x : X | (Y x ∩ Set.Iic x).Nonempty}) ∧
      ∀ x, x ∈ Y x → sInf {x : X | (Y x ∩ Set.Iic x).Nonempty} ≤ x := by
  have hBeq : {x : X | ⊥ ≤ x ∧ ∃ y ∈ Y x, ⊥ ≤ y ∧ y ≤ x}
      = {x : X | (Y x ∩ Set.Iic x).Nonempty} := by
    ext x
    constructor
    · rintro ⟨-, y, hy, -, hyx⟩
      exact ⟨y, hy, hyx⟩
    · rintro ⟨y, hy, hyx⟩
      exact ⟨bot_le, y, hy, bot_le, hyx⟩
  have hsBot : ∀ x, (⊥ : X) ≤ x → ∃ y ∈ Y x, ⊥ ≤ y := by
    intro x _
    obtain ⟨y, hy⟩ := hne x
    exact ⟨y, hy, bot_le⟩
  obtain ⟨hb1, -, hb3⟩ := zhou_lfp_above_f4999b4b Y hinc hsub ⊥ hsBot
    (sInf {x : X | (Y x ∩ Set.Iic x).Nonempty}) (by rw [hBeq])
  exact ⟨hb1, fun x hx => hb3 x hx bot_le⟩

open Supermodularity.Lattices in
theorem solution {X : Type*} [CompleteLattice X] {T : Type*}
    [PartialOrder T] (Y : X → T → Set X)
    (hne : ∀ x : X, ∀ t : T, (Y x t).Nonempty) (hsub : ∀ x : X, ∀ t : T, Subcomplete (Y x t))
    (hinc : ∀ ⦃x x' : X⦄, ∀ ⦃t t' : T⦄, x ≤ x' → t ≤ t' → InducedSetOrder (Y x t) (Y x' t')) :
    ∃ g l : T → X,
      Monotone g ∧ Monotone l ∧
        (∀ t : T, IsGreatest {x : X | x ∈ Y x t} (g t)) ∧
        (∀ t : T, IsLeast {x : X | x ∈ Y x t} (l t)) ∧
        ((∀ x' : X, ∀ ⦃t' t'' : T⦄, t' < t'' → sSup (Y x' t') < sInf (Y x' t'')) →
          StrictMono g ∧ StrictMono l) := by
  obtain ⟨g, hg⟩ : ∃ g : T → X, ∀ t, g t = sSup {x : X | (Y x t ∩ Set.Ici x).Nonempty} :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨l, hl⟩ : ∃ l : T → X, ∀ t, l t = sInf {x : X | (Y x t ∩ Set.Iic x).Nonempty} :=
    ⟨_, fun _ => rfl⟩
  have hG : ∀ t, g t ∈ Y (g t) t ∧ ∀ x, x ∈ Y x t → x ≤ g t := by
    intro t
    rw [hg t]
    exact zhou_gfp_top_f4999b4b (fun x => Y x t) (fun _ _ h => hinc h le_rfl)
      (fun x => hne x t) (fun x => hsub x t)
  have hL : ∀ t, l t ∈ Y (l t) t ∧ ∀ x, x ∈ Y x t → l t ≤ x := by
    intro t
    rw [hl t]
    exact zhou_lfp_bot_f4999b4b (fun x => Y x t) (fun _ _ h => hinc h le_rfl)
      (fun x => hne x t) (fun x => hsub x t)
  have hgm : Monotone g := by
    intro t t' htt'
    have ha := (hG t).1
    have hm : sSup (Y (g t) t') ∈ Y (g t) t' :=
      zhou_sSup_mem_f4999b4b (hsub (g t) t') subset_rfl (hne (g t) t')
    have h1 : g t ⊔ sSup (Y (g t) t') ∈ Y (g t) t' := ((hinc le_rfl htt') ha hm).2
    have h2 : g t ≤ sSup (Y (g t) t') := le_sup_left.trans (le_sSup h1)
    rw [hg t']
    exact le_sSup ⟨sSup (Y (g t) t'), hm, h2⟩
  have hlm : Monotone l := by
    intro t t' htt'
    have hb := (hL t').1
    have hm : sInf (Y (l t') t) ∈ Y (l t') t :=
      zhou_sInf_mem_f4999b4b (hsub (l t') t) subset_rfl (hne (l t') t)
    have h1 : sInf (Y (l t') t) ⊓ l t' ∈ Y (l t') t := ((hinc le_rfl htt') hm hb).1
    have h2 : sInf (Y (l t') t) ≤ l t' := (sInf_le h1).trans inf_le_right
    rw [hl t]
    exact sInf_le ⟨sInf (Y (l t') t), hm, h2⟩
  refine ⟨g, l, hgm, hlm, fun t => ⟨(hG t).1, fun x hx => (hG t).2 x hx⟩,
    fun t => ⟨(hL t).1, fun x hx => (hL t).2 x hx⟩, ?_⟩
  intro H
  constructor
  · intro t t' htt'
    refine lt_of_le_of_ne (hgm htt'.le) (fun heq => ?_)
    have h1 := (hG t).1
    have h2 := (hG t').1
    rw [← heq] at h2
    exact lt_irrefl _ ((le_sSup h1).trans_lt ((H _ htt').trans_le (sInf_le h2)))
  · intro t t' htt'
    refine lt_of_le_of_ne (hlm htt'.le) (fun heq => ?_)
    have h1 := (hL t).1
    have h2 := (hL t').1
    rw [← heq] at h2
    exact lt_irrefl _ ((le_sSup h1).trans_lt ((H _ htt').trans_le (sInf_le h2)))
