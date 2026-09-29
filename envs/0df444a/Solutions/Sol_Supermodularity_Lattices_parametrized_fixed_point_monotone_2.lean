-- Prove2me | solution 2 for Supermodularity.Lattices.parametrized_fixed_point_monotone
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-26T22:46:49.89951+00:00
-- url     : https://prove2.me/submissions/42e9616b-d571-4be5-8143-9310a4044c6d

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_Supermodularity_Lattices_Subcomplete

namespace Supermodularity.Lattices

section Zhou

variable {X : Type*} [CompleteLattice X] (Z : X → Set X)
  (hne : ∀ x, (Z x).Nonempty) (hsub : ∀ x, Subcomplete (Z x))
  (hinc : ∀ ⦃x x' : X⦄, x ≤ x' → InducedSetOrder (Z x) (Z x'))
include hne hsub hinc

/-- Zhou's theorem, greatest fixed point: `sup {x | ∃ y ∈ Z x, x ≤ y}` is the greatest fixed
point of an increasing correspondence with nonempty subcomplete values. -/
lemma zhou_greatest : IsGreatest {x | x ∈ Z x} (sSup {x | ∃ y ∈ Z x, x ≤ y}) := by
  set S := {x | ∃ y ∈ Z x, x ≤ y} with hS
  set a := sSup S
  have step1 : ∀ x ∈ S, ∃ w ∈ Z a, x ≤ w := by
    rintro x ⟨y, hy, hxy⟩
    obtain ⟨z, hz⟩ := hne a
    exact ⟨y ⊔ z, (hinc (le_sSup (show x ∈ S from ⟨y, hy, hxy⟩)) hy hz).2, hxy.trans le_sup_left⟩
  have hbot : (⊥ : X) ∈ S := by obtain ⟨z, hz⟩ := hne ⊥; exact ⟨z, hz, bot_le⟩
  set U := {w | w ∈ Z a ∧ ∃ x ∈ S, x ≤ w}
  have hUne : U.Nonempty := by
    obtain ⟨w, hw, hle⟩ := step1 ⊥ hbot; exact ⟨w, hw, ⊥, hbot, hle⟩
  obtain ⟨s, hsU, hsZ⟩ := ((hsub a).2 (fun w hw => hw.1) hUne).1
  have has : a ≤ s := sSup_le fun x hx => by
    obtain ⟨w, hw, hle⟩ := step1 x hx
    exact hle.trans (hsU.1 ⟨hw, x, hx, hle⟩)
  have hsS : s ∈ S := by
    obtain ⟨u, hu⟩ := hne s
    exact ⟨s ⊔ u, (hinc has hsZ hu).2, le_sup_left⟩
  have hsa : s = a := le_antisymm (le_sSup hsS) has
  refine ⟨hsa ▸ hsZ, fun x hx => le_sSup ⟨x, hx, le_rfl⟩⟩

/-- Zhou's theorem, least fixed point. -/
lemma zhou_least : IsLeast {x | x ∈ Z x} (sInf {x | ∃ y ∈ Z x, y ≤ x}) := by
  set S := {x | ∃ y ∈ Z x, y ≤ x} with hS
  set a := sInf S
  have step1 : ∀ x ∈ S, ∃ w ∈ Z a, w ≤ x := by
    rintro x ⟨y, hy, hxy⟩
    obtain ⟨z, hz⟩ := hne a
    exact ⟨z ⊓ y, (hinc (sInf_le (show x ∈ S from ⟨y, hy, hxy⟩)) hz hy).1, inf_le_right.trans hxy⟩
  have htop : (⊤ : X) ∈ S := by obtain ⟨z, hz⟩ := hne ⊤; exact ⟨z, hz, le_top⟩
  set U := {w | w ∈ Z a ∧ ∃ x ∈ S, w ≤ x}
  have hUne : U.Nonempty := by
    obtain ⟨w, hw, hle⟩ := step1 ⊤ htop; exact ⟨w, hw, ⊤, htop, hle⟩
  obtain ⟨s, hsU, hsZ⟩ := ((hsub a).2 (fun w hw => hw.1) hUne).2
  have has : s ≤ a := le_sInf fun x hx => by
    obtain ⟨w, hw, hle⟩ := step1 x hx
    exact (hsU.1 ⟨hw, x, hx, hle⟩).trans hle
  have hsS : s ∈ S := by
    obtain ⟨u, hu⟩ := hne s
    exact ⟨u ⊓ s, (hinc has hu hsZ).1, inf_le_right⟩
  have hsa : s = a := le_antisymm has (sInf_le hsS)
  refine ⟨hsa ▸ hsZ, fun x hx => sInf_le ⟨x, hx, le_rfl⟩⟩

end Zhou

theorem pfp_main {X : Type*} [CompleteLattice X] {T : Type*}
    [PartialOrder T] (Y : X → T → Set X)
    (hne : ∀ x : X, ∀ t : T, (Y x t).Nonempty) (hsub : ∀ x : X, ∀ t : T, Subcomplete (Y x t))
    (hinc : ∀ ⦃x x' : X⦄, ∀ ⦃t t' : T⦄, x ≤ x' → t ≤ t' → InducedSetOrder (Y x t) (Y x' t')) :
    ∃ g l : T → X,
      Monotone g ∧ Monotone l ∧
        (∀ t : T, IsGreatest {x : X | x ∈ Y x t} (g t)) ∧
        (∀ t : T, IsLeast {x : X | x ∈ Y x t} (l t)) ∧
        ((∀ x' : X, ∀ ⦃t' t'' : T⦄, t' < t'' → sSup (Y x' t') < sInf (Y x' t'')) →
          StrictMono g ∧ StrictMono l) := by
  set g : T → X := fun t => sSup {x | ∃ y ∈ Y x t, x ≤ y}
  set l : T → X := fun t => sInf {x | ∃ y ∈ Y x t, y ≤ x}
  have hG : ∀ t, IsGreatest {x : X | x ∈ Y x t} (g t) := fun t =>
    zhou_greatest (fun x => Y x t) (fun x => hne x t) (fun x => hsub x t)
      (fun _ _ h => hinc h le_rfl)
  have hL : ∀ t, IsLeast {x : X | x ∈ Y x t} (l t) := fun t =>
    zhou_least (fun x => Y x t) (fun x => hne x t) (fun x => hsub x t)
      (fun _ _ h => hinc h le_rfl)
  have mg : Monotone g := by
    intro t t' htt
    have hx : g t ∈ Y (g t) t := (hG t).1
    obtain ⟨z, hz⟩ := hne (g t) t'
    exact le_sSup ⟨g t ⊔ z, (hinc le_rfl htt hx hz).2, le_sup_left⟩
  have ml : Monotone l := by
    intro t t' htt
    have hy : l t' ∈ Y (l t') t' := (hL t').1
    obtain ⟨z, hz⟩ := hne (l t') t
    exact sInf_le ⟨z ⊓ l t', (hinc le_rfl htt hz hy).1, inf_le_right⟩
  refine ⟨g, l, mg, ml, hG, hL, fun H => ⟨fun t t' htt => ?_, fun t t' htt => ?_⟩⟩
  · refine lt_of_le_of_ne (mg htt.le) fun heq => ?_
    have h1 : g t ∈ Y (g t) t := (hG t).1
    have h2 : g t ∈ Y (g t) t' := heq ▸ (hG t').1
    have := H (g t) htt
    exact absurd ((le_sSup h1).trans_lt (this.trans_le (sInf_le h2))) (lt_irrefl _)
  · refine lt_of_le_of_ne (ml htt.le) fun heq => ?_
    have h1 : l t ∈ Y (l t) t := (hL t).1
    have h2 : l t ∈ Y (l t) t' := heq ▸ (hL t').1
    have := H (l t) htt
    exact absurd ((le_sSup h1).trans_lt (this.trans_le (sInf_le h2))) (lt_irrefl _)

end Supermodularity.Lattices

open Supermodularity.Lattices

theorem solution {X : Type*} [CompleteLattice X] {T : Type*}
    [PartialOrder T] (Y : X → T → Set X)
    (hne : ∀ x : X, ∀ t : T, (Y x t).Nonempty) (hsub : ∀ x : X, ∀ t : T, Subcomplete (Y x t))
    (hinc : ∀ ⦃x x' : X⦄, ∀ ⦃t t' : T⦄, x ≤ x' → t ≤ t' → InducedSetOrder (Y x t) (Y x' t')) :
    ∃ g l : T → X,
      Monotone g ∧ Monotone l ∧
        (∀ t : T, IsGreatest {x : X | x ∈ Y x t} (g t)) ∧
        (∀ t : T, IsLeast {x : X | x ∈ Y x t} (l t)) ∧
        ((∀ x' : X, ∀ ⦃t' t'' : T⦄, t' < t'' → sSup (Y x' t') < sInf (Y x' t'')) →
          StrictMono g ∧ StrictMono l) :=
  pfp_main Y hne hsub hinc
