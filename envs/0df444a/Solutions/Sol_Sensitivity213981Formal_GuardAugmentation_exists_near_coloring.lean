-- Prove2me | solution 1 for Sensitivity213981Formal.GuardAugmentation.exists_near_coloring
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T18:28:06.459348+00:00
-- url     : https://prove2.me/submissions/5c64dcda-3d97-4094-bf50-f7a91c21b908

import Definitions.Def_Sensitivity213981Formal_GuardAugmentation
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Linarith


namespace Sensitivity213981Formal
section
/-
Actual guard augmentation for graded-target candidates.

The optional matching and near-coloring argument is adapted from the accepted
CompactTournament.augment_by_guards proof in the attached Paley11987 source
(prove2.me submission 7f5aa99d-5bc6-4815-915f-ef258368885d). This module specializes
its abstract combinatorics to the actual Boolean selected-child guard sets in
TournamentHighRows and the graded target colors in CandidateCoherence.
-/


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace GuardAugmentation
open scoped Classical
open Finset MinmaxLocal TournamentHighRows CandidateCoherence
noncomputable section

variable {V X : Type} [Fintype V] [DecidableEq V]



theorem neighborhood_deficiency (R : V → V → Prop)
    (ht : ∀ x y, x ≠ y → R x y ∨ R y x) (S : Finset V) :
    S.card ≤  (S.biUnion (neighbors R)).card + 1 := by
  let U := S.biUnion (neighbors R)
  have hsmall : (S \ U).card ≤  1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    obtain ⟨hxS,hxU⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨hyS,hyU⟩ := Finset.mem_sdiff.mp hy
    by_contra hxy
    rcases ht x y hxy with he | he
    · exact hyU (Finset.mem_biUnion.mpr
        ⟨x,hxS,by simp [neighbors, outNeighbors, he]⟩)
    · exact hxU (Finset.mem_biUnion.mpr
        ⟨y,hyS,by simp [neighbors, outNeighbors, he]⟩)
  have hc := Finset.card_sdiff_add_card_inter S U
  have hi := Finset.card_le_card (Finset.inter_subset_right : S ∩ U ⊆ U)
  change S.card ≤  U.card + 1
  omega

theorem exists_optional_matching (R : V → V → Prop)
    (ht : ∀ x y, x ≠ y → R x y ∨ R y x) :
    ∃ f : V → Option V, Function.Injective f ∧
      ∀ x y, f x = some y → R x y := by
  let t : V → Finset (Option V) := fun x => insert none ((neighbors R x).image some)
  have hhall : ∀ S : Finset V, S.card ≤  (S.biUnion t).card := by
    intro S
    by_cases hS : S.Nonempty
    · have hu : S.biUnion t = insert none ((S.biUnion (neighbors R)).image some) := by
        ext z
        cases z with
        | none =>
          simp only [Finset.mem_biUnion, t, Finset.mem_insert, true_or,
            and_true, exists_prop, Finset.mem_image, reduceCtorEq, and_false,
            exists_false, or_false]
          exact iff_true_intro hS
        | some y => simp [t, Finset.mem_biUnion]
      rw [hu, Finset.card_insert_of_notMem (by simp),
        Finset.card_image_of_injective _ (Option.some_injective V)]
      exact neighborhood_deficiency R ht S
    · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      simp [he]
  obtain ⟨f,hfi,hf⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hhall
  refine ⟨f,hfi,?_⟩
  intro x y hxy
  have hmem := hf x
  rw [hxy] at hmem
  simpa [t, neighbors, outNeighbors] using hmem

/-- A single coloring matches an outgoing arc from every vertex except
    possibly one. The matching argument also covers an empty tournament. -/
theorem exists_near_coloring (R : V → V → Prop)
    (ht : ∀ x y, x ≠ y → R x y ∨ R y x) (label : V → V → Bool) :
    ∃ (color : V → Bool) (bad : Finset V), bad.card ≤  1 ∧
      ∀ x, x ∉ bad → ∃ y, R x y ∧ label x y = color y := by
  obtain ⟨f,hfi,hf⟩ := exists_optional_matching R ht
  let color : V → Bool := fun y =>
    if h : ∃ x, f x = some y then label (Classical.choose h) y else false
  let bad : Finset V := univ.filter fun x => f x = none
  refine ⟨color,bad,?_,?_⟩
  · apply Finset.card_le_one.mpr
    intro x hx y hy
    exact hfi ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)
  · intro x hx
    cases hfx : f x with
    | none => exact False.elim (hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hfx⟩))
    | some y =>
      refine ⟨y,hf x y hfx,?_⟩
      have hex : ∃ z, f z = some y := ⟨x,hfx⟩
      have he : Classical.choose hex = x := hfi ((Classical.choose_spec hex).trans hfx.symm)
      simp only [color, dif_pos hex, he]







end
end GuardAugmentation







end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {V : Type} [Fintype.{0} V] [DecidableEq.{1} V] (R : V → V → Prop)
  (ht : ∀ (x y : V), @Ne.{1} V x y → Or (R x y) (R y x)) (label : V → V → Bool),
  @Exists.{1} (V → Bool) fun (color : V → Bool) =>
    @Exists.{1} (Finset.{0} V) fun (bad : Finset.{0} V) =>
      And
        (@LE.le.{0} Nat instLENat (@Finset.card.{0} V bad)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (∀ (x : V),
          Not
              (@Membership.mem.{0, 0} V (Finset.{0} V)
                (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) bad x) →
            @Exists.{1} V fun (y : V) => And (R x y) (@Eq.{1} Bool (label x y) (color y))) := @Sensitivity213981Formal.GuardAugmentation.exists_near_coloring
