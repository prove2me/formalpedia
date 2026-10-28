-- Prove2me | solution 1 for Sensitivity213981Formal.GuardAugmentation.augment_by_guards
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T18:31:51.149449+00:00
-- url     : https://prove2.me/submissions/40f4a810-753e-45d8-93e0-0a936f2c67b6

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
import Theorems.Thm_Sensitivity213981Formal_GuardAugmentation_exists_near_coloring


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









/-- Rows with one extra guard failure can be adjoined while losing at most
    one row; no target-threshold equality is used. -/
theorem augment_by_guards (R : V → V → Prop)
    (ht : ∀ x y, x ≠ y → R x y ∨ R y x)
    (ell : V → V → Bool) (C G : Finset V) (hdis : Disjoint C G)
    (q : ℕ) (base : V → Bool)
    (hC : ∀ i ∈ C, (mismatch R ell C base i).card + (outNeighbors R G i).card ≤  q)
    (hG : ∀ i ∈ G, (mismatch R ell C base i).card + (outNeighbors R G i).card ≤  q+1) :
    ∃ (S : Finset V) (color : V → Bool),
      C.card + G.card ≤  S.card + 1 ∧ OrdinaryGood R ell S q color := by
  let RG : G → G → Prop := fun i j => R i.1 j.1
  have hTG : ∀ i j : G, i ≠ j → RG i j ∨ RG j i := by
    intro i j hij
    exact ht i.1 j.1 (fun he => hij (Subtype.ext he))
  obtain ⟨colG,bad,hbad,hcover⟩ :=
    exists_near_coloring RG hTG (fun i j => ell i.1 j.1)
  let B : Finset V := bad.image Subtype.val
  have hBG : B ⊆ G := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact y.2
  have hBcard : B.card ≤  1 := (Finset.card_image_le).trans hbad
  let K := G \ B
  let S := C ∪ K
  let color : V → Bool := fun x => if hx : x ∈ G then colG ⟨x,hx⟩ else base x
  have hcolorC (x : V) (hx : x ∈ C) : color x = base x := by
    have hnot : x ∉ G := fun hg => Finset.disjoint_left.mp hdis hx hg
    simp only [color,dif_neg hnot]
  have hmatch (i : V) (hi : i ∈ K) :
      ∃ j ∈ G, R i j ∧ ell i j = color j := by
    obtain ⟨hiG,hiB⟩ := Finset.mem_sdiff.mp hi
    have hin : (⟨i,hiG⟩ : G) ∉ bad := by
      intro hb
      exact hiB (Finset.mem_image.mpr ⟨⟨i,hiG⟩,hb,rfl⟩)
    obtain ⟨j,hij,hcol⟩ := hcover ⟨i,hiG⟩ hin
    refine ⟨j.1,j.2,hij,?_⟩
    simpa only [color,dif_pos j.2] using hcol
  let charges (i : V) := mismatch R ell C base i ∪ outNeighbors R G i
  have hchargecard (i : V) : (charges i).card =
      (mismatch R ell C base i).card + (outNeighbors R G i).card := by
    apply Finset.card_union_of_disjoint
    apply Finset.disjoint_left.mpr
    intro j hj hk
    exact Finset.disjoint_left.mp hdis
      (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hk).1
  have hsub (i : V) : mismatch R ell S color i ⊆ charges i := by
    intro j hj
    obtain ⟨hjS,hij,hne⟩ := Finset.mem_filter.mp hj
    rcases Finset.mem_union.mp hjS with hjC | hjK
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨hjC,hij,by simpa only [hcolorC j hjC] using hne⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨(Finset.mem_sdiff.mp hjK).1,hij⟩)
  refine ⟨S,color,?_,?_⟩
  · have hdCK : Disjoint C K := by
      apply Finset.disjoint_left.mpr
      intro i hi hk
      exact Finset.disjoint_left.mp hdis hi (Finset.mem_sdiff.mp hk).1
    have hs : S.card = C.card + K.card := Finset.card_union_of_disjoint hdCK
    have hg : K.card + B.card = G.card := Finset.card_sdiff_add_card_eq_card hBG
    omega
  · intro i hi
    rcases Finset.mem_union.mp hi with hiC | hiK
    · have hh := hC i hiC
      rw [← hchargecard i] at hh
      exact (Finset.card_le_card (hsub i)).trans hh
    · obtain ⟨j,hjG,hij,hcol⟩ := hmatch i hiK
      have hjcharges : j ∈ charges i := Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hjG,hij⟩)
      have hjnot : j ∉ mismatch R ell S color i := by
        intro hj
        exact (Finset.mem_filter.mp hj).2.2 hcol
      have herase : mismatch R ell S color i ⊆ (charges i).erase j := by
        intro y hy
        exact Finset.mem_erase.mpr ⟨fun he => hjnot (he ▸ hy),hsub i hy⟩
      have hh := hG i (Finset.mem_sdiff.mp hiK).1
      have hc := Finset.card_le_card herase
      rw [Finset.card_erase_of_mem hjcharges,hchargecard i] at hc
      omega





end
end GuardAugmentation







end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {V : Type} [Fintype.{0} V] [DecidableEq.{1} V] (R : V → V → Prop)
  (ht : ∀ (x y : V), @Ne.{1} V x y → Or (R x y) (R y x)) (ell : V → V → Bool) (C G : Finset.{0} V)
  (hdis : @Disjoint.{0} (Finset.{0} V) (@Finset.instPartialOrder.{0} V) (@Finset.instOrderBot.{0} V) C G) (q : Nat)
  (base : V → Bool)
  (hC :
    ∀ (i : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) C i →
        @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@Finset.card.{0} V (@Sensitivity213981Formal.CandidateCoherence.mismatch V R ell C base i))
            (@Finset.card.{0} V (@Sensitivity213981Formal.TournamentHighRows.outNeighbors V R G i)))
          q)
  (hG :
    ∀ (i : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) G i →
        @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@Finset.card.{0} V (@Sensitivity213981Formal.CandidateCoherence.mismatch V R ell C base i))
            (@Finset.card.{0} V (@Sensitivity213981Formal.TournamentHighRows.outNeighbors V R G i)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
  @Exists.{1} (Finset.{0} V) fun (S : Finset.{0} V) =>
    @Exists.{1} (V → Bool) fun (color : V → Bool) =>
      And
        (@LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Finset.card.{0} V C)
            (@Finset.card.{0} V G))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Finset.card.{0} V S)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@Sensitivity213981Formal.CandidateCoherence.OrdinaryGood V R ell S q color) := @Sensitivity213981Formal.GuardAugmentation.augment_by_guards
