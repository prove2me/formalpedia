-- Prove2me | solution 1 for Sensitivity213981Formal.GuardAugmentation.target_plus_extra_high_cap
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T18:37:12.8152+00:00
-- url     : https://prove2.me/submissions/e9e53b5b-6f5f-4952-80ca-38ace3b10782

import Definitions.Def_Sensitivity213981Formal_GuardAugmentation
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_Supplement_CandidateCoherence
import Definitions.Def_Sensitivity213981Formal_TournamentHighRows
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
import Theorems.Thm_Sensitivity213981Formal_GuardAugmentation_augment_by_guards


namespace Sensitivity213981Formal
section
/-
Semantic high-row bounds for the graded q2/q3 transfer.

The finite high set is connected to actual guard failure sets: every arc to
a high head selects a guard-true child and therefore consumes a failure of
its tail. The tournament edge double count is proved here, not assumed.
-/


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace TournamentHighRows
open scoped Classical BigOperators

variable {V X : Type}

























section GuardSemantics
variable [Fintype V]



/-- Every edge into a high head consumes an actual failed guard. -/
theorem out_high_subset_failures (R : V → V → Prop) (ell : V → V → Bool)
    (P : X → Prop) (children : V → Bool → X) (H : Finset V)
    (hhigh : ∀ w ∈ H, ∀ c : Bool, P (children w c)) (v : V) :
    outNeighbors R H v ⊆ guardFailures R ell P children v := by
  classical
  intro w hw
  rcases Finset.mem_filter.mp hw with ⟨hwH,hvw⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, hvw, hhigh w hwH (ell v w)⟩











end GuardSemantics
end TournamentHighRows








end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/-
The graded-target to labeling-exclusion bridge.

Targets at different rows may use different lower thresholds. A geometric
one-child candidate has an accepted partner; coloring its row by the other
position makes every label mismatch an actual guard failure. This argument
is independent of fixed versus graded targets and applies to min/max targets.
-/


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace CandidateCoherence
open scoped Classical
open MinmaxLocal TournamentHighRows

variable {N : ℕ} {V X : Type}

















theorem mismatch_mono (R : V → V → Prop) (ell : V → V → Bool)
    (T U : Finset V) (hTU : T ⊆ U) (color : V → Bool) (v : V) :
    mismatch R ell T color v ⊆ mismatch R ell U color v := by
  classical
  intro w hw
  rcases Finset.mem_filter.mp hw with ⟨hwT,hw⟩
  exact Finset.mem_filter.mpr ⟨hTU hwT,hw⟩

theorem ordinaryGood_mono (R : V → V → Prop) (ell : V → V → Bool)
    (T U : Finset V) (hTU : T ⊆ U) (q : ℕ) (color : V → Bool)
    (hU : OrdinaryGood R ell U q color) : OrdinaryGood R ell T q color := by
  intro v hv
  exact (Finset.card_le_card (mismatch_mono R ell T U hTU color v)).trans (hU v (hTU hv))

theorem ordinary_card_lt (R : V → V → Prop) (ell : V → V → Bool)
    (q a : ℕ) (hexcl : NoOrdinary R ell q a)
    (T : Finset V) (color : V → Bool) (hT : OrdinaryGood R ell T q color) : T.card <  a := by
  classical
  by_contra hn
  have ha : a ≤  T.card := Nat.le_of_not_gt hn
  obtain ⟨U,hUT,hUa⟩ := Finset.exists_subset_card_eq ha
  exact hexcl U hUa color (ordinaryGood_mono R ell U T hUT q color hT)

section ActualGuards
variable [Fintype V]

/-- Each label mismatch enters the actual selected-child failure set. -/
theorem mismatch_subset_failures (R : V → V → Prop) (ell : V → V → Bool)
    (P : X → Prop) (children : V → Bool → X)
    (T : Finset V) (color : V → Bool)
    (hpartner : ∀ w ∈ T, ∀ b : Bool, b ≠ color w → P (children w b)) (v : V) :
    mismatch R ell T color v ⊆ guardFailures R ell P children v := by
  classical
  intro w hw
  rcases Finset.mem_filter.mp hw with ⟨hwT,hvw,hlabel⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ w,hvw,hpartner w hwT (ell v w) hlabel⟩









end ActualGuards
end CandidateCoherence







end
end Sensitivity213981Formal

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











/-- Every abstract augmentation charge is an actual guard failure. The
    disjointness of candidates and high rows prevents double-counting. -/
theorem charges_card_le_actual_failures (R : V → V → Prop)
    (ell : V → V → Bool) (P : X → Prop) (children : V → Bool → X)
    (C G : Finset V) (hdis : Disjoint C G) (base : V → Bool)
    (hpartner : ∀ w ∈ C, ∀ b : Bool, b ≠ base w → P (children w b))
    (hhigh : ∀ w ∈ G, ∀ b : Bool, P (children w b)) (v : V) :
    (mismatch R ell C base v).card + (outNeighbors R G v).card ≤ 
      (guardFailures R ell P children v).card := by
  have hd : Disjoint (mismatch R ell C base v) (outNeighbors R G v) := by
    apply Finset.disjoint_left.mpr
    intro w hwC hwG
    exact Finset.disjoint_left.mp hdis
      (Finset.mem_filter.mp hwC).1 (Finset.mem_filter.mp hwG).1
  rw [← Finset.card_union_of_disjoint hd]
  apply Finset.card_le_card
  apply Finset.union_subset
  · exact mismatch_subset_failures R ell P children C base hpartner v
  · exact out_high_subset_failures R ell P children G hhigh v

/-- The second strengthened prefix cap: target candidates with budget q
    and disjoint high rows with budget q+1 have total size at most the
    exact ordinary-exclusion cutoff. -/
theorem target_plus_extra_high_cap (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (P : X → Prop) (children : V → Bool → X)
    (C G : Finset V) (hdis : Disjoint C G) (q a : ℕ)
    (hexcl : NoOrdinary R ell q a) (base : V → Bool)
    (hpartner : ∀ w ∈ C, ∀ b : Bool, b ≠ base w → P (children w b))
    (hhigh : ∀ w ∈ G, ∀ b : Bool, P (children w b))
    (hC : ∀ v ∈ C, (guardFailures R ell P children v).card ≤  q)
    (hG : ∀ v ∈ G, (guardFailures R ell P children v).card ≤  q+1) :
    C.card + G.card ≤  a := by
  have ht : ∀ x y, x ≠ y → R x y ∨ R y x := by
    intro x y hxy
    by_cases h : R x y
    · exact Or.inl h
    · exact Or.inr (by by_contra hn; exact h ((hR.orient x y hxy).mpr hn))
  have hb (v : V) := charges_card_le_actual_failures R ell P children C G hdis base
    hpartner hhigh v
  obtain ⟨S,color,hsize,hgood⟩ := augment_by_guards R ht ell C G hdis q base
    (fun v hv => (hb v).trans (hC v hv))
    (fun v hv => (hb v).trans (hG v hv))
  have hS := ordinary_card_lt R ell q a hexcl S color hgood
  omega

end
end GuardAugmentation







end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {V X : Type} [inst : Fintype.{0} V] [DecidableEq.{1} V] (R : V → V → Prop)
  (hR : @Sensitivity213981Formal.TournamentHighRows.IsTournament V R) (ell : V → V → Bool) (P : X → Prop)
  (children : V → Bool → X) (C G : Finset.{0} V)
  (hdis : @Disjoint.{0} (Finset.{0} V) (@Finset.instPartialOrder.{0} V) (@Finset.instOrderBot.{0} V) C G) (q a : Nat)
  (hexcl : @Sensitivity213981Formal.CandidateCoherence.NoOrdinary V R ell q a) (base : V → Bool)
  (hpartner :
    ∀ (w : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) C w →
        ∀ (b : Bool), @Ne.{1} Bool b (base w) → P (children w b))
  (hhigh :
    ∀ (w : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) G w →
        ∀ (b : Bool), P (children w b))
  (hC :
    ∀ (v : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) C v →
        @LE.le.{0} Nat instLENat
          (@Finset.card.{0} V (@Sensitivity213981Formal.TournamentHighRows.guardFailures V X inst R ell P children v))
          q)
  (hG :
    ∀ (v : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) G v →
        @LE.le.{0} Nat instLENat
          (@Finset.card.{0} V (@Sensitivity213981Formal.TournamentHighRows.guardFailures V X inst R ell P children v))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
  @LE.le.{0} Nat instLENat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Finset.card.{0} V C) (@Finset.card.{0} V G)) a := @Sensitivity213981Formal.GuardAugmentation.target_plus_extra_high_cap
