-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundRankMarkers.dominator_mismatch_cap
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T18:38:32.600268+00:00
-- url     : https://prove2.me/submissions/8a216c64-554b-4cac-bf01-8615c75c74ed

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_ResidualCaps
import Definitions.Def_Sensitivity213981Formal_Supplement_CandidateCoherence
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Sensitivity213981Formal_ResidualCaps_high_dominates_zero_candidates


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

/-- Actual guard budgets imply ordinary coherence for any partner-valid coloring. -/
theorem ordinaryGood_of_actual_guards (R : V → V → Prop) (ell : V → V → Bool)
    (P : X → Prop) (children : V → Bool → X)
    (T : Finset V) (q : ℕ) (color : V → Bool)
    (hpartner : ∀ w ∈ T, ∀ b : Bool, b ≠ color w → P (children w b))
    (hbudget : ∀ v ∈ T, (guardFailures R ell P children v).card ≤  q) :
    OrdinaryGood R ell T q color := by
  intro v hv
  exact (Finset.card_le_card (mismatch_subset_failures R ell P children T color hpartner v)).trans
    (hbudget v hv)







end ActualGuards
end CandidateCoherence







end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/-
Source, double-dominator, and zero-mismatch residual caps for actual graded
target candidates. The residuals are actual failed guards left after all arcs
inside the full high-row tournament have been charged.
-/


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ResidualCaps
open scoped Classical BigOperators
open Finset TournamentHighRows CandidateCoherence GuardAugmentation
noncomputable section

variable {V X : Type} [Fintype V] [DecidableEq V]















theorem deletedHeads_subset (R : V → V → Prop) (ell : V → V → Bool)
    (A M : Finset V) (color : V → Bool) : deletedHeads R ell A M color ⊆ A := by
  intro w hw
  obtain ⟨v,_,hv⟩ := Finset.mem_biUnion.mp hw
  exact (Finset.mem_filter.mp hv).1

theorem cleanedHeads_subset (R : V → V → Prop) (ell : V → V → Bool)
    (A M : Finset V) (color : V → Bool) : cleanedHeads R ell A M color ⊆ A :=
  Finset.sdiff_subset

theorem cleaned_plus_deleted (R : V → V → Prop) (ell : V → V → Bool)
    (A M : Finset V) (color : V → Bool) :
    (cleanedHeads R ell A M color).card + (deletedHeads R ell A M color).card = A.card :=
  Finset.card_sdiff_add_card_eq_card (deletedHeads_subset R ell A M color)

theorem marker_clean_mismatch_empty (R : V → V → Prop) (ell : V → V → Bool)
    (A M : Finset V) (color : V → Bool) (v : V) (hv : v ∈ M) :
    mismatch R ell (cleanedHeads R ell A M color) color v = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  obtain ⟨hwC,hvw,hcolor⟩ := Finset.mem_filter.mp hw
  obtain ⟨hwA,hwD⟩ := Finset.mem_sdiff.mp hwC
  exact hwD (Finset.mem_biUnion.mpr
    ⟨v,hv,Finset.mem_filter.mpr ⟨hwA,hvw,hcolor⟩⟩)













end
end ResidualCaps







end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Marker deletion caps using the actual mismatches into the target set.
The marker budget is proved from their true guard counts, so the q3
six- and seven-marker refinements require no false size restriction. -/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

namespace ThreeBoundRankMarkers
open scoped Classical BigOperators
open Finset TournamentHighRows CandidateCoherence GuardAugmentation ResidualCaps
noncomputable section
variable {V X : Type} [Fintype V] [DecidableEq V]

theorem dominator_mismatch_cap (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (guard : X → Prop) (children : V → Bool → X)
    (A H M : Finset V) (hdis : Disjoint A H) (hMH : M ⊆ H)
    (color : V → Bool) (m a : ℕ) (hM : M.card = m)
    (hcap : DominatorCardBound R ell m a)
    (hpartner : ∀ w ∈ A, ∀ c : Bool, c ≠ color w → guard (children w c))
    (hhigh : ∀ w ∈ H, ∀ c : Bool, guard (children w c))
    (hzero : ∀ v ∈ A, (guardFailures R ell guard children v).card = 0) :
    A.card ≤  a-1 + ∑ v ∈ M, (mismatch R ell A color v).card := by
  let C := cleanedHeads R ell A M color
  have hCA : C ⊆ A := cleanedHeads_subset R ell A M color
  have hdisCM : Disjoint C M := hdis.mono hCA hMH
  have hdom := high_dominates_zero_candidates R hR ell guard children A H hdis hhigh hzero
  have hgoodA : OrdinaryGood R ell A 0 color := by
    apply ordinaryGood_of_actual_guards R ell guard children A 0 color hpartner
    intro v hv
    exact le_of_eq (hzero v hv)
  have hgoodC : OrdinaryGood R ell C 0 color := ordinaryGood_mono R ell C A hCA 0 color hgoodA
  have hcoherent : ∀ v ∈ C ∪ M, (mismatch R ell C color v).card = 0 := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvC | hvM
    · exact Nat.eq_zero_of_le_zero (hgoodC v hvC)
    · rw [marker_clean_mismatch_empty R ell A M color v hvM]
      rfl
  have hC := hcap C M color hdisCM hM
    (fun v hv w hw => hdom v (hMH hv) w (hCA hw)) hcoherent
  have hsum : (deletedHeads R ell A M color).card ≤  ∑ v ∈ M, (mismatch R ell A color v).card := Finset.card_biUnion_le
  have htotal := cleaned_plus_deleted R ell A M color
  change C.card + (deletedHeads R ell A M color).card = A.card at htotal
  omega







end
end ThreeBoundRankMarkers




end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {V X : Type} [inst : Fintype.{0} V] [inst_1 : DecidableEq.{1} V] (R : V → V → Prop)
  (hR : @Sensitivity213981Formal.TournamentHighRows.IsTournament V R) (ell : V → V → Bool) (guard : X → Prop)
  (children : V → Bool → X) (A H M : Finset.{0} V)
  (hdis : @Disjoint.{0} (Finset.{0} V) (@Finset.instPartialOrder.{0} V) (@Finset.instOrderBot.{0} V) A H)
  (hMH :
    @LE.le.{0} (Finset.{0} V)
      (@Preorder.toLE.{0} (Finset.{0} V) (@PartialOrder.toPreorder.{0} (Finset.{0} V) (@Finset.instPartialOrder.{0} V)))
      M H)
  (color : V → Bool) (m a : Nat) (hM : @Eq.{1} Nat (@Finset.card.{0} V M) m)
  (hcap : @Sensitivity213981Formal.ResidualCaps.DominatorCardBound V inst_1 R ell m a)
  (hpartner :
    ∀ (w : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) A w →
        ∀ (c : Bool), @Ne.{1} Bool c (color w) → guard (children w c))
  (hhigh :
    ∀ (w : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H w →
        ∀ (c : Bool), guard (children w c))
  (hzero :
    ∀ (v : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) A v →
        @Eq.{1} Nat
          (@Finset.card.{0} V
            (@Sensitivity213981Formal.TournamentHighRows.guardFailures V X inst R ell guard children v))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))),
  @LE.le.{0} Nat instLENat (@Finset.card.{0} V A)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) a
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@Finset.sum.{0, 0} V Nat Nat.instAddCommMonoid M fun (v : V) =>
        @Finset.card.{0} V (@Sensitivity213981Formal.CandidateCoherence.mismatch V R ell A color v))) := @Sensitivity213981Formal.ThreeBoundRankMarkers.dominator_mismatch_cap
