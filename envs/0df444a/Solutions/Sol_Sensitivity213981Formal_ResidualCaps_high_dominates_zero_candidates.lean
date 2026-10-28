-- Prove2me | solution 1 for Sensitivity213981Formal.ResidualCaps.high_dominates_zero_candidates
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T18:34:32.828237+00:00
-- url     : https://prove2.me/submissions/f12b9d7a-a730-4e38-b06d-0b86f9def279

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_ResidualCaps
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

























/-- A zero-budget target row cannot point to any high row. Thus every high
    row dominates the zero-budget negative target set. -/
theorem high_dominates_zero_candidates (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (guard : X → Prop) (children : V → Bool → X)
    (A H : Finset V) (hdis : Disjoint A H)
    (hhigh : ∀ w ∈ H, ∀ c : Bool, guard (children w c))
    (hzero : ∀ v ∈ A, (guardFailures R ell guard children v).card = 0) :
    ∀ v ∈ H, ∀ w ∈ A, R v w := by
  intro v hv w hw
  have hne : v ≠ w := by
    intro he
    subst w
    exact Finset.disjoint_left.mp hdis hw hv
  apply (hR.orient v w hne).mpr
  intro hwv
  have hmem : v ∈ guardFailures R ell guard children w :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hwv,hhigh v hv (ell w v)⟩
  have hpos := Finset.card_pos.mpr ⟨v,hmem⟩
  rw [hzero w hw] at hpos
  omega









end
end ResidualCaps







end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {V X : Type} [inst : Fintype.{0} V] [DecidableEq.{1} V] (R : V → V → Prop)
  (hR : @Sensitivity213981Formal.TournamentHighRows.IsTournament V R) (ell : V → V → Bool) (guard : X → Prop)
  (children : V → Bool → X) (A H : Finset.{0} V)
  (hdis : @Disjoint.{0} (Finset.{0} V) (@Finset.instPartialOrder.{0} V) (@Finset.instOrderBot.{0} V) A H)
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
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (v : V),
  @Membership.mem.{0, 0} V (Finset.{0} V) (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
      H v →
    ∀ (w : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) A w →
        R v w := @Sensitivity213981Formal.ResidualCaps.high_dominates_zero_candidates
