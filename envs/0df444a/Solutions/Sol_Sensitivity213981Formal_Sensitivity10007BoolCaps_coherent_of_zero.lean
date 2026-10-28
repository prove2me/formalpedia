-- Prove2me | solution 1 for Sensitivity213981Formal.Sensitivity10007BoolCaps.coherent_of_zero
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:02:23.666902+00:00
-- url     : https://prove2.me/submissions/42ec1c44-e384-4a4c-a040-214f8633922a

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_SelectedBoolCaps
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto


namespace Sensitivity213981Formal
section
/- The actual Paley-10007 label satisfies the Bool-valued exclusion interfaces
used by the graded-candidate and residual-cap proofs. -/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

namespace Sensitivity10007BoolCaps
open Sensitivity10007Labeling
open scoped Classical BigOperators
noncomputable section





theorem bit_eq_iff (c : Fin 2) (b : Bool) : c = colorBit b ↔ bit c = b := by
  fin_cases c <;> cases b <;> decide





variable {V : Type} [Fintype V] [DecidableEq V]





theorem coherent_of_zero (R : V → V → Prop) (ell : V × V → Fin 2)
    (A M : Finset V) (color : V → Bool)
    (hz : ∀ v ∈ A ∪ M,
      (CandidateCoherence.mismatch R (boolLabel ell) A color v).card = 0) :
    ZL.Coherent R ell A M (fun w => colorBit (color w)) := by
  intro e he
  have hh : e.1 ∈ A ∪ M ∧ e.2 ∈ A ∧ R e.1 e.2 := by
    rcases Finset.mem_union.mp he with hi | hc
    · obtain ⟨hp,hr⟩ := Finset.mem_filter.mp hi
      obtain ⟨hx,hy⟩ := Finset.mem_product.mp hp
      exact ⟨Finset.mem_union_left _ hx,hy,hr⟩
    · obtain ⟨hp,hr⟩ := Finset.mem_filter.mp hc
      obtain ⟨hx,hy⟩ := Finset.mem_product.mp hp
      exact ⟨Finset.mem_union_right _ hx,hy,hr⟩
  apply (bit_eq_iff _ _).mpr
  by_contra hn
  have hm : e.2 ∈ CandidateCoherence.mismatch R (boolLabel ell) A color e.1 :=
    Finset.mem_filter.mpr ⟨hh.2.1,hh.2.2,hn⟩
  have hp := Finset.card_pos.mpr ⟨e.2,hm⟩
  rw [hz e.1 hh.1] at hp
  omega

























end
end Sensitivity10007BoolCaps






end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {V : Type} [Fintype.{0} V] [inst : DecidableEq.{1} V] (R : V → V → Prop)
  (ell : Prod.{0, 0} V V → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (A M : Finset.{0} V)
  (color : V → Bool)
  (hz :
    ∀ (v : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
          (@Union.union.{0} (Finset.{0} V) (@Finset.instUnion.{0} V inst) A M) v →
        @Eq.{1} Nat
          (@Finset.card.{0} V
            (@Sensitivity213981Formal.CandidateCoherence.mismatch V R
              (@Sensitivity213981Formal.Sensitivity10007BoolCaps.boolLabel V ell) A color v))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))),
  @Sensitivity213981Formal.Sensitivity10007Labeling.ZL.Coherent.{0} V inst R ell A M fun (w : V) =>
    Sensitivity213981Formal.Sensitivity10007BoolCaps.colorBit (color w) := @Sensitivity213981Formal.Sensitivity10007BoolCaps.coherent_of_zero
