-- Prove2me | solution 1 for Sensitivity213981Formal.Sensitivity10007BoolCaps.coherent_restrict
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:02:54.808717+00:00
-- url     : https://prove2.me/submissions/55e99f7d-039d-4a5e-b53b-2164884931a8

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











variable {V : Type} [Fintype V] [DecidableEq V]







theorem coherent_restrict (R : V → V → Prop) (ell : V × V → Fin 2)
    (A A' M : Finset V) (hA : A' ⊆ A) (color : V → Fin 2)
    (hg : ZL.Coherent R ell A M color) : ZL.Coherent R ell A' M color := by
  intro e he
  apply hg e
  rcases Finset.mem_union.mp he with hi | hc
  · obtain ⟨hp,hr⟩ := Finset.mem_filter.mp hi
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hp
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hA hx,hA hy⟩,hr⟩)
  · obtain ⟨hp,hr⟩ := Finset.mem_filter.mp hc
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hp
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hx,hA hy⟩,hr⟩)























end
end Sensitivity10007BoolCaps






end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {V : Type} [Fintype.{0} V] [inst : DecidableEq.{1} V] (R : V → V → Prop)
  (ell : Prod.{0, 0} V V → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (A A' M : Finset.{0} V)
  (hA :
    @LE.le.{0} (Finset.{0} V)
      (@Preorder.toLE.{0} (Finset.{0} V) (@PartialOrder.toPreorder.{0} (Finset.{0} V) (@Finset.instPartialOrder.{0} V)))
      A' A)
  (color : V → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (hg : @Sensitivity213981Formal.Sensitivity10007Labeling.ZL.Coherent.{0} V inst R ell A M color),
  @Sensitivity213981Formal.Sensitivity10007Labeling.ZL.Coherent.{0} V inst R ell A' M color := @Sensitivity213981Formal.Sensitivity10007BoolCaps.coherent_restrict
