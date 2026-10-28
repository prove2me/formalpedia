-- Prove2me | solution 1 for Sensitivity213981Formal.Sensitivity10007BoolCaps.source_of_exclusion
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:07:30.811988+00:00
-- url     : https://prove2.me/submissions/01d48e03-2a19-4cfd-87f2-8d1d370664a6

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
import Theorems.Thm_Sensitivity213981Formal_Sensitivity10007BoolCaps_coherent_of_zero
import Theorems.Thm_Sensitivity213981Formal_Sensitivity10007BoolCaps_coherent_restrict


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









theorem source_of_exclusion (R : V → V → Prop) (ell : V × V → Fin 2) (a : ℕ)
    (hex : ∀ J : ZL.SourceIndex R a, ¬ (ZL.sourceFamily R a).bad J ell) :
    ResidualCaps.DominatorCardBound R (boolLabel ell) 1 a := by
  intro A M color _ hM hdom hz
  obtain ⟨s,rfl⟩ := Finset.card_eq_one.mp hM
  by_contra hn
  obtain ⟨A',hA',hcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt hn)
  have hsub : A' ⊆ ZL.outOn R Finset.univ s := by
    intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hdom s (Finset.mem_singleton_self _) w (hA' hw)⟩
  let J : ZL.SourceIndex R a := ⟨s,⟨A',Finset.mem_powersetCard.mpr ⟨hsub,hcard⟩⟩⟩
  apply hex J
  exact ⟨fun w => colorBit (color w),
    coherent_restrict R ell A A' {s} hA' _ (coherent_of_zero R ell A {s} color hz)⟩





















end
end Sensitivity10007BoolCaps






end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {V : Type} [inst : Fintype.{0} V] [inst_1 : DecidableEq.{1} V] (R : V → V → Prop)
  (ell : Prod.{0, 0} V V → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (a : Nat)
  (hex :
    ∀ (J : @Sensitivity213981Formal.Sensitivity10007Labeling.ZL.SourceIndex.{0} V inst R a),
      Not
        (@Sensitivity213981Formal.Sensitivity10007Labeling.ZL.SupportedFamily.bad.{0, 0} (Prod.{0, 0} V V)
          (@Sensitivity213981Formal.Sensitivity10007Labeling.ZL.SourceIndex.{0} V inst R a)
          (fun (a b : Prod.{0, 0} V V) => @instDecidableEqProd.{0, 0} V V inst_1 inst_1 a b)
          (@Sensitivity213981Formal.Sensitivity10007Labeling.ZL.sourceFamily.{0} V inst inst_1 R a) J ell)),
  @Sensitivity213981Formal.ResidualCaps.DominatorCardBound V inst_1 R
    (@Sensitivity213981Formal.Sensitivity10007BoolCaps.boolLabel V ell)
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) a := @Sensitivity213981Formal.Sensitivity10007BoolCaps.source_of_exclusion
