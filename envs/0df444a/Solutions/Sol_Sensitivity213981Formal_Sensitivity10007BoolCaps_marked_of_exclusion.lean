-- Prove2me | solution 1 for Sensitivity213981Formal.Sensitivity10007BoolCaps.marked_of_exclusion
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:01:37.264959+00:00
-- url     : https://prove2.me/submissions/04ac042d-b648-4c49-88d5-870af65ba2cb

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_SelectedBoolCaps
import Definitions.Def_Sensitivity213981Formal_Supplement_CandidateCoherence
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





section ActualGuards
variable [Fintype V]











end ActualGuards
end CandidateCoherence







end
end Sensitivity213981Formal

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

theorem bit_ne_iff (c : Fin 2) (b : Bool) : c ≠ colorBit b ↔ bit c ≠ b :=
  not_congr (bit_eq_iff c b)



variable {V : Type} [Fintype V] [DecidableEq V]

theorem mismatch_eq (R : V → V → Prop) (ell : V × V → Fin 2)
    (A : Finset V) (color : V → Bool) (v : V) :
    ZL.mismatch R ell A (fun w => colorBit (color w)) v =
      CandidateCoherence.mismatch R (boolLabel ell) A color v := by
  ext w
  change (w ∈ A.filter (fun z => R v z ∧ ell (v,z) ≠ colorBit (color z))) ↔
    (w ∈ A.filter (fun z => R v z ∧ bit (ell (v,z)) ≠ color z))
  simp only [Finset.mem_filter, bit_ne_iff]











theorem marked_restrict (R : V → V → Prop) (ell : V → V → Bool)
    (A A' M : Finset V) (hA : A' ⊆ A) (q B : ℕ) (color : V → Bool)
    (hg : ResidualCaps.MarkedGood R ell A M q B color) :
    ResidualCaps.MarkedGood R ell A' M q B color := by
  refine ⟨?_,?_,?_⟩
  · intro v hv
    exact (Nat.add_le_add_right (Finset.card_le_card
      (CandidateCoherence.mismatch_mono R ell A' A hA color v)) _).trans (hg.1 v (hA hv))
  · intro v hv
    exact (Nat.add_le_add_left (Finset.card_le_card
      (CandidateCoherence.mismatch_mono R ell A' A hA color v)) _).trans (hg.2.1 v hv)
  · exact (Finset.sum_le_sum fun v _ => Finset.card_le_card
      (CandidateCoherence.mismatch_mono R ell A' A hA color v)).trans hg.2.2

theorem marked_to_fin (R : V → V → Prop) (ell : V × V → Fin 2)
    (A M : Finset V) (q B : ℕ) (color : V → Bool)
    (hg : ResidualCaps.MarkedGood R (boolLabel ell) A M q B color) :
    ZL.MarkedGood R ell A M ∅ q B (fun w => colorBit (color w)) := by
  have ho (v : V) : ZL.outOn R M v = TournamentHighRows.outNeighbors R M v := rfl
  simpa [ZL.MarkedGood, ResidualCaps.MarkedGood, mismatch_eq, ho]
    using hg

theorem marked_of_exclusion (R : V → V → Prop) (ell : V × V → Fin 2) (q a m B : ℕ)
    (hex : ∀ J : ZL.MarkedIndex V a m, ¬ (ZL.markedFamily R q a m B).bad J ell) :
    ResidualCaps.MarkedCardBound R (boolLabel ell) q m B a := by
  intro A M color hdis hM hg
  by_contra hn
  obtain ⟨A',hA',hcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt hn)
  have hcompl : A' ⊆ Mᶜ := by
    intro v hv
    exact Finset.mem_compl.mpr (fun hm => Finset.disjoint_left.mp hdis (hA' hv) hm)
  let MI : (Finset.univ : Finset V).powersetCard m :=
    ⟨M,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hM⟩⟩
  let J : ZL.MarkedIndex V a m := ⟨MI,⟨A',Finset.mem_powersetCard.mpr ⟨hcompl,hcard⟩⟩⟩
  apply hex J
  exact ⟨fun w => colorBit (color w),marked_to_fin R ell A' M q B color
    (marked_restrict R (boolLabel ell) A A' M hA' q B color hg)⟩













end
end Sensitivity10007BoolCaps






end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {V : Type} [inst : Fintype.{0} V] [inst_1 : DecidableEq.{1} V] (R : V → V → Prop)
  (ell : Prod.{0, 0} V V → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (q a m B : Nat)
  (hex :
    ∀ (J : @Sensitivity213981Formal.Sensitivity10007Labeling.ZL.MarkedIndex.{0} V inst inst_1 a m),
      Not
        (@Sensitivity213981Formal.Sensitivity10007Labeling.ZL.SupportedFamily.bad.{0, 0} (Prod.{0, 0} V V)
          (@Sensitivity213981Formal.Sensitivity10007Labeling.ZL.MarkedIndex.{0} V inst inst_1 a m)
          (fun (a b : Prod.{0, 0} V V) => @instDecidableEqProd.{0, 0} V V inst_1 inst_1 a b)
          (@Sensitivity213981Formal.Sensitivity10007Labeling.ZL.markedFamily.{0} V inst inst_1 R q a m B) J ell)),
  @Sensitivity213981Formal.ResidualCaps.MarkedCardBound V R
    (@Sensitivity213981Formal.Sensitivity10007BoolCaps.boolLabel V ell) q m B a := @Sensitivity213981Formal.Sensitivity10007BoolCaps.marked_of_exclusion
