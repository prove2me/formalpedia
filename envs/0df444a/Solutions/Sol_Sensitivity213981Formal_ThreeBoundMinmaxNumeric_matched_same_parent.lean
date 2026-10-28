-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxNumeric.matched_same_parent
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:23:11.664865+00:00
-- url     : https://prove2.me/submissions/6feaa653-7beb-4e05-95d1-97ceb597c710

import Definitions.Def_Sensitivity213981Formal_MinmaxEntryMatch
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_WitnessLifting
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
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
Common block and positive-sensitivity witnesses for a broad two-child
guarded construction. These are lower-bound witnesses; no upper sensitivity
transfer theorem is asserted here.
-/


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ThreeBoundWitness
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320

variable {L I V : Type}









theorem parent_true_iff [Fintype V] (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (l : L)
    (x : ((V × Bool) × I) → Bool) :
    parent S F l x = true ↔ ∃ v : V,
      (failed S F l x v).card ≤  S.tolerance l ∧
      S.target l (failed S F l x v).card (child x v false) (child x v true) = true := by
  classical
  simp [parent]















































/- Reindexing lemmas follow the accepted Apache-2.0 source by @yousofy:
   Sol_Paley11987Verified_CompactFiniteProfile11987_actual_seeds_of_label_and_certificate,
   together with Definitions.Def_Paley11987Support_053. -/










end ThreeBoundWitness








end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- The exact link between finite numeric min/max entries and Boolean recipes. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxNumeric
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional ThreeBoundMinmaxTransfer ThreeBoundNumeric ThreeBoundFullProfile
open scoped Classical
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]









theorem same_spec (e f : Entry) (he : e.same f=true) :
    e.tolerance=f.tolerance ∧ e.guard=f.guard ∧
      ∀ d, d ≤  e.tolerance → e.lowerAt d=f.lowerAt d ∧ e.upperAt d=f.upperAt d := by
  simp only [Entry.same,Bool.decide_and,Bool.and_eq_true,decide_eq_true_eq] at he
  obtain ⟨hq,hg,ht⟩ := he
  refine ⟨hq,hg,?_⟩
  intro d hd
  have hh := List.all_eq_true.mp ht d (List.mem_range.mpr (by omega))
  simpa only [Bool.and_eq_true,beq_iff_eq] using hh









theorem matched_same_parent (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
    (i j : Fin n) (P : ThreeBoundMinmaxTransfer.PairData S F i j) (a c : Entry)
    (hm : EntryMatch S F i j P a c) (hs : a.same c=true) : parent S F i=parent S F j := by
  obtain ⟨hq,hg,ht⟩ := same_spec a c hs
  have hq' : S.tolerance i=S.tolerance j := by rw [hm.weakTolerance,hm.strongTolerance,hq]
  have hg' : S.guard i=S.guard j := Fin.ext (by rw [hm.weakGuard,hm.strongGuard,hg])
  have hlow (d : ℕ) (hd : d ≤  S.tolerance i) : P.weakLower d=P.strongLower d := by
    apply Fin.ext
    rw [hm.weakLower d hd,hm.strongLower d (by omega)]
    exact (ht d (by simpa only [hm.weakTolerance] using hd)).1
  have hupp (d : ℕ) (hd : d ≤  S.tolerance i) : P.weakUpper d=P.strongUpper d := by
    apply Fin.ext
    rw [hm.weakUpper d hd,hm.strongUpper d (by omega)]
    exact (ht d (by simpa only [hm.weakTolerance] using hd)).2
  funext x
  have hf (w : V) : failed S F i x w=failed S F j x w := by simp only [failed,hg']
  have he : parent S F i x=true ↔ parent S F j x=true := by
    rw [parent_true_iff,parent_true_iff]
    constructor
    · rintro ⟨w,hc,hh⟩
      refine ⟨w,by simpa only [← hf,← hq'] using hc,?_⟩
      rw [P.strongDef,← hf,← hlow _ hc,← hupp _ hc,← P.weakDef]
      exact hh
    · rintro ⟨w,hc,hh⟩
      have hc' : (failed S F i x w).card ≤  S.tolerance i := by simpa only [hf,hq'] using hc
      refine ⟨w,hc',?_⟩
      rw [P.weakDef,hlow _ hc',hupp _ hc',hf,← P.strongDef]
      exact hh
  cases h1 : parent S F i x <;> cases h2 : parent S F j x <;> simp_all



end
end ThreeBoundMinmaxNumeric




end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {n : Nat} {I V : Type} [Fintype.{0} I] [inst : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool) (i j : Fin n)
  (P :
    @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData (Fin n) I V
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j)
  (a c : Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry)
  (hm : @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.EntryMatch n I V S F i j P a c)
  (hs : @Eq.{1} Bool (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.same a c) Bool.true),
  @Eq.{1} ((x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) → Bool)
    (@Sensitivity213981Formal.ThreeBoundWitness.parent (Fin n) I V inst S F i)
    (@Sensitivity213981Formal.ThreeBoundWitness.parent (Fin n) I V inst S F j) := @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.matched_same_parent
