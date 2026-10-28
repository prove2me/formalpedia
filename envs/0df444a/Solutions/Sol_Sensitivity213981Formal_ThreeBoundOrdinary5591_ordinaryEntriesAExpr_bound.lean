-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundOrdinary5591.ordinaryEntriesAExpr_bound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:51:58.972429+00:00
-- url     : https://prove2.me/submissions/8941d771-6b5f-408c-8faf-632e53db444b

import Definitions.Def_Sensitivity213981Formal_MinmaxEntryMatch
import Definitions.Def_Sensitivity213981Formal_MinmaxPairM
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Ordinary5591Numeric
import Definitions.Def_Sensitivity213981Formal_StrictUnion
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditionalNumeric_parent_eq_ordinary_valid
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundOrdinary5591_ordinaryAExpr_bound


namespace Sensitivity213981Formal
section
/- The strict oriented-union estimate for actual graded min/max parents. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxTransfer
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional
open scoped Classical
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

theorem mm_same (F : L → (I → Bool) → Bool) (t : L) (x y : I → Bool) :
    mm F t t x y=(F t x && F t y) := by
  cases hx : F t x <;> cases hy : F t y <;> simp [mm,hx,hy]





end
end ThreeBoundMinmaxTransfer



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





theorem ordinary_spec (e : Entry) (he : e.ordinary=true) (d : ℕ) (hd : d ≤  e.tolerance) :
    e.lowerAt d=e.lowerAt 0 ∧ e.upperAt d=e.lowerAt 0 := by
  have hh := List.all_eq_true.mp he d (List.mem_range.mpr (by omega))
  simpa only [Bool.and_eq_true,beq_iff_eq] using hh









theorem matched_ordinary_weak (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
    (i j : Fin n) (P : ThreeBoundMinmaxTransfer.PairData S F i j) (a c : Entry)
    (hm : EntryMatch S F i j P a c) (ha : a.ordinary=true) :
    parent S F i=ordinaryParent S F (P.weakLower 0) (S.guard i) (S.tolerance i) := by
  apply ThreeBoundConditionalNumeric.parent_eq_ordinary_valid
  intro d hd u z
  obtain ⟨hl,hu⟩ := ordinary_spec a ha d (by simpa only [hm.weakTolerance] using hd)
  have hl' : P.weakLower d=P.weakLower 0 := Fin.ext (by rw [hm.weakLower d hd,hm.weakLower 0 (Nat.zero_le _)]; exact hl)
  have hu' : P.weakUpper d=P.weakLower 0 := Fin.ext (by rw [hm.weakUpper d hd,hm.weakLower 0 (Nat.zero_le _)]; exact hu)
  rw [P.weakDef,hl',hu',mm_same]

theorem matched_ordinary_strong (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
    (i j : Fin n) (P : ThreeBoundMinmaxTransfer.PairData S F i j) (a c : Entry)
    (hm : EntryMatch S F i j P a c) (hc : c.ordinary=true) :
    parent S F j=ordinaryParent S F (P.strongLower 0) (S.guard j) (S.tolerance j) := by
  apply ThreeBoundConditionalNumeric.parent_eq_ordinary_valid
  intro d hd u z
  obtain ⟨hl,hu⟩ := ordinary_spec c hc d (by simpa only [hm.strongTolerance] using hd)
  have hl' : P.strongLower d=P.strongLower 0 := Fin.ext (by rw [hm.strongLower d hd,hm.strongLower 0 (Nat.zero_le _)]; exact hl)
  have hu' : P.strongUpper d=P.strongLower 0 := Fin.ext (by rw [hm.strongUpper d hd,hm.strongLower 0 (Nat.zero_le _)]; exact hu)
  rw [P.strongDef,hl',hu',mm_same]





end
end ThreeBoundMinmaxNumeric




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Exact expression and actual Boolean semantics of the 5591 ordinary branch. -/


set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 50000
set_option linter.unusedSectionVars false

namespace ThreeBoundOrdinary5591
open _root_.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional ThreeBoundNumeric ThreeBoundFullProfile
open scoped Classical
noncomputable section
variable {n k : ℕ} {I : Type} [Fintype I]













/-- Exact actual min/max parents when both entries are ordinary. -/
theorem ordinaryEntriesAExpr_bound (S : Stage (Fin n) I (Fin k))
    (T : ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament k)
    (ell : Fin k → Fin k → Fin 2)
    (hAdj : ∀ v w, T.Adj v w ↔ S.Adj v w)
    (hLabel : ∀ v w, finTwoEquiv (ell v w)=S.label v w)
    (hCaps : LabelCaps T ell)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (recipe : Fin n → ThreeBoundMinmaxNumeric.Entry)
    (i j : Fin n) (P : ThreeBoundMinmaxTransfer.PairData S F i j)
    (hm : ThreeBoundMinmaxNumeric.EntryMatch S F i j P (recipe i) (recipe j))
    (hi : (recipe i).ordinary=true) (hj : (recipe j).ordinary=true)
    (hq4 : 4 ≤  (recipe j).tolerance) (hq8 : (recipe j).tolerance ≤  8)
    (v : Profile n) (hv : Upper F v) :
    ABound (parent S F) i j
      ((ordinaryAExpr n numericCaps ((recipe i).lowerAt 0) (recipe i).guard (recipe i).tolerance
        ((recipe j).lowerAt 0) (recipe j).guard (recipe j).tolerance).eval v) := by
  intro x hx
  rw [ThreeBoundMinmaxNumeric.matched_ordinary_weak S F i j P (recipe i) (recipe j) hm hi] at hx
  rw [ThreeBoundMinmaxNumeric.matched_ordinary_strong S F i j P (recipe i) (recipe j) hm hj]
  have hh := ordinaryAExpr_bound S T ell hAdj hLabel hCaps F hF
    (P.weakLower 0) (P.strongLower 0) (S.guard i) (S.guard j)
    (P.lowerOrder 0 (Nat.zero_le _)) P.guards (P.weakGuardTarget 0 (Nat.zero_le _))
    (S.tolerance i) (S.tolerance j) P.tolerances
    (by simpa only [hm.strongTolerance] using hq4)
    (by simpa only [hm.strongTolerance] using hq8) v hv x hx
  simpa only [hm.weakLower 0 (Nat.zero_le _),hm.strongLower 0 (Nat.zero_le _),
    hm.weakGuard,hm.strongGuard,hm.weakTolerance,hm.strongTolerance] using hh

end
end ThreeBoundOrdinary5591





end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {n k : Nat} {I : Type} [inst : Fintype.{0} I] (S : Sensitivity213981Formal.ThreeBoundWitness.Stage (Fin n) I (Fin k))
  (T : Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament k)
  (ell : Fin k → Fin k → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (hAdj :
    ∀ (v w : Fin k),
      Iff
        (@Digraph.Adj.{0} (Fin k)
          (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament.toDigraph k T) v w)
        (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj (Fin n) I (Fin k) S v w))
  (hLabel :
    ∀ (v w : Fin k),
      @Eq.{1} Bool
        (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Bool)
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Bool)
          (@EquivLike.toFunLike.{1, 1, 1}
            (Equiv.{1, 1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Bool)
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Bool
            (@Equiv.instEquivLike.{1, 1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Bool))
          finTwoEquiv (ell v w))
        (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label (Fin n) I (Fin k) S v w))
  (hCaps : @Sensitivity213981Formal.ThreeBoundOrdinary5591.LabelCaps k T ell) (F : Fin n → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested (Fin n) I
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) F)
  (recipe : Fin n → Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry) (i j : Fin n)
  (P :
    @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData (Fin n) I (Fin k)
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j)
  (hm : @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.EntryMatch n I (Fin k) S F i j P (recipe i) (recipe j))
  (hi : @Eq.{1} Bool (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.ordinary (recipe i)) Bool.true)
  (hj : @Eq.{1} Bool (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.ordinary (recipe j)) Bool.true)
  (hq4 :
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
      (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.tolerance (recipe j)))
  (hq8 :
    @LE.le.{0} Nat instLENat (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.tolerance (recipe j))
      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
  (v : Sensitivity213981Formal.ThreeBoundFullProfile.Profile n)
  (hv : @Sensitivity213981Formal.ThreeBoundFullProfile.Upper n I inst F v),
  @Sensitivity213981Formal.ThreeBoundProfiles.ABound (Fin n) (Prod.{0, 0} (Prod.{0, 0} (Fin k) Bool) I)
    (@instFintypeProd.{0, 0} (Prod.{0, 0} (Fin k) Bool) I
      (@instFintypeProd.{0, 0} (Fin k) Bool (Fin.fintype k) Bool.fintype) inst)
    (@Sensitivity213981Formal.ThreeBoundWitness.parent (Fin n) I (Fin k) (Fin.fintype k) S F) i j
    (@Sensitivity213981Formal.ThreeBoundNumeric.Expr.eval n v
      (Sensitivity213981Formal.ThreeBoundNumeric.ordinaryAExpr n
        Sensitivity213981Formal.ThreeBoundOrdinary5591.numericCaps
        (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.lowerAt (recipe i)
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.guard (recipe i))
        (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.tolerance (recipe i))
        (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.lowerAt (recipe j)
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.guard (recipe j))
        (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.tolerance (recipe j)))) := @Sensitivity213981Formal.ThreeBoundOrdinary5591.ordinaryEntriesAExpr_bound
