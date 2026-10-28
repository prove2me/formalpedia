-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Ordinary.ordinaryA_bound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:55:20.939386+00:00
-- url     : https://prove2.me/submissions/64ca30c6-9b0e-4da9-a924-388250d44da3

import Definitions.Def_Sensitivity213981Formal_Endpoint22PairData
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Ordinary5591Numeric
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundOrdinary5591_ordinaryEntriesAExpr_bound


namespace Sensitivity213981Formal
section
/- Concrete third-endpoint min/max pairing, independent of the chosen edge label. -/


set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
set_option linter.unusedSectionVars false

namespace ThreeBoundEndpoint22Pairs
open ThreeBoundWitness ThreeBoundProfiles ThreeBoundNesting
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxNumeric





variable {I : Type} [Fintype I]



theorem numeric_lower (p : Fin 4) (l : Fin 22) (d : ℕ)
    (hd : d ≤  (Sensitivity5591Endpoint22.entry p l).tolerance) :
    ((Sensitivity5591Endpoint22.entry p l).threshold d).val=
      (ThreeBoundMinmaxNumeric.Endpoint22.recipe p l).lowerAt d := by
  have hd9 : d< 9 := by have hh := Sensitivity5591Endpoint22.entry_tolerance_bound p l; omega
  simp [ThreeBoundMinmaxNumeric.Endpoint22.recipe,ThreeBoundMinmaxNumeric.Entry.lowerAt,Array.getD,hd9]

theorem numeric_upper (p : Fin 4) (l : Fin 22) (d : ℕ)
    (hd : d ≤  (Sensitivity5591Endpoint22.entry p l).tolerance) :
    ((Sensitivity5591Endpoint22.entry p l).upper d).val=
      (ThreeBoundMinmaxNumeric.Endpoint22.recipe p l).upperAt d := by
  have hd9 : d< 9 := by have hh := Sensitivity5591Endpoint22.entry_tolerance_bound p l; omega
  simp [ThreeBoundMinmaxNumeric.Endpoint22.recipe,ThreeBoundMinmaxNumeric.Entry.upperAt,Array.getD,hd9]

theorem entryMatch (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ w, ¬Adj w w)
    (label : Fin 5591 → Fin 5591 → Bool) (p : Fin 4) (F : Fin 22 → (I → Bool) → Bool)
    (i j : Fin 22) (hij : i ≤  j) :
    EntryMatch ((Sensitivity5591Endpoint22.recipe Adj loopless label p).stage F) F i j
      (pairData Adj loopless label p F i j hij) (ThreeBoundMinmaxNumeric.Endpoint22.recipe p i)
      (ThreeBoundMinmaxNumeric.Endpoint22.recipe p j) where
  weakTolerance := rfl
  strongTolerance := rfl
  weakGuard := rfl
  strongGuard := rfl
  weakLower := numeric_lower p i
  weakUpper := numeric_upper p i
  strongLower := numeric_lower p j
  strongUpper := numeric_upper p j

end ThreeBoundEndpoint22Pairs




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Every third-endpoint row of tolerance at least four is an actual ordinary
row.  This discharges the only ordinary fallback retained in that endpoint. -/


set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 200000
set_option linter.unusedSectionVars false

namespace ThreeBoundEndpoint22Ordinary
open _root_.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional ThreeBoundNumeric ThreeBoundFullProfile
open scoped Classical
noncomputable section

theorem large_ordinary : ∀ (p : Fin 4) (l : Fin 22),
    4 ≤  (ThreeBoundMinmaxNumeric.Endpoint22.recipe p l).tolerance →
    (ThreeBoundMinmaxNumeric.Endpoint22.recipe p l).ordinary=true := by decide +kernel

variable {I : Type} [Fintype I]

theorem ordinaryA_bound (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ w, ¬Adj w w)
    (label : Fin 5591 → Fin 5591 → Bool)
    (T : ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament 5591)
    (ell : Fin 5591 → Fin 5591 → Fin 2)
    (hAdj : ∀ v w, T.Adj v w ↔ Adj v w)
    (hLabel : ∀ v w, finTwoEquiv (ell v w)=label v w)
    (hCaps : ThreeBoundOrdinary5591.LabelCaps T ell)
    (p : Fin 4) (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
    (v : Profile 22) (hv : Upper F v) (i j : Fin 22) (hij : i ≤  j)
    (hq4 : 4 ≤  (ThreeBoundMinmaxNumeric.Endpoint22.recipe p j).tolerance) :
    ABound (parent ((Sensitivity5591Endpoint22.recipe Adj loopless label p).stage F) F) i j
      ((ordinaryAExpr 22 ThreeBoundOrdinary5591.numericCaps
        ((ThreeBoundMinmaxNumeric.Endpoint22.recipe p i).lowerAt 0)
        (ThreeBoundMinmaxNumeric.Endpoint22.recipe p i).guard
        (ThreeBoundMinmaxNumeric.Endpoint22.recipe p i).tolerance
        ((ThreeBoundMinmaxNumeric.Endpoint22.recipe p j).lowerAt 0)
        (ThreeBoundMinmaxNumeric.Endpoint22.recipe p j).guard
        (ThreeBoundMinmaxNumeric.Endpoint22.recipe p j).tolerance).eval v) := by
  let S := (Sensitivity5591Endpoint22.recipe Adj loopless label p).stage F
  let P := ThreeBoundEndpoint22Pairs.pairData Adj loopless label p F i j hij
  have hm := ThreeBoundEndpoint22Pairs.entryMatch Adj loopless label p F i j hij
  have hq4i : 4 ≤  (ThreeBoundMinmaxNumeric.Endpoint22.recipe p i).tolerance := by
    have hh := P.tolerances
    rw [hm.weakTolerance,hm.strongTolerance] at hh
    omega
  have hq8 : (ThreeBoundMinmaxNumeric.Endpoint22.recipe p j).tolerance ≤  8 :=
    Sensitivity5591Endpoint22.entry_tolerance_bound p j
  exact ThreeBoundOrdinary5591.ordinaryEntriesAExpr_bound S T ell hAdj hLabel hCaps F hF
    (ThreeBoundMinmaxNumeric.Endpoint22.recipe p) i j P hm
    (large_ordinary p i hq4i) (large_ordinary p j hq4) hq4 hq8 v hv

end
end ThreeBoundEndpoint22Ordinary




end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {I : Type} [inst : Fintype.{0} I]
  (Adj :
    Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591))) →
      Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591))) → Prop)
  (loopless : ∀ (w : Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591)))), Not (Adj w w))
  (label :
    Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591))) →
      Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591))) → Bool)
  (T :
    Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament
      (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591))))
  (ell :
    Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591))) →
      Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591))) →
        Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (hAdj :
    ∀ (v w : Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591)))),
      Iff
        (@Digraph.Adj.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591))))
          (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament.toDigraph
            (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591))) T)
          v w)
        (Adj v w))
  (hLabel :
    ∀ (v w : Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591)))),
      @Eq.{1} Bool
        (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Bool)
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Bool)
          (@EquivLike.toFunLike.{1, 1, 1}
            (Equiv.{1, 1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Bool)
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Bool
            (@Equiv.instEquivLike.{1, 1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Bool))
          finTwoEquiv (ell v w))
        (label v w))
  (hCaps :
    @Sensitivity213981Formal.ThreeBoundOrdinary5591.LabelCaps
      (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591))) T ell)
  (p : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
  (F : Fin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))) I
      (@PartialOrder.toPreorder.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
        (@Fin.instPartialOrder (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))))
      F)
  (v :
    Sensitivity213981Formal.ThreeBoundFullProfile.Profile
      (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
  (hv :
    @Sensitivity213981Formal.ThreeBoundFullProfile.Upper (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))
      I inst F v)
  (i j : Fin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
  (hij :
    @LE.le.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
      (@instLEFin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))) i j)
  (hq4 :
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
      (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.tolerance
        (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.recipe p j))),
  @Sensitivity213981Formal.ThreeBoundProfiles.ABound
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
    (Prod.{0, 0} (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591)))) Bool) I)
    (@instFintypeProd.{0, 0}
      (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591)))) Bool) I
      (@instFintypeProd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591)))) Bool
        (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591)))) Bool.fintype)
      inst)
    (@Sensitivity213981Formal.ThreeBoundWitness.parent
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))) I
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591))))
      (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591))))
      (@Sensitivity213981Formal.ThreeBoundWitness.MinMaxRecipe.stage
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))) I
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591))))
        (Sensitivity213981Formal.Sensitivity5591Endpoint22.recipe Adj loopless label p) F)
      F)
    i j
    (@Sensitivity213981Formal.ThreeBoundNumeric.Expr.eval
      (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) v
      (Sensitivity213981Formal.ThreeBoundNumeric.ordinaryAExpr
        (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))
        Sensitivity213981Formal.ThreeBoundOrdinary5591.numericCaps
        (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.lowerAt
          (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.recipe p i)
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.guard
          (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.recipe p i))
        (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.tolerance
          (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.recipe p i))
        (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.lowerAt
          (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.recipe p j)
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.guard
          (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.recipe p j))
        (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.tolerance
          (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.recipe p j)))) := @Sensitivity213981Formal.ThreeBoundEndpoint22Ordinary.ordinaryA_bound
