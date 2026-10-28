-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.Tree.packedCheck_eq
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T21:02:38.177981+00:00
-- url     : https://prove2.me/submissions/4c17ee99-d63d-4192-9987-25247c6712ad

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankAnnotatedTree
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
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
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Prod.Lex
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Packed_packedCodeCheck_eq
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Records_staticKeyCode_staticEq


namespace Sensitivity213981Formal
section
/- Certified common-kind masks skip whole impossible record subtrees. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000
namespace ThreeBoundRankAnnotated
open ThreeBoundNumeric (Caps recordOfList)
open ThreeBoundRankNumeric ThreeBoundRankCached ThreeBoundFullProfile
open ThreeBoundEndpoint22Records

theorem and_true {a b : Bool} (h : (a && b)=true) : a=true ∧ b=true := by
  simpa only [Bool.and_eq_true] using h





































end ThreeBoundRankAnnotated


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ThreeBoundEndpoint22Packed
open ThreeBoundRankCached ThreeBoundRankAnnotated
open ThreeBoundEndpoint22Records



theorem Tree.packedCheck_eq (mask : Array Bool) (q : Fin 4) (values : CostValues)
    (bound : ℕ) (t : ThreeBoundRankAnnotated.Tree)
    (hs : t.checkStatics keyCodes.get keyCount=true) :
    Tree.packedCheck mask q.val values bound t=
      t.fusedCheck mask q.val (prepared keyCodes.get convertedValues q.val) values bound := by
  induction t with
  | leaf bits key code =>
      obtain ⟨_,he⟩:=and_true hs
      have hp:=staticKeyCode_staticEq code
      rw [of_decide_eq_true he] at hp
      have hext : codeRecord code 11=staticRow key 11:=hp.1 ⟨11,by decide⟩
      simp only [Tree.packedCheck,ThreeBoundRankAnnotated.Tree.fusedCheck,
        packedCodeCheck_eq q key values bound code hext]
  | branch bits pivot left right hl hr =>
      obtain ⟨hleft,hright⟩:=and_true hs
      simp only [Tree.packedCheck,ThreeBoundRankAnnotated.Tree.fusedCheck,hl hleft,hr hright]





end ThreeBoundEndpoint22Packed


end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ (mask : Array.{0} Bool) (q : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
  (values : Sensitivity213981Formal.ThreeBoundRankCached.CostValues) (bound : Nat)
  (t : Sensitivity213981Formal.ThreeBoundRankAnnotated.Tree)
  (hs :
    @Eq.{1} Bool
      (Sensitivity213981Formal.ThreeBoundRankAnnotated.Tree.checkStatics
        (Sensitivity213981Formal.ThreeBoundNumeric.NatTable.get
          Sensitivity213981Formal.ThreeBoundEndpoint22Records.keyCodes)
        Sensitivity213981Formal.ThreeBoundEndpoint22Records.keyCount t)
      Bool.true),
  @Eq.{1} Bool
    (Sensitivity213981Formal.ThreeBoundEndpoint22Packed.Tree.packedCheck mask
      (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q) values bound t)
    (Sensitivity213981Formal.ThreeBoundRankAnnotated.Tree.fusedCheck mask
      (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)
      (Sensitivity213981Formal.ThreeBoundRankAnnotated.prepared
        (Sensitivity213981Formal.ThreeBoundNumeric.NatTable.get
          Sensitivity213981Formal.ThreeBoundEndpoint22Records.keyCodes)
        Sensitivity213981Formal.ThreeBoundEndpoint22Records.convertedValues
        (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
      values bound t) := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.Tree.packedCheck_eq
