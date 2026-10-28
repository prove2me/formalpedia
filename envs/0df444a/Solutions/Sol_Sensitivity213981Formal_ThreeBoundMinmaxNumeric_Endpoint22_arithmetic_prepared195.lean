-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.arithmetic_prepared195
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T23:54:08.914044+00:00
-- url     : https://prove2.me/submissions/d9794501-85ac-411d-b8bd-04db880ddd12

import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData
import Definitions.Def_Sensitivity213981Formal_Endpoint22DenyData
import Definitions.Def_Sensitivity213981Formal_Endpoint22EnvelopeData
import Definitions.Def_Sensitivity213981Formal_Endpoint22FastTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22StrictPacked
import Definitions.Def_Sensitivity213981Formal_Endpoint22StrictTree
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankBlockedBits
import Definitions.Def_Sensitivity213981Formal_RankFusedTree
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Packed_Tree_packedCheck_eq
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Records_annotated_statics_checked
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankAnnotated_fusedCodePreparedCheck_eq


namespace Sensitivity213981Formal
section
/- A single bit intersection implements the finite common-kind rejection test. -/

set_option autoImplicit false
namespace ThreeBoundRankAnnotated

theorem and_single_bit (n i : ℕ) : n &&& 2^i=(n.testBit i).toNat*2^i := by
  apply Nat.eq_of_testBit_eq
  intro j
  obtain rfl | hij := Decidable.eq_or_ne i j <;> cases h : n.testBit i
  · simp [h]
  · simp [h]
  · simp [Nat.testBit_two_pow_of_ne hij]
  · simp [Nat.testBit_two_pow_of_ne hij]



theorem deniedFrom_check (mask : Array Bool) (ks : List (Fin 11)) (bits : ℕ) :
    decide (bits &&& deniedFrom mask ks≠0)=
      ks.any (fun k => bits.testBit (4*k.val) && !(mask.getD k.val false)) := by
  induction ks with
  | nil => simp only [deniedFrom,Nat.and_zero,ne_self_iff_false,decide_false,List.any_nil]
  | cons k ks ih =>
      simp only [deniedFrom,List.any_cons,Nat.and_or_distrib_left]
      cases hm : mask.getD k.val false with
      | true =>
          simpa only [hm,if_true,Nat.and_zero,Nat.zero_or,Bool.not_true,Bool.and_false,Bool.false_or] using ih
      | false =>
          simp only [hm,Bool.false_eq_true,if_false,Bool.not_false,Bool.and_true]
          cases hb : bits.testBit (4*k.val) with
          | false =>
              simpa only [and_single_bit,hb,Bool.toNat_false,Nat.zero_mul,Nat.zero_or,Bool.false_or] using ih
          | true =>
              simp only [and_single_bit,hb,Bool.toNat_true,Nat.one_mul,Bool.true_or]
              apply decide_eq_true
              intro hz
              have hp := (Nat.or_eq_zero_iff.mp hz).1
              exact (pow_ne_zero _ (by decide : (2:ℕ)≠0)) hp





theorem blockedFast_eq (mask : Array Bool) (deny bits : ℕ) (h : deny=denied mask) :
    blockedFast deny bits=blocked mask bits := by
  subst deny
  exact deniedFrom_check mask (List.finRange 11) bits

end ThreeBoundRankAnnotated


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundRankAnnotated

























































































































































































































































theorem denied_checked195 : deny195=denied mask195:=by decide +kernel


end ThreeBoundMinmaxNumeric.Endpoint22

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
namespace ThreeBoundRankAnnotated
open ThreeBoundRankCached



theorem Tree.fusedCheck_eq (mask : Array Bool) (q : ℕ) (pre : ℕ → PreparedValues)
    (values : CostValues) (bound : ℕ) (t : Tree) :
    t.fusedCheck mask q pre values bound=t.preparedCheck mask q pre values bound := by
  induction t with
  | leaf bits key code => simp only [Tree.fusedCheck,Tree.preparedCheck,fusedCodePreparedCheck_eq]
  | branch bits pivot left right hl hr => simp only [Tree.fusedCheck,Tree.preparedCheck,hl,hr]





end ThreeBoundRankAnnotated


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ThreeBoundEndpoint22Packed
open ThreeBoundRankCached ThreeBoundRankAnnotated



theorem Tree.fastCheck_eq (mask : Array Bool) (deny : ℕ) (hd : deny=denied mask)
    (q : ℕ) (values : CostValues) (bound : ℕ) (t : ThreeBoundRankAnnotated.Tree) :
    Tree.fastCheck deny q values bound t=Tree.packedCheck mask q values bound t := by
  induction t with
  | leaf bits key code => simp only [Tree.fastCheck,Tree.packedCheck,blockedFast_eq mask deny _ hd]
  | branch bits pivot left right hl hr =>
      simp only [Tree.fastCheck,Tree.packedCheck,blockedFast_eq mask deny _ hd,hl,hr]





end ThreeBoundEndpoint22Packed


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Exact eager evaluation of the packed scalar arithmetic. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ThreeBoundEndpoint22Strict
open ThreeBoundNumeric (maximum)
open ThreeBoundRankCached ThreeBoundEndpoint22Packed ThreeBoundEndpoint22Records



theorem withNat_eq {α : Sort _} (n : ℕ) (f : ℕ → α) : withNat n f=f n := by
  cases n <;> rfl



theorem fastDigit_eq (code k : ℕ) : fastDigit code k=(code/(16^k))%16 := by
  unfold fastDigit
  rw [Nat.shiftRight_eq_div_pow,show (15:ℕ)=2^4-1 from rfl,Nat.and_two_pow_sub_one_eq_mod]
  have hp : (16:ℕ)^k=2^(4*k) := by
    rw [show (16:ℕ)=2^4 from rfl,← pow_mul]
  rw [← hp]



theorem fastRecord_eq (code : ℕ) : fastRecord code=codeRecord code := by
  funext k
  simp only [fastRecord,codeRecord,decodeDigit,fastDigit_eq]



theorem fastCap_eq (code e k : ℕ) : fastCap code e k=packedCap code e k := by
  unfold fastCap packedCap
  rw [Nat.shiftRight_eq_div_pow,show (63:ℕ)=2^6-1 from rfl,Nat.and_two_pow_sub_one_eq_mod]
  have hp : (64:ℕ)^(4*e+k)=2^(6*(4*e+k)) := by
    rw [show (64:ℕ)=2^6 from rfl,← pow_mul]
  rw [← hp]



theorem strictNegativeCost_eq (q code e : ℕ) (values : CostValues) :
    strictNegativeCost q code e values=packedNegativeCost q code e values := by
  cases q with
  | zero => simp only [strictNegativeCost,withNat_eq,fastCap_eq,packedNegativeCost]
  | succ q =>
      cases q with
      | zero => simp only [strictNegativeCost,withNat_eq,fastCap_eq,packedNegativeCost]
      | succ q =>
          cases q with
          | zero => simp only [strictNegativeCost,withNat_eq,fastCap_eq,packedNegativeCost]
          | succ q => simp only [strictNegativeCost,withNat_eq,fastCap_eq,packedNegativeCost]



theorem strictCodeCheck_eq (q capcode : ℕ) (values : CostValues) (bound code : ℕ) :
    strictCodeCheck q capcode values bound code=packedCodeCheck q capcode values bound code := by
  simp only [strictCodeCheck,withNat_eq,fastRecord_eq,strictNegativeCost_eq,packedCodeCheck,packedVariableCost]
  rfl

end ThreeBoundEndpoint22Strict


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ThreeBoundEndpoint22Strict
open ThreeBoundRankCached ThreeBoundRankAnnotated



theorem Tree.strictCheck_eq (deny q : ℕ) (values : CostValues) (bound : ℕ)
    (t : ThreeBoundRankAnnotated.Tree) :
    Tree.strictCheck deny q values bound t=ThreeBoundEndpoint22Packed.Tree.fastCheck deny q values bound t := by
  induction t with
  | leaf bits key code =>
      simp only [Tree.strictCheck,ThreeBoundEndpoint22Packed.Tree.fastCheck,strictCodeCheck_eq]
  | branch bits pivot left right hl hr =>
      simp only [Tree.strictCheck,ThreeBoundEndpoint22Packed.Tree.fastCheck,hl,hr]





end ThreeBoundEndpoint22Strict


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundEndpoint22Records ThreeBoundRankAnnotated
theorem arithmetic_fast195 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny195 0 values195 bound195 annotated=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny195 0 values195 bound195 annotated=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_prepared195 : annotated.preparedCheck mask195 0 (prepared keyCodes.get convertedValues 0) values195 bound195=true := by
  have h:=arithmetic_fast195
  rw [ThreeBoundEndpoint22Packed.Tree.fastCheck_eq mask195 deny195 denied_checked195] at h
  rw [ThreeBoundEndpoint22Packed.Tree.packedCheck_eq mask195 (⟨0,by decide⟩ : Fin 4)
    values195 bound195 annotated annotated_statics_checked] at h
  simpa only [ThreeBoundRankAnnotated.Tree.fusedCheck_eq] using h
end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRankAnnotated.Tree.preparedCheck
    Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.mask195
    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
    (Sensitivity213981Formal.ThreeBoundRankAnnotated.prepared
      (Sensitivity213981Formal.ThreeBoundNumeric.NatTable.get
        Sensitivity213981Formal.ThreeBoundEndpoint22Records.keyCodes)
      Sensitivity213981Formal.ThreeBoundEndpoint22Records.convertedValues
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.values195
    Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.bound195
    Sensitivity213981Formal.ThreeBoundEndpoint22Records.annotated)
  Bool.true := @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.arithmetic_prepared195
