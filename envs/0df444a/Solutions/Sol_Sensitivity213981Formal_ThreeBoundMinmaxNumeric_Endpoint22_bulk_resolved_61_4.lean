-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.bulk_resolved_61_4
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:45:48.136987+00:00
-- url     : https://prove2.me/submissions/7875a902-8552-4a8c-abbb-39192fb12ea6

import Definitions.Def_Sensitivity213981Formal_Endpoint22DenyData
import Definitions.Def_Sensitivity213981Formal_Endpoint22EnvelopeData
import Definitions.Def_Sensitivity213981Formal_Endpoint22FastTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22StrictPacked
import Definitions.Def_Sensitivity213981Formal_Endpoint22StrictTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22VariableCacheData1100
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankAnnotatedTree
import Definitions.Def_Sensitivity213981Formal_RankBlockedBits
import Definitions.Def_Sensitivity213981Formal_RankCoefficientDominance
import Definitions.Def_Sensitivity213981Formal_RankPackedStrictCache
import Definitions.Def_Sensitivity213981Formal_Supplement_NumericExpressions
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch001
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Packed_Tree_cachedCheck_sound
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22VariableCache_cache1100_valid


namespace Sensitivity213981Formal
section
/- Homogeneous arithmetic expressions for the exact sensitivity transfer.
Every operation is interpreted in Nat. In particular subtraction is truncated
subtraction, which commutes with multiplication by every natural scalar. -/


set_option autoImplicit false

namespace ThreeBoundNumeric
open ThreeBoundFullProfile


















theorem le_maximum_of_mem {xs : List ℕ} {x : ℕ} (h : x ∈ xs) :
    x ≤  maximum xs := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact le_max_left _ _
      · exact (ih h).trans (le_max_right _ _)

theorem maximum_le {xs : List ℕ} {k : ℕ} (h : ∀ x ∈ xs, x ≤  k) :
    maximum xs ≤  k := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
      exact max_le (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))





















end ThreeBoundNumeric



end
end Sensitivity213981Formal

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







































































theorem denied_checked61 : deny61=denied mask61:=by decide +kernel




















































































































































































end ThreeBoundMinmaxNumeric.Endpoint22

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Reuse an exact record certificate when every normalized cost decreases. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ThreeBoundRankAnnotated
open ThreeBoundRankCached ThreeBoundRankNumeric
open ThreeBoundEndpoint22Records





theorem headSum_cross_le (q : ℕ) (x y : CostValues) (a b : ℕ)
    (h : CoefficientLe q x y a b) (r : Record) : headSum x r*b≤ headSum y r*a := by
  simp only [headSum,List.ofFn_eq_map]
  rw [← List.sum_map_mul_right,← List.sum_map_mul_right]
  apply List.sum_le_sum
  intro k hk
  simp only [Nat.add_mul,Nat.mul_assoc]
  apply Nat.add_le_add
  · apply Nat.add_le_add
    · exact Nat.mul_le_mul_left _ (h.heads ⟨3*k.val,by omega⟩)
    · exact Nat.mul_le_mul_left _ (h.heads ⟨3*k.val+1,by omega⟩)
  · exact Nat.mul_le_mul_left _ (h.heads ⟨3*k.val+2,by omega⟩)









theorem blocked_of_maskLe (small large : Array Bool) (h : MaskLe small large)
    (bits : ℕ) (hb : blocked large bits=true) : blocked small bits=true := by
  obtain ⟨k,hk,hbits⟩ := List.any_eq_true.mp hb
  obtain ⟨hbit,hnot⟩ := and_true hbits
  apply List.any_eq_true.mpr
  refine ⟨k,hk,?_⟩
  cases hs : small.getD k.val false with
  | false => simp only [hbit,hs,Bool.not_false,Bool.true_and]
  | true =>
      have hl := h k hs
      simp only [hl,Bool.not_true,Bool.false_eq_true] at hnot





end ThreeBoundRankAnnotated


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
open ThreeBoundRankCached


















































theorem denied_checked1100 : deny1100=denied mask1100 := by decide +kernel













theorem envelope_coefficient61 : CoefficientLe 3 values61 values1100 bound61 bound1100 := by decide +kernel

theorem envelope_mask61 : MaskLe mask61 mask1100 := by decide +kernel





















end ThreeBoundMinmaxNumeric.Endpoint22

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

theorem Tree.fastCheck_branch (deny q : ℕ) (values : CostValues) (bound bits : ℕ)
    (pivot : List ℕ) (left right : ThreeBoundRankAnnotated.Tree)
    (hl : Tree.fastCheck deny q values bound left=true)
    (hr : Tree.fastCheck deny q values bound right=true) :
    Tree.fastCheck deny q values bound (.branch bits pivot left right)=true := by
  simp only [Tree.fastCheck]
  split
  · rfl
  · simp only [hl,hr,Bool.true_and]



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
/- Exact coefficient transport for the packed and bit-mask checkers.
No record-static premise is needed: all packed negative weights are natural numbers.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ThreeBoundEndpoint22Packed
open ThreeBoundNumeric (maximum maximum_le le_maximum_of_mem)
open ThreeBoundRankCached ThreeBoundRankAnnotated
open ThreeBoundEndpoint22Records

theorem packedNegativeCost_cross_le (q : Fin 4) (capcode e : ℕ)
    (x y : CostValues) (a b : ℕ) (h : CoefficientLe q.val x y a b) :
    packedNegativeCost q.val capcode e x*b≤ packedNegativeCost q.val capcode e y*a := by
  fin_cases q
  · simpa only [packedNegativeCost,Nat.mul_assoc] using
      Nat.mul_le_mul_left (packedCap capcode e 0) (h.negative ⟨0,by decide⟩)
  · have h0 := Nat.mul_le_mul_left
      (min (packedCap capcode e 0) (packedCap capcode e 1)) (h.negative ⟨0,by decide⟩)
    have h1 := Nat.mul_le_mul_left
      (packedCap capcode e 1-min (packedCap capcode e 0) (packedCap capcode e 1))
      (h.negative ⟨1,by decide⟩)
    simpa only [packedNegativeCost,Nat.add_mul,Nat.mul_assoc] using Nat.add_le_add h0 h1
  · let s1:=min (packedCap capcode e 1) (packedCap capcode e 2)
    let s0:=min (packedCap capcode e 0) s1
    have h0 := Nat.mul_le_mul_left s0 (h.negative ⟨0,by decide⟩)
    have h1 := Nat.mul_le_mul_left (s1-s0) (h.negative ⟨1,by decide⟩)
    have h2 := Nat.mul_le_mul_left (packedCap capcode e 2-s1) (h.negative ⟨2,by decide⟩)
    simpa only [packedNegativeCost,Nat.add_mul,Nat.mul_assoc,s0,s1] using
      Nat.add_le_add (Nat.add_le_add h0 h1) h2
  · let s2:=min (packedCap capcode e 2) (packedCap capcode e 3)
    let s1:=min (packedCap capcode e 1) s2
    let s0:=min (packedCap capcode e 0) s1
    have h0 := Nat.mul_le_mul_left s0 (h.negative ⟨0,by decide⟩)
    have h1 := Nat.mul_le_mul_left (s1-s0) (h.negative ⟨1,by decide⟩)
    have h2 := Nat.mul_le_mul_left (s2-s1) (h.negative ⟨2,by decide⟩)
    have h3 := Nat.mul_le_mul_left (packedCap capcode e 3-s2) (h.negative ⟨3,by decide⟩)
    simpa only [packedNegativeCost,Nat.add_mul,Nat.mul_assoc,s0,s1,s2] using
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h0 h1) h2) h3

theorem packedVariableCost_cross_le (q : Fin 4) (capcode external e : ℕ)
    (x y : CostValues) (a b : ℕ) (h : CoefficientLe q.val x y a b) :
    packedVariableCost q.val capcode x external e*b≤ 
      packedVariableCost q.val capcode y external e*a := by
  have hg : ((external-e)*x.guard)*b≤ ((external-e)*y.guard)*a := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (external-e) h.guard
  have he : (e*x.converted)*b≤ (e*y.converted)*a := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left e h.converted
  simpa only [packedVariableCost,Nat.add_mul] using
    Nat.add_le_add (Nat.add_le_add hg he) (packedNegativeCost_cross_le q capcode e x y a b h)

theorem packedCodeCheck_of_dominance (q : Fin 4) (capcode : ℕ)
    (x y : CostValues) (a b code : ℕ) (hb : 0< b) (hc : CoefficientLe q.val x y a b)
    (hy : packedCodeCheck q.val capcode y b code=true) :
    packedCodeCheck q.val capcode x a code=true := by
  have hy' : headSum y (codeRecord code)+maximum
      ((List.range (codeRecord code 11+1)).map fun e =>
        packedVariableCost q.val capcode y (codeRecord code 11) e)≤ b := of_decide_eq_true hy
  have hx (e : ℕ) (he : e∈List.range (codeRecord code 11+1)) :
      headSum x (codeRecord code)+packedVariableCost q.val capcode x (codeRecord code 11) e≤ a := by
    have hm := le_maximum_of_mem (List.mem_map.mpr ⟨e,he,rfl⟩ :
      packedVariableCost q.val capcode y (codeRecord code 11) e∈
        (List.range (codeRecord code 11+1)).map
          (fun e => packedVariableCost q.val capcode y (codeRecord code 11) e))
    have hye : headSum y (codeRecord code)+
        packedVariableCost q.val capcode y (codeRecord code 11) e≤ b :=
      (Nat.add_le_add_left hm _).trans hy'
    have hcross : (headSum x (codeRecord code)+
        packedVariableCost q.val capcode x (codeRecord code 11) e)*b≤ 
        (headSum y (codeRecord code)+
          packedVariableCost q.val capcode y (codeRecord code 11) e)*a := by
      simpa only [Nat.add_mul] using Nat.add_le_add
        (headSum_cross_le q.val x y a b hc (codeRecord code))
        (packedVariableCost_cross_le q capcode (codeRecord code 11) e x y a b hc)
    apply Nat.le_of_mul_le_mul_right (c:=b) _ hb
    exact hcross.trans (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_right a hye)
  have h0:=hx 0 (by simp)
  have hhead : headSum x (codeRecord code)≤ a := by omega
  have hmax : maximum ((List.range (codeRecord code 11+1)).map fun e =>
      packedVariableCost q.val capcode x (codeRecord code 11) e)≤ a-headSum x (codeRecord code) := by
    apply maximum_le
    intro val hval
    obtain ⟨e,he,rfl⟩:=List.mem_map.mp hval
    exact (Nat.le_sub_iff_add_le hhead).mpr (by simpa only [Nat.add_comm] using hx e he)
  apply decide_eq_true
  change headSum x (codeRecord code)+maximum ((List.range (codeRecord code 11+1)).map fun e =>
      packedVariableCost q.val capcode x (codeRecord code 11) e)≤ a
  omega

theorem Tree.packedCheck_of_dominance (small large : Array Bool) (hm : MaskLe small large)
    (q : Fin 4) (x y : CostValues) (a b : ℕ)
    (hb : 0< b) (hc : CoefficientLe q.val x y a b) (t : ThreeBoundRankAnnotated.Tree)
    (hy : Tree.packedCheck large q.val y b t=true) :
    Tree.packedCheck small q.val x a t=true := by
  induction t with
  | leaf bits key code =>
      by_cases hs : blocked small (ThreeBoundRankAnnotated.Tree.leaf bits key code).mask=true
      · simp only [Tree.packedCheck,hs,if_true]
      · have hl : blocked large (ThreeBoundRankAnnotated.Tree.leaf bits key code).mask=false := by
          apply Bool.eq_false_iff.mpr
          exact fun hh => hs (blocked_of_maskLe small large hm _ hh)
        have hs' : blocked small (ThreeBoundRankAnnotated.Tree.leaf bits key code).mask=false :=
          Bool.eq_false_iff.mpr hs
        simp only [Tree.packedCheck,hl,hs',Bool.false_eq_true,if_false] at hy ⊢
        exact packedCodeCheck_of_dominance q (convertedCodes.get key) x y a b code hb hc hy
  | branch bits pivot left right il ir =>
      by_cases hs : blocked small (ThreeBoundRankAnnotated.Tree.branch bits pivot left right).mask=true
      · simp only [Tree.packedCheck,hs,if_true]
      · have hl : blocked large (ThreeBoundRankAnnotated.Tree.branch bits pivot left right).mask=false := by
          apply Bool.eq_false_iff.mpr
          exact fun hh => hs (blocked_of_maskLe small large hm _ hh)
        have hs' : blocked small (ThreeBoundRankAnnotated.Tree.branch bits pivot left right).mask=false :=
          Bool.eq_false_iff.mpr hs
        simp only [Tree.packedCheck,hl,hs',Bool.false_eq_true,if_false] at hy ⊢
        obtain ⟨hleft,hright⟩ := and_true hy
        simp only [il hleft,ir hright,Bool.true_and]

theorem Tree.fastCheck_of_dominance (small large : Array Bool) (hm : MaskLe small large)
    (denySmall denyLarge : ℕ) (hds : denySmall=denied small) (hdl : denyLarge=denied large)
    (q : Fin 4) (x y : CostValues) (a b : ℕ)
    (hb : 0< b) (hc : CoefficientLe q.val x y a b) (t : ThreeBoundRankAnnotated.Tree)
    (hy : Tree.fastCheck denyLarge q.val y b t=true) :
    Tree.fastCheck denySmall q.val x a t=true := by
  rw [Tree.fastCheck_eq large denyLarge hdl] at hy
  rw [Tree.fastCheck_eq small denySmall hds]
  exact Tree.packedCheck_of_dominance small large hm q x y a b hb hc t hy

end ThreeBoundEndpoint22Packed


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Force the packed capcode once before the cache search, and use proved
bit-shift record access.  This changes evaluation order only. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ThreeBoundEndpoint22Packed
open ThreeBoundRankCached ThreeBoundRankAnnotated
open ThreeBoundEndpoint22Records ThreeBoundEndpoint22Strict



theorem strictCachedCodeCheck_eq (cache : VariableCache) (capcode : ℕ) (values : CostValues)
    (bound code : ℕ) :
    strictCachedCodeCheck cache capcode values bound code=
      cachedCodeCheck cache capcode values bound code := by
  simp only [strictCachedCodeCheck,withNat_eq,fastRecord_eq,cachedCodeCheck]
  rfl



theorem Tree.strictCachedCheck_eq (deny : ℕ) (cache : VariableCache) (values : CostValues)
    (bound : ℕ) (t : ThreeBoundRankAnnotated.Tree) :
    Tree.strictCachedCheck deny cache values bound t=Tree.cachedCheck deny cache values bound t := by
  induction t with
  | leaf bits key code =>
      simp only [Tree.strictCachedCheck,Tree.cachedCheck,strictCachedCodeCheck_eq]
  | branch bits pivot left right hl hr =>
      simp only [Tree.strictCachedCheck,Tree.cachedCheck,hl,hr]

theorem Tree.strictCachedCheck_sound (deny q : ℕ) (cache : VariableCache) (values : CostValues)
    (bound : ℕ) (hc : cache.check q values=true) (t : ThreeBoundRankAnnotated.Tree)
    (h : Tree.strictCachedCheck deny cache values bound t=true) :
    Tree.fastCheck deny q values bound t=true := by
  rw [Tree.strictCachedCheck_eq] at h
  exact Tree.cachedCheck_sound deny q cache values bound hc t h





end ThreeBoundEndpoint22Packed


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
theorem bulk_1100_4_3_0 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny1100 3 values1100 bound1100 ((annotated4.frontier 3).getD 0 annotated4)=true := by
  have h : ThreeBoundEndpoint22Packed.Tree.strictCachedCheck deny1100 ThreeBoundEndpoint22VariableCache.cache1100 values1100 bound1100 ((annotated4.frontier 3).getD 0 annotated4)=true := by decide +kernel
  exact ThreeBoundEndpoint22Packed.Tree.strictCachedCheck_sound deny1100 3 ThreeBoundEndpoint22VariableCache.cache1100
    values1100 bound1100 ThreeBoundEndpoint22VariableCache.cache1100_valid ((annotated4.frontier 3).getD 0 annotated4) h

theorem bulk_1100_4_3_1 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny1100 3 values1100 bound1100 ((annotated4.frontier 3).getD 1 annotated4)=true := by
  have h : ThreeBoundEndpoint22Packed.Tree.strictCachedCheck deny1100 ThreeBoundEndpoint22VariableCache.cache1100 values1100 bound1100 ((annotated4.frontier 3).getD 1 annotated4)=true := by decide +kernel
  exact ThreeBoundEndpoint22Packed.Tree.strictCachedCheck_sound deny1100 3 ThreeBoundEndpoint22VariableCache.cache1100
    values1100 bound1100 ThreeBoundEndpoint22VariableCache.cache1100_valid ((annotated4.frontier 3).getD 1 annotated4) h

theorem bulk_1100_4_3_2 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny1100 3 values1100 bound1100 ((annotated4.frontier 3).getD 2 annotated4)=true := by
  have h : ThreeBoundEndpoint22Packed.Tree.strictCachedCheck deny1100 ThreeBoundEndpoint22VariableCache.cache1100 values1100 bound1100 ((annotated4.frontier 3).getD 2 annotated4)=true := by decide +kernel
  exact ThreeBoundEndpoint22Packed.Tree.strictCachedCheck_sound deny1100 3 ThreeBoundEndpoint22VariableCache.cache1100
    values1100 bound1100 ThreeBoundEndpoint22VariableCache.cache1100_valid ((annotated4.frontier 3).getD 2 annotated4) h

theorem bulk_1100_4_5_12 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny1100 3 values1100 bound1100 ((annotated4.frontier 5).getD 12 annotated4)=true := by
  have h : ThreeBoundEndpoint22Packed.Tree.strictCachedCheck deny1100 ThreeBoundEndpoint22VariableCache.cache1100 values1100 bound1100 ((annotated4.frontier 5).getD 12 annotated4)=true := by decide +kernel
  exact ThreeBoundEndpoint22Packed.Tree.strictCachedCheck_sound deny1100 3 ThreeBoundEndpoint22VariableCache.cache1100
    values1100 bound1100 ThreeBoundEndpoint22VariableCache.cache1100_valid ((annotated4.frontier 5).getD 12 annotated4) h

theorem bulk_1100_4_6_26 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny1100 3 values1100 bound1100 ((annotated4.frontier 6).getD 26 annotated4)=true := by
  have h : ThreeBoundEndpoint22Packed.Tree.strictCachedCheck deny1100 ThreeBoundEndpoint22VariableCache.cache1100 values1100 bound1100 ((annotated4.frontier 6).getD 26 annotated4)=true := by decide +kernel
  exact ThreeBoundEndpoint22Packed.Tree.strictCachedCheck_sound deny1100 3 ThreeBoundEndpoint22VariableCache.cache1100
    values1100 bound1100 ThreeBoundEndpoint22VariableCache.cache1100_valid ((annotated4.frontier 6).getD 26 annotated4) h

theorem bulk_1100_4_7_54 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny1100 3 values1100 bound1100 ((annotated4.frontier 7).getD 54 annotated4)=true := by
  have h : ThreeBoundEndpoint22Packed.Tree.strictCachedCheck deny1100 ThreeBoundEndpoint22VariableCache.cache1100 values1100 bound1100 ((annotated4.frontier 7).getD 54 annotated4)=true := by decide +kernel
  exact ThreeBoundEndpoint22Packed.Tree.strictCachedCheck_sound deny1100 3 ThreeBoundEndpoint22VariableCache.cache1100
    values1100 bound1100 ThreeBoundEndpoint22VariableCache.cache1100_valid ((annotated4.frontier 7).getD 54 annotated4) h

theorem bulk_1100_4_8_110 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny1100 3 values1100 bound1100 ((annotated4.frontier 8).getD 110 annotated4)=true := by
  have h : ThreeBoundEndpoint22Packed.Tree.strictCachedCheck deny1100 ThreeBoundEndpoint22VariableCache.cache1100 values1100 bound1100 ((annotated4.frontier 8).getD 110 annotated4)=true := by decide +kernel
  exact ThreeBoundEndpoint22Packed.Tree.strictCachedCheck_sound deny1100 3 ThreeBoundEndpoint22VariableCache.cache1100
    values1100 bound1100 ThreeBoundEndpoint22VariableCache.cache1100_valid ((annotated4.frontier 8).getD 110 annotated4) h

theorem bulk_1100_4_10_444 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny1100 3 values1100 bound1100 ((annotated4.frontier 10).getD 444 annotated4)=true := by
  have h : ThreeBoundEndpoint22Packed.Tree.strictCachedCheck deny1100 ThreeBoundEndpoint22VariableCache.cache1100 values1100 bound1100 ((annotated4.frontier 10).getD 444 annotated4)=true := by decide +kernel
  exact ThreeBoundEndpoint22Packed.Tree.strictCachedCheck_sound deny1100 3 ThreeBoundEndpoint22VariableCache.cache1100
    values1100 bound1100 ThreeBoundEndpoint22VariableCache.cache1100_valid ((annotated4.frontier 10).getD 444 annotated4) h

theorem bulk_1100_4_9_223 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny1100 3 values1100 bound1100 ((annotated4.frontier 9).getD 223 annotated4)=true := by
  have h : ThreeBoundEndpoint22Packed.Tree.strictCachedCheck deny1100 ThreeBoundEndpoint22VariableCache.cache1100 values1100 bound1100 ((annotated4.frontier 9).getD 223 annotated4)=true := by decide +kernel
  exact ThreeBoundEndpoint22Packed.Tree.strictCachedCheck_sound deny1100 3 ThreeBoundEndpoint22VariableCache.cache1100
    values1100 bound1100 ThreeBoundEndpoint22VariableCache.cache1100_valid ((annotated4.frontier 9).getD 223 annotated4) h

theorem bulk_1100_4_4_7 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny1100 3 values1100 bound1100 ((annotated4.frontier 4).getD 7 annotated4)=true := by
  have h : ThreeBoundEndpoint22Packed.Tree.strictCachedCheck deny1100 ThreeBoundEndpoint22VariableCache.cache1100 values1100 bound1100 ((annotated4.frontier 4).getD 7 annotated4)=true := by decide +kernel
  exact ThreeBoundEndpoint22Packed.Tree.strictCachedCheck_sound deny1100 3 ThreeBoundEndpoint22VariableCache.cache1100
    values1100 bound1100 ThreeBoundEndpoint22VariableCache.cache1100_valid ((annotated4.frontier 4).getD 7 annotated4) h

theorem bulk_1100_4_1_1 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny1100 3 values1100 bound1100 ((annotated4.frontier 1).getD 1 annotated4)=true := by
  have h : ThreeBoundEndpoint22Packed.Tree.strictCachedCheck deny1100 ThreeBoundEndpoint22VariableCache.cache1100 values1100 bound1100 ((annotated4.frontier 1).getD 1 annotated4)=true := by decide +kernel
  exact ThreeBoundEndpoint22Packed.Tree.strictCachedCheck_sound deny1100 3 ThreeBoundEndpoint22VariableCache.cache1100
    values1100 bound1100 ThreeBoundEndpoint22VariableCache.cache1100_valid ((annotated4.frontier 1).getD 1 annotated4) h













theorem bulk_exception_61_4_445 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny61 3 values61 bound61 ((annotated4.frontier 10).getD 445 annotated4)=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny61 3 values61 bound61 ((annotated4.frontier 10).getD 445 annotated4)=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem bulk_resolved_61_4 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny61 3 values61 bound61 annotated4=true := by
  apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
  ·
    apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
    ·
      apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
      ·
        exact ThreeBoundEndpoint22Packed.Tree.fastCheck_of_dominance mask61 mask1100
          envelope_mask61 deny61 deny1100 denied_checked61 denied_checked1100
          (⟨3,by decide⟩ : Fin 4) values61 values1100 bound61 bound1100
          (by decide) envelope_coefficient61 ((annotated4.frontier 3).getD 0 annotated4) bulk_1100_4_3_0
      ·
        exact ThreeBoundEndpoint22Packed.Tree.fastCheck_of_dominance mask61 mask1100
          envelope_mask61 deny61 deny1100 denied_checked61 denied_checked1100
          (⟨3,by decide⟩ : Fin 4) values61 values1100 bound61 bound1100
          (by decide) envelope_coefficient61 ((annotated4.frontier 3).getD 1 annotated4) bulk_1100_4_3_1
    ·
      apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
      ·
        exact ThreeBoundEndpoint22Packed.Tree.fastCheck_of_dominance mask61 mask1100
          envelope_mask61 deny61 deny1100 denied_checked61 denied_checked1100
          (⟨3,by decide⟩ : Fin 4) values61 values1100 bound61 bound1100
          (by decide) envelope_coefficient61 ((annotated4.frontier 3).getD 2 annotated4) bulk_1100_4_3_2
      ·
        apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
        ·
          apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
          ·
            exact ThreeBoundEndpoint22Packed.Tree.fastCheck_of_dominance mask61 mask1100
              envelope_mask61 deny61 deny1100 denied_checked61 denied_checked1100
              (⟨3,by decide⟩ : Fin 4) values61 values1100 bound61 bound1100
              (by decide) envelope_coefficient61 ((annotated4.frontier 5).getD 12 annotated4) bulk_1100_4_5_12
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact ThreeBoundEndpoint22Packed.Tree.fastCheck_of_dominance mask61 mask1100
                envelope_mask61 deny61 deny1100 denied_checked61 denied_checked1100
                (⟨3,by decide⟩ : Fin 4) values61 values1100 bound61 bound1100
                (by decide) envelope_coefficient61 ((annotated4.frontier 6).getD 26 annotated4) bulk_1100_4_6_26
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact ThreeBoundEndpoint22Packed.Tree.fastCheck_of_dominance mask61 mask1100
                  envelope_mask61 deny61 deny1100 denied_checked61 denied_checked1100
                  (⟨3,by decide⟩ : Fin 4) values61 values1100 bound61 bound1100
                  (by decide) envelope_coefficient61 ((annotated4.frontier 7).getD 54 annotated4) bulk_1100_4_7_54
              ·
                apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
                ·
                  exact ThreeBoundEndpoint22Packed.Tree.fastCheck_of_dominance mask61 mask1100
                    envelope_mask61 deny61 deny1100 denied_checked61 denied_checked1100
                    (⟨3,by decide⟩ : Fin 4) values61 values1100 bound61 bound1100
                    (by decide) envelope_coefficient61 ((annotated4.frontier 8).getD 110 annotated4) bulk_1100_4_8_110
                ·
                  apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
                  ·
                    apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
                    ·
                      exact ThreeBoundEndpoint22Packed.Tree.fastCheck_of_dominance mask61 mask1100
                        envelope_mask61 deny61 deny1100 denied_checked61 denied_checked1100
                        (⟨3,by decide⟩ : Fin 4) values61 values1100 bound61 bound1100
                        (by decide) envelope_coefficient61 ((annotated4.frontier 10).getD 444 annotated4) bulk_1100_4_10_444
                    ·
                      exact bulk_exception_61_4_445
                  ·
                    exact ThreeBoundEndpoint22Packed.Tree.fastCheck_of_dominance mask61 mask1100
                      envelope_mask61 deny61 deny1100 denied_checked61 denied_checked1100
                      (⟨3,by decide⟩ : Fin 4) values61 values1100 bound61 bound1100
                      (by decide) envelope_coefficient61 ((annotated4.frontier 9).getD 223 annotated4) bulk_1100_4_9_223
        ·
          exact ThreeBoundEndpoint22Packed.Tree.fastCheck_of_dominance mask61 mask1100
            envelope_mask61 deny61 deny1100 denied_checked61 denied_checked1100
            (⟨3,by decide⟩ : Fin 4) values61 values1100 bound61 bound1100
            (by decide) envelope_coefficient61 ((annotated4.frontier 4).getD 7 annotated4) bulk_1100_4_4_7
  ·
    exact ThreeBoundEndpoint22Packed.Tree.fastCheck_of_dominance mask61 mask1100
      envelope_mask61 deny61 deny1100 denied_checked61 denied_checked1100
      (⟨3,by decide⟩ : Fin 4) values61 values1100 bound61 bound1100
      (by decide) envelope_coefficient61 ((annotated4.frontier 1).getD 1 annotated4) bulk_1100_4_1_1





















end ThreeBoundMinmaxNumeric.Endpoint22

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundEndpoint22Packed.Tree.fastCheck
    Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.deny61
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.values61
    Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.bound61
    Sensitivity213981Formal.ThreeBoundEndpoint22Records.annotated4)
  Bool.true := @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.bulk_resolved_61_4
