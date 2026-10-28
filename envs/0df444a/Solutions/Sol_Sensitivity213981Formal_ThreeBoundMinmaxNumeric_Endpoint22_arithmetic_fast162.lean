-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.arithmetic_fast162
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T23:49:59.846179+00:00
-- url     : https://prove2.me/submissions/0bf93075-a5a2-4428-9cd5-fceedadcd2af

import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData
import Definitions.Def_Sensitivity213981Formal_Endpoint22EnvelopeData
import Definitions.Def_Sensitivity213981Formal_Endpoint22FastTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22StrictPacked
import Definitions.Def_Sensitivity213981Formal_Endpoint22StrictTree
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
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


namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ThreeBoundEndpoint22Packed
open ThreeBoundRankCached ThreeBoundRankAnnotated





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

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundEndpoint22Records ThreeBoundRankAnnotated
theorem arithmetic_block_162_0 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated0=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated0=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_1 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated1=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated1=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_2 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated2=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated2=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_3 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated3=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated3=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_4 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated4=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated4=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_5 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated5=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated5=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_6 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated6=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated6=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_7 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated7=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated7=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_8 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated8=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated8=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_9 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated9=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated9=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_10 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated10=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated10=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_11 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated11=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated11=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_12 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated12=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated12=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_13 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated13=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated13=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_14 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated14=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated14=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_15 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated15=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated15=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_16 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated16=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated16=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_17 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated17=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated17=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_18 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated18=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated18=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_19 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated19=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated19=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_20 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated20=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated20=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_21 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated21=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated21=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_22 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated22=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated22=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_23 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated23=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated23=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_24 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated24=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated24=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_25 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated25=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated25=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_26 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated26=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated26=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_27 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated27=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated27=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_28 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated28=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated28=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_29 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated29=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated29=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_30 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated30=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated30=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_31 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated31=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated31=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_32 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated32=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated32=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_33 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated33=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated33=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_34 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated34=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated34=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_35 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated35=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated35=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_36 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated36=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated36=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_37 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated37=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated37=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_38 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated38=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated38=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_39 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated39=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated39=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_40 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated40=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated40=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_41 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated41=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated41=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_42 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated42=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated42=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_43 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated43=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated43=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_44 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated44=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated44=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_45 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated45=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated45=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_46 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated46=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated46=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_47 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated47=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated47=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_48 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated48=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated48=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_49 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated49=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated49=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_50 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated50=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated50=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_51 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated51=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated51=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_52 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated52=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated52=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_53 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated53=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated53=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_54 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated54=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated54=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_55 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated55=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated55=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_56 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated56=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated56=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_57 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated57=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated57=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_58 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated58=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated58=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_59 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated59=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated59=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_60 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated60=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated60=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_61 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated61=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated61=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_62 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated62=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated62=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_63 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated63=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated63=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_64 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated64=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated64=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_65 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated65=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated65=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_66 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated66=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated66=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_67 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated67=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated67=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_68 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated68=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated68=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_69 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated69=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated69=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_70 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated70=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated70=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_71 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated71=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated71=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_72 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated72=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated72=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_73 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated73=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated73=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_74 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated74=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated74=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_75 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated75=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated75=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_76 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated76=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated76=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_77 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated77=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated77=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_78 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated78=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated78=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_79 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated79=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated79=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_80 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated80=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated80=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_81 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated81=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated81=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_82 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated82=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated82=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_83 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated83=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated83=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_84 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated84=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated84=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_85 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated85=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated85=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_86 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated86=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated86=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_87 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated87=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated87=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_88 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated88=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated88=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_89 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated89=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated89=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_90 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated90=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated90=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_91 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated91=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated91=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_92 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated92=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated92=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_93 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated93=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated93=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_94 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated94=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated94=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_162_95 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated95=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny162 2 values162 bound162 annotated95=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_fast162 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny162 2 values162 bound162 annotated=true := by
  unfold annotated
  apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
  ·
    apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
    ·
      apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
      ·
        apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
        ·
          apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_162_0
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_162_1
              ·
                exact arithmetic_block_162_2
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_162_3
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_162_4
              ·
                exact arithmetic_block_162_5
        ·
          apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_162_6
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_162_7
              ·
                exact arithmetic_block_162_8
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_162_9
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_162_10
              ·
                exact arithmetic_block_162_11
      ·
        apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
        ·
          apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_162_12
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_162_13
              ·
                exact arithmetic_block_162_14
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_162_15
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_162_16
              ·
                exact arithmetic_block_162_17
        ·
          apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_162_18
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_162_19
              ·
                exact arithmetic_block_162_20
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_162_21
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_162_22
              ·
                exact arithmetic_block_162_23
    ·
      apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
      ·
        apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
        ·
          apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_162_24
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_162_25
              ·
                exact arithmetic_block_162_26
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_162_27
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_162_28
              ·
                exact arithmetic_block_162_29
        ·
          apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_162_30
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_162_31
              ·
                exact arithmetic_block_162_32
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_162_33
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_162_34
              ·
                exact arithmetic_block_162_35
      ·
        apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
        ·
          apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_162_36
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_162_37
              ·
                exact arithmetic_block_162_38
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_162_39
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_162_40
              ·
                exact arithmetic_block_162_41
        ·
          apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_162_42
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_162_43
              ·
                exact arithmetic_block_162_44
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_162_45
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_162_46
              ·
                exact arithmetic_block_162_47
  ·
    apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
    ·
      apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
      ·
        apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
        ·
          apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_162_48
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_162_49
              ·
                exact arithmetic_block_162_50
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_162_51
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_162_52
              ·
                exact arithmetic_block_162_53
        ·
          apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_162_54
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_162_55
              ·
                exact arithmetic_block_162_56
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_162_57
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_162_58
              ·
                exact arithmetic_block_162_59
      ·
        apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
        ·
          apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_162_60
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_162_61
              ·
                exact arithmetic_block_162_62
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_162_63
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_162_64
              ·
                exact arithmetic_block_162_65
        ·
          apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_162_66
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_162_67
              ·
                exact arithmetic_block_162_68
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_162_69
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_162_70
              ·
                exact arithmetic_block_162_71
    ·
      apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
      ·
        apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
        ·
          apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_162_72
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_162_73
              ·
                exact arithmetic_block_162_74
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_162_75
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_162_76
              ·
                exact arithmetic_block_162_77
        ·
          apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_162_78
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_162_79
              ·
                exact arithmetic_block_162_80
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_162_81
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_162_82
              ·
                exact arithmetic_block_162_83
      ·
        apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
        ·
          apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_162_84
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_162_85
              ·
                exact arithmetic_block_162_86
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_162_87
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_162_88
              ·
                exact arithmetic_block_162_89
        ·
          apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_162_90
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_162_91
              ·
                exact arithmetic_block_162_92
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_162_93
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_162_94
              ·
                exact arithmetic_block_162_95


end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundEndpoint22Packed.Tree.fastCheck
    Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.deny162
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.values162
    Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.bound162
    Sensitivity213981Formal.ThreeBoundEndpoint22Records.annotated)
  Bool.true := @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.arithmetic_fast162
