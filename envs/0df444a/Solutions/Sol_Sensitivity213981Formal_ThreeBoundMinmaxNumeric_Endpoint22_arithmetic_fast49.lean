-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.arithmetic_fast49
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T23:08:23.458912+00:00
-- url     : https://prove2.me/submissions/b5c22885-1b68-4373-9033-11a10b0c05fc

import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData
import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData011
import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData028
import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData041
import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData046
import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData059
import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData068
import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData072
import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData087
import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData089
import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData091
import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData092
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_block_49_11
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_block_49_28
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_block_49_41
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_block_49_46
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_block_49_59
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_block_49_68
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_block_49_72
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_block_49_87
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_block_49_89
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_block_49_91
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_block_49_92


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
theorem arithmetic_block_49_0 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated0=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated0=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_1 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated1=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated1=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_2 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated2=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated2=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_3 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated3=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated3=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_4 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated4=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated4=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_5 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated5=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated5=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_6 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated6=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated6=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_7 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated7=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated7=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_8 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated8=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated8=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_9 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated9=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated9=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_10 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated10=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated10=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_12 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated12=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated12=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_13 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated13=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated13=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_14 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated14=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated14=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_15 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated15=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated15=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_16 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated16=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated16=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_17 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated17=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated17=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_18 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated18=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated18=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_19 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated19=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated19=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_20 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated20=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated20=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_21 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated21=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated21=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_22 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated22=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated22=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_23 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated23=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated23=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_24 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated24=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated24=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_25 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated25=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated25=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_26 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated26=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated26=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_27 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated27=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated27=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_29 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated29=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated29=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_30 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated30=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated30=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_31 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated31=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated31=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_32 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated32=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated32=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_33 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated33=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated33=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_34 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated34=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated34=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_35 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated35=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated35=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_36 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated36=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated36=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_37 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated37=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated37=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_38 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated38=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated38=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_39 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated39=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated39=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_40 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated40=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated40=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_42 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated42=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated42=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_43 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated43=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated43=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_44 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated44=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated44=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_45 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated45=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated45=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_47 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated47=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated47=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_48 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated48=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated48=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_49 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated49=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated49=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_50 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated50=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated50=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_51 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated51=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated51=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_52 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated52=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated52=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_53 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated53=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated53=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_54 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated54=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated54=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_55 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated55=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated55=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_56 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated56=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated56=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_57 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated57=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated57=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_58 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated58=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated58=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_60 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated60=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated60=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_61 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated61=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated61=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_62 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated62=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated62=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_63 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated63=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated63=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_64 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated64=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated64=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_65 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated65=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated65=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_66 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated66=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated66=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_67 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated67=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated67=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_69 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated69=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated69=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_70 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated70=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated70=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_71 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated71=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated71=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_73 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated73=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated73=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_74 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated74=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated74=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_75 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated75=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated75=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_76 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated76=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated76=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_77 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated77=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated77=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_78 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated78=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated78=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_79 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated79=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated79=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_80 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated80=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated80=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_81 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated81=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated81=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_82 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated82=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated82=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_83 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated83=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated83=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_84 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated84=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated84=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_85 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated85=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated85=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_86 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated86=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated86=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_88 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated88=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated88=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_90 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated90=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated90=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_93 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated93=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated93=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_94 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated94=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated94=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_49_95 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated95=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny49 3 values49 bound49 annotated95=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_fast49 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny49 3 values49 bound49 annotated=true := by
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
              exact arithmetic_block_49_0
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_49_1
              ·
                exact arithmetic_block_49_2
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_49_3
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_49_4
              ·
                exact arithmetic_block_49_5
        ·
          apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_49_6
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_49_7
              ·
                exact arithmetic_block_49_8
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_49_9
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_49_10
              ·
                exact arithmetic_block_49_11
      ·
        apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
        ·
          apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_49_12
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_49_13
              ·
                exact arithmetic_block_49_14
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_49_15
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_49_16
              ·
                exact arithmetic_block_49_17
        ·
          apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_49_18
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_49_19
              ·
                exact arithmetic_block_49_20
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_49_21
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_49_22
              ·
                exact arithmetic_block_49_23
    ·
      apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
      ·
        apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
        ·
          apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_49_24
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_49_25
              ·
                exact arithmetic_block_49_26
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_49_27
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_49_28
              ·
                exact arithmetic_block_49_29
        ·
          apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_49_30
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_49_31
              ·
                exact arithmetic_block_49_32
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_49_33
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_49_34
              ·
                exact arithmetic_block_49_35
      ·
        apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
        ·
          apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_49_36
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_49_37
              ·
                exact arithmetic_block_49_38
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_49_39
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_49_40
              ·
                exact arithmetic_block_49_41
        ·
          apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_49_42
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_49_43
              ·
                exact arithmetic_block_49_44
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_49_45
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_49_46
              ·
                exact arithmetic_block_49_47
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
              exact arithmetic_block_49_48
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_49_49
              ·
                exact arithmetic_block_49_50
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_49_51
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_49_52
              ·
                exact arithmetic_block_49_53
        ·
          apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_49_54
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_49_55
              ·
                exact arithmetic_block_49_56
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_49_57
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_49_58
              ·
                exact arithmetic_block_49_59
      ·
        apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
        ·
          apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_49_60
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_49_61
              ·
                exact arithmetic_block_49_62
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_49_63
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_49_64
              ·
                exact arithmetic_block_49_65
        ·
          apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_49_66
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_49_67
              ·
                exact arithmetic_block_49_68
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_49_69
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_49_70
              ·
                exact arithmetic_block_49_71
    ·
      apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
      ·
        apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
        ·
          apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_49_72
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_49_73
              ·
                exact arithmetic_block_49_74
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_49_75
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_49_76
              ·
                exact arithmetic_block_49_77
        ·
          apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_49_78
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_49_79
              ·
                exact arithmetic_block_49_80
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_49_81
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_49_82
              ·
                exact arithmetic_block_49_83
      ·
        apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
        ·
          apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_49_84
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_49_85
              ·
                exact arithmetic_block_49_86
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_49_87
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_49_88
              ·
                exact arithmetic_block_49_89
        ·
          apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_49_90
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_49_91
              ·
                exact arithmetic_block_49_92
          ·
            apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
            ·
              exact arithmetic_block_49_93
            ·
              apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
              ·
                exact arithmetic_block_49_94
              ·
                exact arithmetic_block_49_95


end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundEndpoint22Packed.Tree.fastCheck
    Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.deny49
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.values49
    Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.bound49
    Sensitivity213981Formal.ThreeBoundEndpoint22Records.annotated)
  Bool.true := @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.arithmetic_fast49
