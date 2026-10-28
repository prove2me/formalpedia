-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.arithmetic_block_52_46
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T23:13:24.599097+00:00
-- url     : https://prove2.me/submissions/69a7e46c-e1e6-4b62-8af4-2bf00ad86d05

import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData046
import Definitions.Def_Sensitivity213981Formal_Endpoint22EnvelopeData
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Packed_Tree_fastCheck_of_frontier


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
theorem arithmetic_part_52_46_0 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny52 3 values52 bound52 ((annotated46.frontier 3).getD 0 annotated46)=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny52 3 values52 bound52 ((annotated46.frontier 3).getD 0 annotated46)=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_part_52_46_1 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny52 3 values52 bound52 ((annotated46.frontier 3).getD 1 annotated46)=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny52 3 values52 bound52 ((annotated46.frontier 3).getD 1 annotated46)=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_part_52_46_2 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny52 3 values52 bound52 ((annotated46.frontier 3).getD 2 annotated46)=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny52 3 values52 bound52 ((annotated46.frontier 3).getD 2 annotated46)=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_part_52_46_3 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny52 3 values52 bound52 ((annotated46.frontier 3).getD 3 annotated46)=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny52 3 values52 bound52 ((annotated46.frontier 3).getD 3 annotated46)=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_part_52_46_4 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny52 3 values52 bound52 ((annotated46.frontier 3).getD 4 annotated46)=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny52 3 values52 bound52 ((annotated46.frontier 3).getD 4 annotated46)=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_part_52_46_5 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny52 3 values52 bound52 ((annotated46.frontier 3).getD 5 annotated46)=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny52 3 values52 bound52 ((annotated46.frontier 3).getD 5 annotated46)=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_part_52_46_6 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny52 3 values52 bound52 ((annotated46.frontier 3).getD 6 annotated46)=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny52 3 values52 bound52 ((annotated46.frontier 3).getD 6 annotated46)=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_part_52_46_7 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny52 3 values52 bound52 ((annotated46.frontier 3).getD 7 annotated46)=true := by
  have h : ThreeBoundEndpoint22Strict.Tree.strictCheck deny52 3 values52 bound52 ((annotated46.frontier 3).getD 7 annotated46)=true := by decide +kernel
  simpa only [ThreeBoundEndpoint22Strict.Tree.strictCheck_eq] using h

theorem arithmetic_block_52_46 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny52 3 values52 bound52 annotated46=true := by
  apply ThreeBoundEndpoint22Packed.Tree.fastCheck_of_frontier deny52 3 values52 bound52 3 annotated46
  change [((annotated46.frontier 3).getD 0 annotated46),((annotated46.frontier 3).getD 1 annotated46),((annotated46.frontier 3).getD 2 annotated46),((annotated46.frontier 3).getD 3 annotated46),((annotated46.frontier 3).getD 4 annotated46),((annotated46.frontier 3).getD 5 annotated46),((annotated46.frontier 3).getD 6 annotated46),((annotated46.frontier 3).getD 7 annotated46)].all (fun t => ThreeBoundEndpoint22Packed.Tree.fastCheck deny52 3 values52 bound52 t)=true
  simp only [List.all_cons,List.all_nil,arithmetic_part_52_46_0,arithmetic_part_52_46_1,arithmetic_part_52_46_2,arithmetic_part_52_46_3,arithmetic_part_52_46_4,arithmetic_part_52_46_5,arithmetic_part_52_46_6,arithmetic_part_52_46_7,Bool.true_and]
end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundEndpoint22Packed.Tree.fastCheck
    Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.deny52
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.values52
    Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.bound52
    Sensitivity213981Formal.ThreeBoundEndpoint22Records.annotated46)
  Bool.true := @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.arithmetic_block_52_46
