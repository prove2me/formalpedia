-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.bulk_block_1100_52
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:47:28.034041+00:00
-- url     : https://prove2.me/submissions/dd164155-8d55-4e6c-84ff-879f87f82b1a

import Definitions.Def_Sensitivity213981Formal_Endpoint22EnvelopeData
import Definitions.Def_Sensitivity213981Formal_Endpoint22FastTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22StrictPacked
import Definitions.Def_Sensitivity213981Formal_Endpoint22StrictTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22VariableCacheData1100
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankCoefficientDominance
import Definitions.Def_Sensitivity213981Formal_RankPackedStrictCache
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch012
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













end ThreeBoundEndpoint22Strict


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
theorem bulk_1100_52_1_0 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny1100 3 values1100 bound1100 ((annotated52.frontier 1).getD 0 annotated52)=true := by
  have h : ThreeBoundEndpoint22Packed.Tree.strictCachedCheck deny1100 ThreeBoundEndpoint22VariableCache.cache1100 values1100 bound1100 ((annotated52.frontier 1).getD 0 annotated52)=true := by decide +kernel
  exact ThreeBoundEndpoint22Packed.Tree.strictCachedCheck_sound deny1100 3 ThreeBoundEndpoint22VariableCache.cache1100
    values1100 bound1100 ThreeBoundEndpoint22VariableCache.cache1100_valid ((annotated52.frontier 1).getD 0 annotated52) h

theorem bulk_1100_52_2_2 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny1100 3 values1100 bound1100 ((annotated52.frontier 2).getD 2 annotated52)=true := by
  have h : ThreeBoundEndpoint22Packed.Tree.strictCachedCheck deny1100 ThreeBoundEndpoint22VariableCache.cache1100 values1100 bound1100 ((annotated52.frontier 2).getD 2 annotated52)=true := by decide +kernel
  exact ThreeBoundEndpoint22Packed.Tree.strictCachedCheck_sound deny1100 3 ThreeBoundEndpoint22VariableCache.cache1100
    values1100 bound1100 ThreeBoundEndpoint22VariableCache.cache1100_valid ((annotated52.frontier 2).getD 2 annotated52) h

theorem bulk_1100_52_3_6 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny1100 3 values1100 bound1100 ((annotated52.frontier 3).getD 6 annotated52)=true := by
  have h : ThreeBoundEndpoint22Packed.Tree.strictCachedCheck deny1100 ThreeBoundEndpoint22VariableCache.cache1100 values1100 bound1100 ((annotated52.frontier 3).getD 6 annotated52)=true := by decide +kernel
  exact ThreeBoundEndpoint22Packed.Tree.strictCachedCheck_sound deny1100 3 ThreeBoundEndpoint22VariableCache.cache1100
    values1100 bound1100 ThreeBoundEndpoint22VariableCache.cache1100_valid ((annotated52.frontier 3).getD 6 annotated52) h

theorem bulk_1100_52_3_7 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny1100 3 values1100 bound1100 ((annotated52.frontier 3).getD 7 annotated52)=true := by
  have h : ThreeBoundEndpoint22Packed.Tree.strictCachedCheck deny1100 ThreeBoundEndpoint22VariableCache.cache1100 values1100 bound1100 ((annotated52.frontier 3).getD 7 annotated52)=true := by decide +kernel
  exact ThreeBoundEndpoint22Packed.Tree.strictCachedCheck_sound deny1100 3 ThreeBoundEndpoint22VariableCache.cache1100
    values1100 bound1100 ThreeBoundEndpoint22VariableCache.cache1100_valid ((annotated52.frontier 3).getD 7 annotated52) h

theorem bulk_block_1100_52 : ThreeBoundEndpoint22Packed.Tree.fastCheck deny1100 3 values1100 bound1100 annotated52=true := by
  apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
  ·
    exact bulk_1100_52_1_0
  ·
    apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
    ·
      exact bulk_1100_52_2_2
    ·
      apply ThreeBoundEndpoint22Packed.Tree.fastCheck_branch
      ·
        exact bulk_1100_52_3_6
      ·
        exact bulk_1100_52_3_7

end ThreeBoundMinmaxNumeric.Endpoint22

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundEndpoint22Packed.Tree.fastCheck
    Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.deny1100
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.values1100
    Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.bound1100
    Sensitivity213981Formal.ThreeBoundEndpoint22Records.annotated52)
  Bool.true := @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.bulk_block_1100_52
