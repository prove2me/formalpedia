-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundRankAnnotated.Tree.allPrepared_of_statics
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:55:12.750899+00:00
-- url     : https://prove2.me/submissions/512c1113-bff6-49cc-9595-b59a0b56b36e

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankAnnotatedTree
import Definitions.Def_Sensitivity213981Formal_RankConvertedPreparation
import Definitions.Def_Sensitivity213981Formal_RankStaticPreparation
import Definitions.Def_Sensitivity213981Formal_Supplement_NumericExpressions
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Records_staticKeyCode_staticEq


namespace Sensitivity213981Formal
section
/- Homogeneous arithmetic expressions for the exact sensitivity transfer.
Every operation is interpreted in Nat. In particular subtraction is truncated
subtraction, which commutes with multiplication by every natural scalar. -/


set_option autoImplicit false

namespace ThreeBoundNumeric
open ThreeBoundFullProfile






























theorem mem_interval {a b k : ℕ} : k ∈ interval a b ↔ a ≤  k ∧ k <  b := by
  simp only [interval, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i,hi,rfl⟩
    omega
  · rintro ⟨ha,hb⟩
    exact ⟨k-a,by omega,by omega⟩











end ThreeBoundNumeric



end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Cap and converted-negative preparation depends on only 19 static fields. -/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

namespace ThreeBoundRankCached
open ThreeBoundNumeric (Caps recordOfList)
open ThreeBoundRankNumeric
open scoped BigOperators

















theorem StaticEq.small {r s : Record} (h : StaticEq r s) (k : Fin 11) : r k.val=s k.val :=
  h.1 ⟨k.val,by omega⟩

theorem headCount_static {r s : Record} (h : StaticEq r s) : headCount r=headCount s := by
  simp only [headCount,h.small]

theorem guardCount_static {r s : Record} (h : StaticEq r s) : guardCount r=guardCount s := by
  simp only [guardCount,h.small]

theorem positivePrefix_static {r s : Record} (h : StaticEq r s) (q : ℕ) :
    positivePrefix r q=positivePrefix s q := by
  simp only [positivePrefix,h.small]

theorem lowCount_static {r s : Record} (h : StaticEq r s) (q : ℕ) : lowCount r q=lowCount s q := by
  simp only [lowCount,h.small]

theorem nextCount_static {r s : Record} (h : StaticEq r s) (q : ℕ) : nextCount r q=nextCount s q := by
  simp only [nextCount,h.small]

theorem eligibleCount_static {r s : Record} (h : StaticEq r s) (q : ℕ) :
    eligibleCount r q=eligibleCount s q := by
  simp only [eligibleCount,h.small]

theorem capPrefix_static (caps : Caps) {r s : Record} (h : StaticEq r s) (q : ℕ) :
    capPrefix caps r q=capPrefix caps s q := by
  have h34 : r 34=s 34 := h.2 (0 : Fin 7)
  have h35 : r 35=s 35 := h.2 (1 : Fin 7)
  have h36 : r 36=s 36 := h.2 (2 : Fin 7)
  have h37 : r 37=s 37 := h.2 (3 : Fin 7)
  have h38 : r 38=s 38 := h.2 (4 : Fin 7)
  have h39 : r 39=s 39 := h.2 (5 : Fin 7)
  have h40 : r 40=s 40 := h.2 (6 : Fin 7)
  simp only [capPrefix,headCount_static h,positivePrefix_static h,lowCount_static h,
    nextCount_static h,eligibleCount_static h,h34,h35,h36,h37,h38,h39,h40]

theorem convertedCap_static (caps : Caps) (perfect : ℕ) {r s : Record}
    (h : StaticEq r s) (e q : ℕ) :
    convertedCap caps perfect r e q=convertedCap caps perfect s e q := by
  simp only [convertedCap,capPrefix_static caps h,positivePrefix_static h,guardCount_static h]

theorem negativeCount_static (caps : Caps) (perfect q : ℕ) {r s : Record}
    (h : StaticEq r s) (e k : ℕ) :
    negativeCount caps perfect q r e k=negativeCount caps perfect q s e k := by
  simp only [negativeCount,suffixCapacity,convertedCap_static caps perfect h]

theorem staticAllowed_static (caps : Caps) (q : ℕ) {r s : Record} (h : StaticEq r s) :
    staticAllowed caps q r=staticAllowed caps q s := by
  simp only [staticAllowed,positivePrefix_static h,capPrefix_static caps h]



theorem preparedOK_static_iff (caps : Caps) (perfect q : ℕ) {r s : Record}
    (h : StaticEq r s) (p : PreparedValues) :
    PreparedOK caps perfect q r p ↔ PreparedOK caps perfect q s p := by
  have he : r 11=s 11 := h.1 (11 : Fin 12)
  simp only [PreparedOK,staticAllowed_static caps q h,negativeCount_static caps perfect q h]
  rw [he]

theorem preparedOK_of_static (caps : Caps) (perfect q : ℕ) {r s : Record}
    (h : StaticEq r s) (p : PreparedValues) (hp : PreparedOK caps perfect q s p) :
    PreparedOK caps perfect q r p := (preparedOK_static_iff caps perfect q h p).mpr hp



end ThreeBoundRankCached




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Each static record needs only four converted caps per external-arc count.
The q-specific greedy increments are then computed from these small arrays. -/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

namespace ThreeBoundRankCached
open ThreeBoundNumeric (Caps interval mem_interval)
open ThreeBoundRankNumeric

















theorem readNegative_preparedFromConverted (q external : ℕ) (values : ConvertedValues)
    (e : Fin (external+1)) (k : Fin (q+1)) :
    readNegative (preparedFromConverted q external values) e.val k.val=
      convertedNegative values q e.val k.val := by
  simp [readNegative,preparedFromConverted,Array.getD,e.isLt,k.isLt]

theorem convertedSuffix_eq (caps : Caps) (perfect : ℕ) (r : Record)
    (values : ConvertedValues) (hc : ConvertedOK caps perfect r values)
    (q : ℕ) (hq : q ≤  3) (e : Fin (r 11+1)) (k : ℕ) :
    convertedSuffix values q e.val k=suffixCapacity caps perfect q r e.val k := by
  have hqv : readConverted values e.val q=convertedCap caps perfect r e.val q :=
    hc.2 e ⟨q,by omega⟩
  have hm : (interval k (q+1)).map (fun j => readConverted values e.val j)=
      (interval k (q+1)).map (fun j => convertedCap caps perfect r e.val j) := by
    apply List.map_congr_left
    intro j hj
    have hjq := (mem_interval.mp hj).2
    exact hc.2 e ⟨j,by omega⟩
  simp only [convertedSuffix,suffixCapacity,hqv,hm]

theorem convertedNegative_eq (caps : Caps) (perfect : ℕ) (r : Record)
    (values : ConvertedValues) (hc : ConvertedOK caps perfect r values)
    (q : ℕ) (hq : q ≤  3) (e : Fin (r 11+1)) (k : ℕ) :
    convertedNegative values q e.val k=negativeCount caps perfect q r e.val k := by
  simp only [convertedNegative,negativeCount,convertedSuffix_eq caps perfect r values hc q hq e]

theorem preparedFromConverted_ok (caps : Caps) (perfect : ℕ) (r : Record)
    (values : ConvertedValues) (hc : ConvertedOK caps perfect r values) (q : ℕ) (hq : q ≤  3) :
    PreparedOK caps perfect q r (preparedFromConverted q (r 11) values) := by
  constructor
  · exact hc.1 ⟨q,by omega⟩
  · intro _ e k
    rw [readNegative_preparedFromConverted]
    exact convertedNegative_eq caps perfect r values hc q hq e k.val





theorem preparedFromConverted_of_static (caps : Caps) (perfect : ℕ) {r s : Record}
    (h : StaticEq r s) (values : ConvertedValues) (hc : ConvertedOK caps perfect s values)
    (q : ℕ) (hq : q ≤  3) :
    PreparedOK caps perfect q r (preparedFromConverted q (s 11) values) :=
  preparedOK_of_static caps perfect q h _ (preparedFromConverted_ok caps perfect s values hc q hq)

end ThreeBoundRankCached




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



































theorem Tree.allPrepared_of_statics (caps : Caps) (perfect : ℕ)
    (codes : ℕ → ℕ) (values : ℕ → ConvertedValues) (count q : ℕ) (hq : q≤ 3)
    (hkeys : ∀ key, key< count → ConvertedOK caps perfect (staticCodeRecord (codes key)) (values key))
    (t : Tree) (h : t.checkStatics codes count=true) :
    t.AllPrepared caps perfect q (prepared codes values q) := by
  induction t with
  | leaf bits key code =>
      obtain ⟨hk,hs⟩:=and_true h
      have he:staticKeyCode code=codes key:=of_decide_eq_true hs
      have hstatic:=staticKeyCode_staticEq code
      rw [he] at hstatic
      exact preparedFromConverted_of_static caps perfect hstatic (values key)
        (hkeys key (of_decide_eq_true hk)) q hq
  | branch bits pivot left right hl hr =>
      obtain ⟨hleft,hright⟩:=and_true h
      exact ⟨hl hleft,hr hright⟩

end ThreeBoundRankAnnotated


end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ (caps : Sensitivity213981Formal.ThreeBoundNumeric.Caps) (perfect : Nat) (codes : Nat → Nat)
  (values : Nat → Sensitivity213981Formal.ThreeBoundRankCached.ConvertedValues) (count q : Nat)
  (hq : @LE.le.{0} Nat instLENat q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
  (hkeys :
    ∀ (key : Nat),
      @LT.lt.{0} Nat instLTNat key count →
        Sensitivity213981Formal.ThreeBoundRankCached.ConvertedOK caps perfect
          (Sensitivity213981Formal.ThreeBoundEndpoint22Records.staticCodeRecord (codes key)) (values key))
  (t : Sensitivity213981Formal.ThreeBoundRankAnnotated.Tree)
  (h : @Eq.{1} Bool (Sensitivity213981Formal.ThreeBoundRankAnnotated.Tree.checkStatics codes count t) Bool.true),
  Sensitivity213981Formal.ThreeBoundRankAnnotated.Tree.AllPrepared caps perfect q
    (Sensitivity213981Formal.ThreeBoundRankAnnotated.prepared codes values q) t := @Sensitivity213981Formal.ThreeBoundRankAnnotated.Tree.allPrepared_of_statics
