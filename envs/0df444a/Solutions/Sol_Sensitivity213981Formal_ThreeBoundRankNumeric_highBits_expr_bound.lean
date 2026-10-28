-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundRankNumeric.highBits_expr_bound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:53:38.225696+00:00
-- url     : https://prove2.me/submissions/a28ec326-7b25-4e46-87c3-538a99a2a68f

import Definitions.Def_Sensitivity213981Formal_GlobalAccounting
import Definitions.Def_Sensitivity213981Formal_MinmaxPrefixCaps
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2RawExpressions
import Definitions.Def_Sensitivity213981Formal_RankCapData
import Definitions.Def_Sensitivity213981Formal_RankCostExpressions
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankNumeric_actual_kind_rankCost_bound


namespace Sensitivity213981Formal
section
/- Actual coordinate accounting: incoming arcs are deduplicated to child
positions, external arcs have residual multiplicity, and histograms are
derived identities. -/


set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace ThreeBoundAccounting
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped Classical BigOperators
noncomputable section
variable {V I K : Type} [Fintype V] [Fintype I] [Fintype K]

















theorem sum_grouped (H : Finset V) (tag : V → K) (f : K → ℕ) :
    (∑ v ∈ H, f (tag v)) = ∑ k, typeCount H tag k*f k := by
  classical
  simpa [typeCount, Finset.sum_const, nsmul_eq_mul] using
    (Finset.sum_fiberwise' H tag f).symm

theorem histogram_partition (H : Finset V) (tag : V → K) (inc : V → ℕ) (k : K) :
    hist H tag inc k 0+hist H tag inc k 1+hist H tag inc k 2 = typeCount H tag k := by
  let g : V → Fin 3 := fun v => ⟨min 2 (inc v),by omega⟩
  have hh := Finset.sum_card_fiberwise_eq_card_filter
    (H.filter fun v => tag v = k) (Finset.univ : Finset (Fin 3)) g
  simp only [Finset.mem_univ, Finset.filter_true] at hh
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ] at hh
  simpa [hist,typeCount,g,Finset.filter_filter,Fin.ext_iff,Nat.add_assoc] using hh

theorem histogram_zero (H : Finset V) (tag : V → K) (inc : V → ℕ) (k : K) :
    hist H tag inc k 0 = typeCount H tag k-hist H tag inc k 1-hist H tag inc k 2 := by
  have h := histogram_partition H tag inc k
  omega

theorem histogram_sum (H : Finset V) (tag : V → K) (inc : V → ℕ)
    (cost : K → ℕ → ℕ) :
    (∑ v ∈ H, cost (tag v) (min 2 (inc v))) =
      ∑ k, (hist H tag inc k 0*cost k 0+
        hist H tag inc k 1*cost k 1+hist H tag inc k 2*cost k 2) := by
  classical
  let g : V → K × Fin 3 := fun v => (tag v,⟨min 2 (inc v),by omega⟩)
  let f : K × Fin 3 → ℕ := fun z => cost z.1 z.2.val
  have hh := sum_grouped H g f
  rw [Fintype.sum_prod_type] at hh
  have hc : ∀ k,
      (∑ b : Fin 3, typeCount H g (k,b)*f (k,b)) =
      hist H tag inc k 0*cost k 0+hist H tag inc k 1*cost k 1+
        hist H tag inc k 2*cost k 2 := by
    intro k
    rw [Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ]
    simp [typeCount,hist,g,f,Prod.ext_iff,Fin.ext_iff,Nat.add_assoc]
  simpa only [g,f,hc] using hh

theorem histogram_weighted_bound (H : Finset V) (tag : V → K) (inc : V → ℕ)
    (sets : V → Finset I) (cost : K → ℕ → ℕ)
    (hcost : ∀ v ∈ H, (sets v).card ≤  cost (tag v) (min 2 (inc v))) :
    (H.biUnion sets).card ≤ 
      ∑ k, ((typeCount H tag k-hist H tag inc k 1-hist H tag inc k 2)*cost k 0+
        hist H tag inc k 1*cost k 1+hist H tag inc k 2*cost k 2) := by
  calc
    _ ≤  ∑ v ∈ H, (sets v).card := Finset.card_biUnion_le
    _ ≤  ∑ v ∈ H, cost (tag v) (min 2 (inc v)) := Finset.sum_le_sum hcost
    _ = _ := by rw [histogram_sum]; simp only [← histogram_zero]





variable {L : Type} [Preorder L]













end
end ThreeBoundAccounting




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Homogeneous arithmetic expressions for the exact sensitivity transfer.
Every operation is interpreted in Nat. In particular subtraction is truncated
subtraction, which commutes with multiplication by every natural scalar. -/


set_option autoImplicit false

namespace ThreeBoundNumeric
open ThreeBoundFullProfile
























theorem Expr.eval_sum {n : ℕ} (es : List (Expr n)) (v : Profile n) :
    (Expr.sum es).eval v = (es.map (fun e=>e.eval v)).sum := by
  induction es with
  | nil => rfl
  | cons e es ih => simpa only [Expr.sum,List.foldr_cons,Expr.eval,List.map_cons,
      List.sum_cons] using congrArg (fun z=>e.eval v+z) ih

















end ThreeBoundNumeric



end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Symbolic transcription of graded2_union_recurrence.py, with the ordinary
q=1, three-positive cap corrected to marked[6]+2, the established general
bound. This correction changes no coordinate of the first endpoint's four
numerical phases, because every ordinary q=1 fallback there is absent.
The formulas are homogeneous natural arithmetic expressions. This module
defines the numeric raw transfer; its semantic raw-A/M/P/D obligations are
separate theorems about the actual Boolean parent. -/


set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace ThreeBoundNumeric
open ThreeBoundFullProfile








@[simp] theorem eval_add {n : ℕ} (v : Profile n) (a b : Expr n) :
    (a+b).eval v = a.eval v+b.eval v := rfl

@[simp] theorem eval_mul {n : ℕ} (v : Profile n) (k : ℕ) (a : Expr n) :
    (k*a).eval v = k*a.eval v := rfl







































































end ThreeBoundNumeric



end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- A homogeneous rank transfer expression over q3 count records.
Converted arcs use the proved lower-target guard cost. -/


set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

namespace ThreeBoundRankNumeric
open ThreeBoundNumeric ThreeBoundFullProfile
open scoped BigOperators











theorem highExpr_eval {n : ℕ} (a c : Entry) (r : Record) (v : Profile n) :
    (highExpr n a c r).eval v = ∑ k : Fin 11,
      ((r k.val-r (12+2*k.val)-r (13+2*k.val))*(rankCost n a c k 0).eval v+
        r (12+2*k.val)*(rankCost n a c k 1).eval v+
        r (13+2*k.val)*(rankCost n a c k 2).eval v) := by
  simp only [highExpr,Expr.eval_sum,List.map_ofFn,List.sum_ofFn,Function.comp_apply,eval_add,eval_mul]



end ThreeBoundRankNumeric



end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Actual high-head rank costs aggregated by exact type/hit histograms. -/


set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000

namespace ThreeBoundRankNumeric
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxCandidates ThreeBoundMinmaxCover
open ThreeBoundHeadCharge (headBits)
open ThreeBoundMinmaxNumeric (EntryMatch)
open ThreeBoundNumeric ThreeBoundFullProfile
open scoped Classical BigOperators
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

theorem highBits_expr_bound
    (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (a c : Entry) (matchE : EntryMatch S F i j P a c)
    (v : Profile n) (hv : Upper F v) (x : ((V × Bool) × I) → Bool)
    (hoff : parent S F i x=false) (hQ : S.tolerance j ≤  3) (tag : V → Fin 11)
    (htag : ∀ w ∈ highHeads S F P.strongLower P.strongUpper j x,
      ThreeBoundHighTypes.OfKind 3
        (PositiveCandidate S F P.strongLower P.strongUpper j x w)
        (GuardCandidate S F P.strongLower P.strongUpper j x w) (tag w))
    (r : Record)
    (htypes : ∀ k : Fin 11, r k.val=ThreeBoundAccounting.typeCount
      (highHeads S F P.strongLower P.strongUpper j x) tag k)
    (hhist : ∀ (k : Fin 11) (h : Fin 2), r (12+2*k.val+h.val)=
      ((highHeads S F P.strongLower P.strongUpper j x).filter fun w => tag w=k ∧
        min 2 (incomingSources S F P.strongLower P.strongUpper j x w).card=h.val+1).card) :
    (highBits S F P.strongLower P.strongUpper j x).card ≤  (highExpr n a c r).eval v := by
  let H := highHeads S F P.strongLower P.strongUpper j x
  let inc := fun w => (incomingSources S F P.strongLower P.strongUpper j x w).card
  let sets := fun w => headBits w (actualHeadParts S F P.strongLower P.strongUpper j x w)
  let cost := fun k : Fin 11 => fun h => (rankCost n a c k h).eval v
  have hcost : ∀ w ∈ H, (sets w).card ≤  cost (tag w) (min 2 (inc w)) := by
    intro w hw
    exact (actual_kind_rankCost_bound S F hF i j P a c matchE v hv x hoff w hQ (tag w) (htag w hw)).2
  have hb := ThreeBoundAccounting.histogram_weighted_bound H tag inc sets cost hcost
  letI : DecidableEq ((V × Bool) × I) := fun a b => Classical.propDecidable (a=b)
  have heHigh : highBits S F P.strongLower P.strongUpper j x=H.biUnion sets := by
    ext bit
    simp only [highBits,H,sets,Finset.mem_biUnion]
  rw [heHigh]
  apply hb.trans_eq
  rw [highExpr_eval]
  apply Finset.sum_congr rfl
  intro k _
  have hh1 := hhist k 0
  have hh2 := hhist k 1
  have hindex : 12+2*k.val+1=13+2*k.val := by omega
  simp only [Fin.val_zero,Fin.val_one,Nat.add_zero,zero_add,hindex,Nat.reduceAdd] at hh1 hh2
  have ht0 : ThreeBoundAccounting.typeCount H tag k=r k.val := (htypes k).symm
  have ht1 : ThreeBoundAccounting.hist H tag inc k 1=r (12+2*k.val) := by
    unfold ThreeBoundAccounting.hist
    convert hh1.symm using 1 <;> congr 1 <;> ext w <;> simp [H,inc]
  have ht2 : ThreeBoundAccounting.hist H tag inc k 2=r (13+2*k.val) := by
    unfold ThreeBoundAccounting.hist
    convert hh2.symm using 1 <;> congr 1 <;> ext w <;> simp [H,inc]
  rw [ht0,ht1,ht2]



end
end ThreeBoundRankNumeric




end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {n : Nat} {I V : Type} [inst : Fintype.{0} I] [inst_1 : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested (Fin n) I
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) F)
  (i j : Fin n)
  (P :
    @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData (Fin n) I V
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j)
  (a c : Sensitivity213981Formal.ThreeBoundRankNumeric.Entry)
  (matchE : @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.EntryMatch n I V S F i j P a c)
  (v : Sensitivity213981Formal.ThreeBoundFullProfile.Profile n)
  (hv : @Sensitivity213981Formal.ThreeBoundFullProfile.Upper n I inst F v)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool)
  (hoff : @Eq.{1} Bool (@Sensitivity213981Formal.ThreeBoundWitness.parent (Fin n) I V inst_1 S F i x) Bool.false)
  (hQ :
    @LE.le.{0} Nat instLENat (@Sensitivity213981Formal.ThreeBoundWitness.Stage.tolerance (Fin n) I V S j)
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
  (tag : V → Fin (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
  (htag :
    ∀ (w : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
          (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads (Fin n) I V inst_1 S F
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
              (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
              (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
            j x)
          w →
        Sensitivity213981Formal.ThreeBoundHighTypes.OfKind (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.PositiveCandidate (Fin n) I V inst_1 S F
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
              (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
              (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
            j x w)
          (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.GuardCandidate (Fin n) I V inst_1 S F
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
              (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
              (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
            j x w)
          (tag w))
  (r : Sensitivity213981Formal.ThreeBoundRankNumeric.Record)
  (htypes :
    ∀ (k : Fin (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))),
      @Eq.{1} Nat (r (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))) k))
        (@Sensitivity213981Formal.ThreeBoundAccounting.typeCount V
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
          (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads (Fin n) I V inst_1 S F
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
              (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
              (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
            j x)
          tag k))
  (hhist :
    ∀ (k : Fin (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
      (h : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))),
      @Eq.{1} Nat
        (r
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))) k)))
            (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)))
        (@Finset.card.{0} V
          (@Finset.filter.{0} V
            (fun (w : V) =>
              And (@Eq.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))) (tag w) k)
                (@Eq.{1} Nat
                  (@Min.min.{0} Nat instMinNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@Finset.card.{0} V
                      (@Sensitivity213981Formal.ThreeBoundMinmaxCover.incomingSources (Fin n) I V inst_1 S F
                        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
                          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
                        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
                          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
                        j x w)))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (fun (a : V) =>
              @instDecidableAnd
                (@Eq.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))) (tag a) k)
                (@Eq.{1} Nat
                  (@Min.min.{0} Nat instMinNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@Finset.card.{0} V
                      (@Sensitivity213981Formal.ThreeBoundMinmaxCover.incomingSources (Fin n) I V inst_1 S F
                        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
                          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
                        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
                          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
                        j x a)))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))) (tag a) k)
                (instDecidableEqNat
                  (@Min.min.{0} Nat instMinNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@Finset.card.{0} V
                      (@Sensitivity213981Formal.ThreeBoundMinmaxCover.incomingSources (Fin n) I V inst_1 S F
                        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
                          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
                        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
                          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
                        j x a)))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads (Fin n) I V inst_1 S F
              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
                (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
                (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
              j x)))),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@Sensitivity213981Formal.ThreeBoundMinmaxCover.highBits (Fin n) I V inst inst_1 S F
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
        j x))
    (@Sensitivity213981Formal.ThreeBoundNumeric.Expr.eval n v
      (Sensitivity213981Formal.ThreeBoundRankNumeric.highExpr n a c r)) := @Sensitivity213981Formal.ThreeBoundRankNumeric.highBits_expr_bound
