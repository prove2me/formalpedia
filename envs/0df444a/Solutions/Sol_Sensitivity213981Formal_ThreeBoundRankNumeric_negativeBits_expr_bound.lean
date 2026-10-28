-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundRankNumeric.negativeBits_expr_bound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:32:45.367811+00:00
-- url     : https://prove2.me/submissions/3b1d1a6b-552f-4e09-8079-385441d4d3ab

import Definitions.Def_Sensitivity213981Formal_MinmaxNegative
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_NumericAdmissibility
import Definitions.Def_Sensitivity213981Formal_RankCapData
import Definitions.Def_Sensitivity213981Formal_RankConvertedCaps
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxCover_negativeBits_card_le
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankNumeric_negative_weighted


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
/- Semantic interpretation of interval maxima in the transfer formula. -/


set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ThreeBoundNumeric
open ThreeBoundProfiles ThreeBoundFullProfile





variable {n : ℕ} {I : Type} [Fintype I]

theorem aExpr_bound (F : Fin n → (I → Bool) → Bool) (v : Profile n)
    (hv : Upper F v) (i j : Fin n) (hij : i ≤  j) :
    ABound F i j ((aExpr n i.val j.val).eval v) := by
  simpa only [aExpr, dif_pos i.isLt, dif_pos j.isLt, Expr.eval] using hv (.a i j) hij









end ThreeBoundNumeric





end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ThreeBoundNumericOrder
open ThreeBoundNumeric ThreeBoundFullProfile

theorem a_antitone_right {n : ℕ} (v : Profile n) (hv : Ordered v)
    (i j k : Fin n) (hij : i ≤  j) (hjk : j ≤  k) : v (.a i k) ≤  v (.a i j) := by
  have aux : ∀ d : ℕ, ∀ k : Fin n, k.val = d →
      ∀ j : Fin n, i ≤  j → j ≤  k → v (.a i k) ≤  v (.a i j) := by
    intro d
    induction d with
    | zero =>
      intro k hk j hij hjk
      have he : k = j := Fin.ext (by omega)
      subst k
      exact le_rfl
    | succ d ih =>
      intro k hk j hij hjk
      by_cases he : k = j
      · subst k; exact le_rfl
      have hjk' : j <  k := lt_of_le_of_ne hjk (Ne.symm he)
      have hik : i <  k := lt_of_le_of_lt hij hjk'
      have hp : (prev k).val = d := by simp only [prev,Fin.val_mk]; omega
      have hjp : j ≤  prev k := by change j.val ≤  k.val-1; omega
      exact (hv i k hik).2.1.trans (ih (prev k) hp j hij hjp)
  exact aux k.val k rfl j hij hjk

theorem aExpr_antitone_right {n : ℕ} (v : Profile n) (hv : Ordered v)
    (i j k : Fin n) (hij : i ≤  j) (hjk : j ≤  k) :
    (aExpr n i.val k.val).eval v ≤  (aExpr n i.val j.val).eval v := by
  simpa only [aExpr,dif_pos i.isLt,dif_pos j.isLt,dif_pos k.isLt,Expr.eval]
    using a_antitone_right v hv i j k hij hjk

end ThreeBoundNumericOrder



end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Negative target repairs and cumulative tier allocation for min/max. -/


set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxCover
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxCandidates ThreeBoundMinmaxHeads
open scoped Classical BigOperators
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

theorem mem_targetPrefix_iff (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (q : ℕ) (w : V) :
    w ∈ targetPrefix S F t u j x q ↔
      targetAt S F t u j x w ∧ (failed S F j x w).card ≤  q := by
  simp only [targetPrefix,Finset.mem_filter,Finset.mem_univ,true_and,targetAt]
  constructor
  · rintro ⟨b,hb,ht⟩
    exact ⟨⟨b,ht⟩,ht.2.1.le.trans hb⟩
  · rintro ⟨⟨b,ht⟩,hc⟩
    exact ⟨b,by rw [← ht.2.1]; exact hc,ht⟩



theorem negative_prefix_eq (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (q : ℕ) :
    (negativeTargets S F t u j x).filter (fun v => (failed S F j x v).card ≤  q) =
      targetPrefix S F t u j x q \ highHeads S F t u j x := by
  ext w
  simp only [negativeTargets,Finset.mem_filter,Finset.mem_sdiff,mem_targetPrefix_iff]
  constructor
  · tauto
  · rintro ⟨⟨ht,hq⟩,hh⟩
    obtain ⟨b,hb⟩ := ht
    exact ⟨⟨⟨⟨b,hb⟩,hb.2.1.le.trans hb.1⟩,hh⟩,hq⟩

theorem negative_prefix_sum (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (q : ℕ) :
    (∑ b ∈ Finset.range (q+1), (negativeTier S F t u j x b).card) =
      (targetPrefix S F t u j x q \ highHeads S F t u j x).card := by
  have h := Finset.sum_card_fiberwise_eq_card_filter (negativeTargets S F t u j x)
    (Finset.range (q+1)) (fun v => (failed S F j x v).card)
  simp only [Finset.mem_range,Nat.lt_succ_iff] at h
  simpa only [negativeTier,negative_prefix_eq] using h





end
end ThreeBoundMinmaxCover



end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- The four-tier greedy expression bounds actual negative target repairs. -/


set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedSectionVars false

namespace ThreeBoundRankNumeric
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxCandidates ThreeBoundMinmaxCover
open ThreeBoundNumeric ThreeBoundFullProfile ThreeBoundNumericOrder
open ThreeBoundMinmaxNumeric (EntryMatch)
open scoped Classical BigOperators
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

theorem negativeExpr_eval (caps : Caps) (perfect : ℕ) (c : Entry)
    (r : Record) (e : ℕ) (v : Profile n) :
    (negativeExpr n caps perfect c r e).eval v=
      ((List.range (c.tolerance+1)).map fun k =>
        negativeCount caps perfect c.tolerance r e k*(aExpr n c.guard (c.lowerAt k)).eval v).sum := by
  rw [negativeExpr,Expr.eval_sum,List.map_map]
  rfl

theorem negativeBits_expr_bound (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (a c : Entry) (hm : EntryMatch S F i j P a c)
    (input : ((V × Bool) × I) → Bool) (hQ : S.tolerance j ≤  3)
    (v : Profile n) (hv : Upper F v) (hordered : Ordered v)
    (caps : Caps) (perfect : ℕ) (r : Record) (e : ℕ)
    (hprefix : ∀ k, k ≤  S.tolerance j →
      (negativePrefix S F P.strongLower P.strongUpper j input k).card ≤  convertedCap caps perfect r e k) :
    (negativeBits S F P.strongLower P.strongUpper j input).card ≤ 
      (negativeExpr n caps perfect c r e).eval v := by
  let cost := fun k => (aExpr n c.guard (c.lowerAt k)).eval v
  let count := fun k => (negativeTier S F P.strongLower P.strongUpper j input k).card
  have hb : ∀ k, k ≤  S.tolerance j → ABound F (S.guard j) (P.strongLower k) (cost k) := by
    intro k hk
    have h := aExpr_bound F v hv (S.guard j) (P.strongLower k) (P.guardTarget k hk)
    simpa only [hm.strongGuard,hm.strongLower k hk,cost] using h
  have hfirst := negativeBits_card_le S F hF i j P input cost hb
  have hp : ∀ k, k ≤  S.tolerance j → (∑ b ∈ Finset.range (k+1), count b) ≤  convertedCap caps perfect r e k := by
    intro k hk
    change (∑ b ∈ Finset.range (k+1), (negativeTier S F P.strongLower P.strongUpper j input b).card) ≤  _
    rw [negative_prefix_sum]
    exact hprefix k hk
  have ha : ∀ k, k+1 ≤  S.tolerance j → cost (k+1) ≤  cost k := by
    intro k hk
    have hk' : k ≤  S.tolerance j := by omega
    have h := aExpr_antitone_right v hordered (S.guard j) (P.strongLower k) (P.strongLower (k+1))
      (P.guardTarget k hk') (P.strongLowerMono (by omega))
    simpa only [hm.strongGuard,hm.strongLower k hk',hm.strongLower (k+1) hk,cost] using h
  have hsecond := negative_weighted caps perfect r e (S.tolerance j) hQ count cost hp ha
  have h := hfirst.trans hsecond
  rw [hm.strongTolerance] at h
  rw [negativeExpr_eval]
  exact h

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
  (hm : @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.EntryMatch n I V S F i j P a c)
  (input : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool)
  (hQ :
    @LE.le.{0} Nat instLENat (@Sensitivity213981Formal.ThreeBoundWitness.Stage.tolerance (Fin n) I V S j)
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
  (v : Sensitivity213981Formal.ThreeBoundFullProfile.Profile n)
  (hv : @Sensitivity213981Formal.ThreeBoundFullProfile.Upper n I inst F v)
  (hordered : @Sensitivity213981Formal.ThreeBoundNumeric.Ordered n v)
  (caps : Sensitivity213981Formal.ThreeBoundNumeric.Caps) (perfect : Nat)
  (r : Sensitivity213981Formal.ThreeBoundRankNumeric.Record) (e : Nat)
  (hprefix :
    ∀ (k : Nat),
      @LE.le.{0} Nat instLENat k (@Sensitivity213981Formal.ThreeBoundWitness.Stage.tolerance (Fin n) I V S j) →
        @LE.le.{0} Nat instLENat
          (@Finset.card.{0} V
            (@Sensitivity213981Formal.ThreeBoundRankNumeric.negativePrefix n I V inst_1 S F
              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
                (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
                (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
              j input k))
          (Sensitivity213981Formal.ThreeBoundRankNumeric.convertedCap caps perfect r e k)),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@Sensitivity213981Formal.ThreeBoundMinmaxCover.negativeBits (Fin n) I V inst inst_1 S F
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
        j input))
    (@Sensitivity213981Formal.ThreeBoundNumeric.Expr.eval n v
      (Sensitivity213981Formal.ThreeBoundRankNumeric.negativeExpr n caps perfect c r e)) := @Sensitivity213981Formal.ThreeBoundRankNumeric.negativeBits_expr_bound
