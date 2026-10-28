-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundRankNumeric.convertedCap_from_prefix
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:53:02.912423+00:00
-- url     : https://prove2.me/submissions/372f6b05-67d7-457a-b06f-47b922116e86

import Definitions.Def_Sensitivity213981Formal_GlobalAccounting
import Definitions.Def_Sensitivity213981Formal_MinmaxPrefixCaps
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankCapData
import Definitions.Def_Sensitivity213981Formal_RankConvertedCaps
import Definitions.Def_Sensitivity213981Formal_ResidualCaps
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankNumeric_actual_dominator_converted_cap
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankNumeric_actual_marked_converted_cap
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankNumeric_convertedCap_bound


namespace Sensitivity213981Formal
section
/- Converted external failures give exact averaged marker budgets for the
negative target prefixes.  Every selected marker is an actual guard source. -/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000
set_option linter.unusedSectionVars false

namespace ThreeBoundRankNumeric
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxCandidates ThreeBoundMinmaxCaps
open ThreeBoundRankMarkers CandidateCoherence TournamentHighRows
open scoped Classical BigOperators
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]













theorem prefix_card_eq_high_add_negative (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (t u : ℕ → Fin n) (j : Fin n)
    (x : ((V × Bool) × I) → Bool) (q : ℕ) :
    (targetPrefix S F t u j x q).card =
      (targetPrefix S F t u j x q ∩ highHeads S F t u j x).card+
        (negativePrefix S F t u j x q).card := by
  have hh := Finset.card_sdiff_add_card_inter (targetPrefix S F t u j x q) (highHeads S F t u j x)
  dsimp only [negativePrefix]
  omega







end
end ThreeBoundRankNumeric






end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Exact converted-cap program semantics for the actual negative prefixes. -/


set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedSectionVars false

namespace ThreeBoundRankNumeric
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxCandidates ThreeBoundMinmaxCaps
open ThreeBoundAccounting ThreeBoundNumeric
open scoped Classical BigOperators
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

theorem convertedCap_from_prefix (S : Stage (Fin n) I V)
    (hR : TournamentHighRows.IsTournament S.Adj)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (input : ((V × Bool) × I) → Bool)
    (hQ : S.tolerance j ≤  3) (caps : Caps) (perfect : ℕ)
    (hcap : CapsSound S.Adj S.label caps perfect) (r : Record) (q : ℕ) (hq : q ≤  3)
    (hguard : guardCount r=(guardSources S F P.strongLower P.strongUpper j input).card)
    (hpos : positivePrefix r q=(targetPrefix S F P.strongLower P.strongUpper j input q ∩
      highHeads S F P.strongLower P.strongUpper j input).card)
    (hprefix : (targetPrefix S F P.strongLower P.strongUpper j input q).card ≤  capPrefix caps r q) :
    (negativePrefix S F P.strongLower P.strongUpper j input q).card ≤ 
      convertedCap caps perfect r (convertedCount S F P.strongLower P.strongUpper j input) q := by
  apply convertedCap_bound caps perfect r _ q _ hq
  · have hpart := prefix_card_eq_high_add_negative S F P.strongLower P.strongUpper j input q
    rw [← hpos] at hpart
    omega
  · intro hz hm
    subst q
    rw [hguard] at hm
    have hh := actual_dominator_converted_cap S hR F hF i j P input 1 (caps.pcross+1) hm hcap.source
    simpa only [hguard,Nat.add_sub_cancel] using hh
  · intro hz hm
    subst q
    rw [hguard] at hm
    have hh := actual_dominator_converted_cap S hR F hF i j P input 2 (Caps.at caps.zero 2+1) hm hcap.double
    simpa only [hguard,Nat.add_sub_cancel] using hh
  · intro hz hm
    subst q
    rw [hguard] at hm
    have hh := actual_dominator_converted_cap S hR F hF i j P input 3 (perfect+1) hm hcap.triple
    simpa only [hguard,Nat.add_sub_cancel] using hh
  · intro hz hm
    subst q
    rw [hguard] at hm
    have hh := actual_marked_converted_cap S hR F hF i j P input 1 3 _ hm (Or.inl (by omega)) hcap.zeroThree
    simpa only [hguard] using hh
  · intro hz hm
    subst q
    rw [hguard] at hm
    have hh := actual_marked_converted_cap S hR F hF i j P input 2 4 _ hm (Or.inl (by omega)) hcap.zeroFour
    simpa only [hguard] using hh
  · intro hz hm
    subst q
    rw [hguard] at hm
    have hh := actual_marked_converted_cap S hR F hF i j P input 3 5 _ hm (Or.inl (by omega)) hcap.zeroFive
    simpa only [hguard] using hh
  · intro hz hm
    subst q
    rw [hguard] at hm
    have hh := actual_marked_converted_cap S hR F hF i j P input 3 6 _ hm (Or.inr hQ) hcap.zeroSix
    simpa only [hguard] using hh
  · intro hz hm
    subst q
    rw [hguard] at hm
    have hh := actual_marked_converted_cap S hR F hF i j P input 3 7 _ hm (Or.inr hQ) hcap.zeroSeven
    simpa only [hguard] using hh



end
end ThreeBoundRankNumeric




end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {n : Nat} {I V : Type} [Fintype.{0} I] [inst : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage (Fin n) I V)
  (hR :
    @Sensitivity213981Formal.TournamentHighRows.IsTournament V
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj (Fin n) I V S))
  (F : Fin n → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested (Fin n) I
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) F)
  (i j : Fin n)
  (P :
    @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData (Fin n) I V
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j)
  (input : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool)
  (hQ :
    @LE.le.{0} Nat instLENat (@Sensitivity213981Formal.ThreeBoundWitness.Stage.tolerance (Fin n) I V S j)
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
  (caps : Sensitivity213981Formal.ThreeBoundNumeric.Caps) (perfect : Nat)
  (hcap :
    @Sensitivity213981Formal.ThreeBoundRankNumeric.CapsSound V inst
      (fun (a b : V) => Classical.propDecidable (@Eq.{1} V a b))
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj (Fin n) I V S)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label (Fin n) I V S) caps perfect)
  (r : Sensitivity213981Formal.ThreeBoundRankNumeric.Record) (q : Nat)
  (hq : @LE.le.{0} Nat instLENat q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
  (hguard :
    @Eq.{1} Nat (Sensitivity213981Formal.ThreeBoundRankNumeric.guardCount r)
      (@Finset.card.{0} V
        (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.guardSources (Fin n) I V inst S F
          (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
            (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
          (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
            (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
          j input)))
  (hpos :
    @Eq.{1} Nat (Sensitivity213981Formal.ThreeBoundRankNumeric.positivePrefix r q)
      (@Finset.card.{0} V
        (@Inter.inter.{0} (Finset.{0} V)
          (@Finset.instInter.{0} V fun (a b : V) => Classical.propDecidable (@Eq.{1} V a b))
          (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.targetPrefix (Fin n) I V inst S F
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
              (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
              (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
            j input q)
          (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads (Fin n) I V inst S F
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
              (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
              (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
            j input))))
  (hprefix :
    @LE.le.{0} Nat instLENat
      (@Finset.card.{0} V
        (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.targetPrefix (Fin n) I V inst S F
          (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
            (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
          (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
            (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
          j input q))
      (Sensitivity213981Formal.ThreeBoundRankNumeric.capPrefix caps r q)),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} V
      (@Sensitivity213981Formal.ThreeBoundRankNumeric.negativePrefix n I V inst S F
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
        j input q))
    (Sensitivity213981Formal.ThreeBoundRankNumeric.convertedCap caps perfect r
      (@Sensitivity213981Formal.ThreeBoundRankNumeric.convertedCount n I V inst S F
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
        j input)
      q) := @Sensitivity213981Formal.ThreeBoundRankNumeric.convertedCap_from_prefix
