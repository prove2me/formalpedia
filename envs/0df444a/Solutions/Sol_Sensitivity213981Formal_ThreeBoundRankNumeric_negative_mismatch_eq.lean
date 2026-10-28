-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundRankNumeric.negative_mismatch_eq
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:33:31.415012+00:00
-- url     : https://prove2.me/submissions/3b65cb5c-3a19-4095-a46e-c9c2d3e4aa57

import Definitions.Def_Sensitivity213981Formal_MinmaxCandidates
import Definitions.Def_Sensitivity213981Formal_MinmaxPrefixCaps
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankConvertedCaps
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxCandidates_negative_guard_false


namespace Sensitivity213981Formal
section
/- Actual geometric target and guard candidates for monotone min/max rows. -/


set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxCandidates
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive ThreeBoundRepair
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxHeads
open scoped Classical BigOperators
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]





















theorem target_some_guard (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
    (w : V) (b : ℕ) (hb : TargetCandidate S F P.strongLower P.strongUpper j x w b) :
    F (S.guard j) (child x w false)=true ∨ F (S.guard j) (child x w true)=true :=
  hb.2.2.2.elim (fun hh => Or.inl (hF _ _ (P.guardTarget b hb.1) _ hh))
    (fun hh => Or.inr (hF _ _ (P.guardTarget b hb.1) _ hh))

theorem target_partner_guard (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
    (w : V) (b : ℕ) (hb : TargetCandidate S F P.strongLower P.strongUpper j x w b)
    (c : Bool) (hc : c ≠ missing S F j x w) : F (S.guard j) (child x w c)=true := by
  have hh := target_some_guard S F hF i j P x w b hb
  unfold missing at hc
  cases c <;> split_ifs at hc with he <;> simp_all











end
end ThreeBoundMinmaxCandidates





end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Candidate prefix caps for symmetric min/max targets. -/


set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxCaps
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxCandidates ThreeBoundPrefixCaps

open scoped Classical BigOperators
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

theorem prefix_partner (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (q : ℕ) (w : V)
    (hw : w ∈ targetPrefix S F P.strongLower P.strongUpper j x q)
    (c : Bool) (hc : c ≠ missing S F j x w) :
    F (S.guard j) (child x w c)=true := by
  obtain ⟨b,hb,ht⟩ := (Finset.mem_filter.mp hw).2
  exact target_partner_guard S F hF i j P x w b ht c hc
















end
end ThreeBoundMinmaxCaps



end
end Sensitivity213981Formal

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







/-- A mismatch into a negative head is precisely the external guard failure
that lands there; no cost or counting approximation enters this identity. -/
theorem negative_mismatch_eq (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool) (v : V) :
    mismatch S.Adj S.label (negativeTargets S F P.strongLower P.strongUpper j x)
      (missing S F j x) v =
      ThreeBoundAccounting.externalHeads S F j x (highHeads S F P.strongLower P.strongUpper j x) v ∩
        negativeTargets S F P.strongLower P.strongUpper j x := by
  ext w
  constructor
  · intro hw
    obtain ⟨hn,hadj,hne⟩ := Finset.mem_filter.mp hw
    have hprefix := (Finset.mem_sdiff.mp hn).1
    have htrue := prefix_partner S F hF i j P x (S.tolerance j) w hprefix (S.label v w) hne
    exact Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hadj,htrue⟩,(Finset.mem_sdiff.mp hn).2⟩,hn⟩
  · intro hw
    obtain ⟨hext,hn⟩ := Finset.mem_inter.mp hw
    obtain ⟨_,hadj,htrue⟩ := Finset.mem_filter.mp (Finset.mem_sdiff.mp hext).1
    refine Finset.mem_filter.mpr ⟨hn,hadj,?_⟩
    intro hcolor
    rw [hcolor,negative_guard_false S F hF i j P x w hn] at htrue
    contradiction













end
end ThreeBoundRankNumeric






end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {n : Nat} {I V : Type} [Fintype.{0} I] [inst : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested (Fin n) I
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) F)
  (i j : Fin n)
  (P :
    @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData (Fin n) I V
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (v : V),
  @Eq.{1} (Finset.{0} V)
    (@Sensitivity213981Formal.CandidateCoherence.mismatch V
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj (Fin n) I V S)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label (Fin n) I V S)
      (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.negativeTargets (Fin n) I V inst S F
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
        j x)
      (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.missing (Fin n) I V S F j x) v)
    (@Inter.inter.{0} (Finset.{0} V) (@Finset.instInter.{0} V fun (a b : V) => Classical.propDecidable (@Eq.{1} V a b))
      (@Sensitivity213981Formal.ThreeBoundAccounting.externalHeads V I inst (Fin n) S F j x
        (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads (Fin n) I V inst S F
          (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
            (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
          (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
            (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
          j x)
        v)
      (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.negativeTargets (Fin n) I V inst S F
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
        j x)) := @Sensitivity213981Formal.ThreeBoundRankNumeric.negative_mismatch_eq
