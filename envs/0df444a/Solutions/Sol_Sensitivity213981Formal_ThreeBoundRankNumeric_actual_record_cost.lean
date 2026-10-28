-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundRankNumeric.actual_record_cost
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:56:21.3013+00:00
-- url     : https://prove2.me/submissions/52998158-6ddd-466b-a031-ef5429fe456c

import Definitions.Def_Sensitivity213981Formal_GlobalAccounting
import Definitions.Def_Sensitivity213981Formal_GradedCandidates
import Definitions.Def_Sensitivity213981Formal_HeadCostExpressions
import Definitions.Def_Sensitivity213981Formal_MinmaxCandidates
import Definitions.Def_Sensitivity213981Formal_MinmaxNegative
import Definitions.Def_Sensitivity213981Formal_MinmaxPairData
import Definitions.Def_Sensitivity213981Formal_MinmaxPrefixCaps
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2EnumerationBridge
import Definitions.Def_Sensitivity213981Formal_Q2RawExpressions
import Definitions.Def_Sensitivity213981Formal_Q3Enumeration
import Definitions.Def_Sensitivity213981Formal_Q3RecordFields
import Definitions.Def_Sensitivity213981Formal_RankCapData
import Definitions.Def_Sensitivity213981Formal_RankConvertedCaps
import Definitions.Def_Sensitivity213981Formal_RankCostExpressions
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxCandidates_actual_high_tags
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxCover_upward_subset
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxQ3_actual_record_exists
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxTransfer_strong_false_of_weak_false
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundQ3ActualRecordFields_all_record_fields
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankNumeric_actual_capPrefix
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankNumeric_actual_external_split_bound
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankNumeric_actual_recordAllowed
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankNumeric_convertedCap_from_prefix
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankNumeric_guardSources_eq_filter
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankNumeric_highBits_expr_bound
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankNumeric_kind_target_prefix_iff
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankNumeric_negativeBits_expr_bound


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













variable {L : Type} [Preorder L]



theorem failed_inter_high (S : Stage L I V) (F : L → (I → Bool) → Bool) (j : L)
    (x : ((V × Bool) × I) → Bool) (H : Finset V)
    (hH : ∀ w ∈ H, ∀ c : Bool, F (S.guard j) (child x w c) = true) (v : V) :
    failed S F j x v ∩ H = H.filter (S.Adj v) := by
  ext w
  simp only [Finset.mem_inter,failed,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · exact fun h => ⟨h.2,h.1.1⟩
  · exact fun h => ⟨⟨h.2,hH w h.1 (S.label v w)⟩,h.1⟩

theorem externalHeads_card (S : Stage L I V) (F : L → (I → Bool) → Bool) (j : L)
    (x : ((V × Bool) × I) → Bool) (H : Finset V)
    (hH : ∀ w ∈ H, ∀ c : Bool, F (S.guard j) (child x w c) = true) (v : V) :
    (externalHeads S F j x H v).card =
      (failed S F j x v).card-(H.filter (S.Adj v)).card := by
  unfold externalHeads
  have hh := Finset.card_sdiff_add_card_inter (failed S F j x v) H
  rw [failed_inter_high S F j x H hH v] at hh
  omega





theorem union_cover_bound (U high negative external : Finset I) (h n e : ℕ)
    (hcover : U ⊆ high ∪ negative ∪ external)
    (hh : high.card ≤  h) (hn : negative.card ≤  n) (he : external.card ≤  e) :
    U.card ≤  h+n+e := by
  calc
    _ ≤  (high ∪ negative ∪ external).card := Finset.card_le_card hcover
    _ ≤  (high ∪ negative).card+external.card := Finset.card_union_le _ _
    _ ≤  high.card+negative.card+external.card :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤  _ := Nat.add_le_add (Nat.add_le_add hh hn) he

end
end ThreeBoundAccounting




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ThreeBoundTypeCounts
open ThreeBoundAccounting
open scoped Classical BigOperators
noncomputable section
variable {V K : Type} [Fintype V] [Fintype K]

theorem card_filter_tag (H : Finset V) (tag : V → K) (p : K → Prop) :
    (H.filter fun v => p (tag v)).card =
      ∑ k, if p k then typeCount H tag k else 0 := by
  classical
  have hh := sum_grouped H tag (fun k => if p k then 1 else 0)
  simp only [mul_ite,mul_one,mul_zero] at hh
  rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  exact hh







end
end ThreeBoundTypeCounts

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Shared actual-predicate interface for symmetric min/max transfer. -/


set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxTransfer
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional
open scoped Classical
noncomputable section
variable {L I V : Type} [Preorder L] [Fintype I] [Fintype V]



theorem mm_true (F : L → (I → Bool) → Bool) (t u : L) (x y : I → Bool) :
    mm F t u x y=true ↔ F t x=true ∧ F t y=true ∧ (F u x=true ∨ F u y=true) := by
  simp only [mm,Bool.and_eq_true,Bool.or_eq_true,and_assoc]















end
end ThreeBoundMinmaxTransfer




end
end Sensitivity213981Formal

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



















theorem high_guards_true (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
    (w : V) (hw : w ∈ highHeads S F P.strongLower P.strongUpper j x) :
    ∀ c, F (S.guard j) (child x w c)=true := by
  rcases (Finset.mem_filter.mp hw).2 with ⟨b,hb⟩ | ⟨b,hb⟩
  · exact hb.2
  · have hh := (mm_true F _ _ _ _).1 hb.2.2
    intro c
    cases c
    · exact hF _ _ (P.guardTarget b hb.1) _ hh.1
    · exact hF _ _ (P.guardTarget b hb.1) _ hh.2.1















end
end ThreeBoundMinmaxCandidates





end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Exact eleven-kind prefix identities for actual min/max candidates. -/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundRankNumeric
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxCandidates ThreeBoundMinmaxCaps
open ThreeBoundAccounting ThreeBoundTypeCounts
open scoped Classical BigOperators
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]



theorem prefix_high_eq
    (S : Stage L I V) (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
    (hQ : S.tolerance j ≤  3) (tag : V → Fin 11)
    (hk : ∀ w ∈ highHeads S F P.strongLower P.strongUpper j x,
      ThreeBoundHighTypes.OfKind 3
        (PositiveCandidate S F P.strongLower P.strongUpper j x w)
        (GuardCandidate S F P.strongLower P.strongUpper j x w) (tag w)) (q : ℕ) :
    targetPrefix S F P.strongLower P.strongUpper j x q ∩
        highHeads S F P.strongLower P.strongUpper j x =
      (highHeads S F P.strongLower P.strongUpper j x).filter
        fun w => ThreeBoundHighTypes.positivePrefix 3 q (tag w)=true := by
  ext w
  simp only [Finset.mem_inter,Finset.mem_filter]
  constructor
  · rintro ⟨ht,hh⟩
    exact ⟨hh,(kind_target_prefix_iff S F hF i j P x hQ w (tag w) (hk w hh) q).1 ht⟩
  · rintro ⟨hh,ht⟩
    exact ⟨(kind_target_prefix_iff S F hF i j P x hQ w (tag w) (hk w hh) q).2 ht,hh⟩














theorem positivePrefix_card (H : Finset V) (tag : V → Fin 11) (r : Record)
    (hx : ∀ k : Fin 11, r k.val=typeCount H tag k) (q : ℕ) :
    positivePrefix r q = (H.filter fun w => ThreeBoundHighTypes.positivePrefix 3 q (tag w)=true).card := by
  have he := card_filter_tag H tag (fun k => ThreeBoundHighTypes.positivePrefix 3 q k=true)
  unfold positivePrefix
  simp only [hx]
  convert he.symm using 1 <;> congr 1 <;> ext w <;> simp

theorem guardCount_card (H : Finset V) (tag : V → Fin 11) (r : Record)
    (hx : ∀ k : Fin 11, r k.val=typeCount H tag k)  :
    guardCount r = (H.filter fun w => ThreeBoundHighTypes.isGuard 3 (tag w)=true).card := by
  have he := card_filter_tag H tag (fun k => ThreeBoundHighTypes.isGuard 3 k=true)
  unfold guardCount
  simp only [hx]
  convert he.symm using 1 <;> congr 1 <;> ext w <;> simp


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



theorem actual_convertedCap (S : Stage (Fin n) I V)
    (hR : TournamentHighRows.IsTournament S.Adj)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (input : ((V × Bool) × I) → Bool)
    (hQ : S.tolerance j ≤  3) (tag : V → Fin 11)
    (hk : ∀ w ∈ highHeads S F P.strongLower P.strongUpper j input,
      ThreeBoundHighTypes.OfKind 3
        (PositiveCandidate S F P.strongLower P.strongUpper j input w)
        (GuardCandidate S F P.strongLower P.strongUpper j input w) (tag w))
    (hc : ∀ w ∈ highHeads S F P.strongLower P.strongUpper j input,
      (failed S F j input w).card = ThreeBoundHighTypes.budget 3 (tag w))
    (caps : Caps) (perfect : ℕ) (hcap : CapsSound S.Adj S.label caps perfect) (r : Record)
    (hx : ∀ k : Fin 11, r k.val=typeCount (highHeads S F P.strongLower P.strongUpper j input) tag k)
    (hrs : ∀ k : Fin 7, k.val+1 ≤  (highHeads S F P.strongLower P.strongUpper j input).card →
      r (34+k.val)=residualPrefix S F P.strongLower P.strongUpper j input (k.val+1))
    (q : ℕ) (hq : q ≤  3) :
    (negativePrefix S F P.strongLower P.strongUpper j input q).card ≤ 
      convertedCap caps perfect r (convertedCount S F P.strongLower P.strongUpper j input) q := by
  let H := highHeads S F P.strongLower P.strongUpper j input
  have hg : guardCount r=(guardSources S F P.strongLower P.strongUpper j input).card :=
    (guardCount_card H tag r hx).trans
      (congrArg Finset.card (guardSources_eq_filter S F i j P input hQ tag hk).symm)
  have hp : positivePrefix r q=(targetPrefix S F P.strongLower P.strongUpper j input q ∩ H).card :=
    (positivePrefix_card H tag r hx q).trans
      (congrArg Finset.card (prefix_high_eq S F hF i j P input hQ tag hk q).symm)
  exact convertedCap_from_prefix S hR F hF i j P input hQ caps perfect hcap r q hq hg hp
    (actual_capPrefix S hR F hF i j P input hQ tag hk hc caps perfect hcap r hx hrs q hq)

end
end ThreeBoundRankNumeric




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Complete actual q0--q3 rank upward transfer. Every numerical record
field, prefix constraint, rank charge, and converted arc is justified by
the Boolean parent construction. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundRankNumeric
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxCandidates ThreeBoundMinmaxCover
open ThreeBoundMinmaxNumeric (EntryMatch)
open ThreeBoundNumeric ThreeBoundFullProfile
open scoped Classical BigOperators
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

theorem convertedCount_le_total (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (input : ((V × Bool) × I) → Bool) :
    convertedCount S F P.strongLower P.strongUpper j input ≤ 
      ∑ w ∈ guardSources S F P.strongLower P.strongUpper j input,
        ((failed S F j input w).card-
          ((highHeads S F P.strongLower P.strongUpper j input).filter (S.Adj w)).card) := by
  unfold convertedCount
  apply Finset.sum_le_sum
  intro w _
  exact (Finset.card_le_card Finset.inter_subset_left).trans_eq
    (ThreeBoundAccounting.externalHeads_card S F j input _ (high_guards_true S F hF i j P input) w)

theorem actual_record_cost (S : Stage (Fin n) I V)
    (hR : TournamentHighRows.IsTournament S.Adj)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (a c : Entry) (matchE : EntryMatch S F i j P a c)
    (input : ((V × Bool) × I) → Bool) (hoff : parent S F i input=false)
    (hQ : S.tolerance j ≤  3) (caps : Caps) (perfect : ℕ)
    (hcaps : CapsSound S.Adj S.label caps perfect)
    (v : Profile n) (hv : Upper F v) (hordered : Ordered v) :
    ∃ xs ∈ ThreeBoundQ3.records, ∃ e : ℕ,
      e ≤  recordOfList xs 11 ∧ recordAllowed n caps a c (recordOfList xs)=true ∧
      (flipsTo (parent S F j) true input).card ≤ 
        (recordCost n caps perfect a c (recordOfList xs) e).eval v := by
  obtain ⟨tag,htag,hcount,hout⟩ := actual_high_tags S F hF i j P input 3 hQ
  obtain ⟨ts,ds,num,hsort,hget,hdirs,hmem⟩ :=
    ThreeBoundMinmaxQ3.actual_record_exists S hR F hF i j P input hQ tag htag hout
  let H := highHeads S F P.strongLower P.strongUpper j input
  let G := guardSources S F P.strongLower P.strongUpper j input
  let r := recordOfList (ThreeBoundQ3.record (ts,ds))
  let converted := convertedCount S F P.strongLower P.strongUpper j input
  have hG : G=H.filter fun w => ThreeBoundQ3.isGuard (tag w)=true :=
    guardSources_eq_filter S F i j P input hQ tag htag
  obtain ⟨htypes,hext,hhist,hrs⟩ := ThreeBoundQ3ActualRecordFields.all_record_fields
    ts ds H G tag S.Adj hR num hget hdirs hG (fun w => (failed S F j input w).card) hcount
  have hx : ∀ kind : Fin 11, r kind.val=ThreeBoundAccounting.typeCount H tag kind := by
    intro kind
    unfold ThreeBoundAccounting.typeCount
    convert htypes kind using 1 <;> congr 1 <;> ext w <;> simp [H]
  have hres : ∀ k : Fin 7, k.val+1 ≤  H.card →
      r (34+k.val)=ThreeBoundMinmaxCaps.residualPrefix S F P.strongLower P.strongUpper j input (k.val+1) := by
    intro k hk
    exact hrs k hk
  have hprefix (q : ℕ) (hq : q ≤  3) :
      (targetPrefix S F P.strongLower P.strongUpper j input q).card ≤  capPrefix caps r q :=
    actual_capPrefix S hR F hF i j P input hQ tag htag hcount caps perfect hcaps r hx hres q hq
  have hpos (q : ℕ) : positivePrefix r q=
      (targetPrefix S F P.strongLower P.strongUpper j input q ∩ H).card :=
    (positivePrefix_card H tag r hx q).trans
      (congrArg Finset.card (prefix_high_eq S F hF i j P input hQ tag htag q).symm)
  have hallowed : recordAllowed n caps a c r=true := by
    apply actual_recordAllowed S F hF i j P a c matchE v hv input hoff hQ tag htag caps r hx
    intro q hq
    have hq3 : q ≤  3 := by rw [← matchE.strongTolerance] at hq; omega
    rw [hpos q]
    exact (Finset.card_le_card Finset.inter_subset_left).trans (hprefix q hq3)
  have hconverted : ∀ q, q ≤  S.tolerance j →
      (negativePrefix S F P.strongLower P.strongUpper j input q).card ≤  convertedCap caps perfect r converted q := by
    intro q hq
    exact actual_convertedCap S hR F hF i j P input hQ tag htag hcount caps perfect hcaps r hx hres q (hq.trans hQ)
  have hnegative := negativeBits_expr_bound S F hF i j P a c matchE input hQ v hv hordered
    caps perfect r converted hconverted
  have hhigh := highBits_expr_bound S F hF i j P a c matchE v hv input hoff hQ tag htag r hx
    (by
      intro kind hits
      convert hhist kind hits using 1 <;> congr 1 <;> ext w <;> simp [H,G,incomingSources])
  have hexternal := actual_external_split_bound S F hF i j P a c matchE v hv input hoff
  dsimp only at hexternal
  rw [← hext] at hexternal
  have hconvle := convertedCount_le_total S F hF i j P input
  rw [← hext] at hconvle
  have hcover := upward_subset S F hF i j P input
    (strong_false_of_weak_false S F hF i j P input hoff)
  have htotal := ThreeBoundAccounting.union_cover_bound
    (flipsTo (parent S F j) true input) (negativeBits S F P.strongLower P.strongUpper j input)
    (highBits S F P.strongLower P.strongUpper j input)
    (ThreeBoundMinmaxCover.externalBits S F P.strongLower P.strongUpper j input)
    _ _ _ (by
      intro bit hb
      have hh := hcover hb
      simpa only [Finset.mem_union] using hh) hnegative hhigh hexternal
  refine ⟨ThreeBoundQ3.record (ts,ds),hmem,converted,hconvle,hallowed,?_⟩
  change _ ≤  (r 11-converted)*(bExpr n c.guard a.guard).eval v+
    converted*(bExpr n c.guard (c.lowerAt 0)).eval v+
    (negativeExpr n caps perfect c r converted).eval v+(highExpr n a c r).eval v
  change _ ≤  (negativeExpr n caps perfect c r converted).eval v+(highExpr n a c r).eval v+
    (converted*(bExpr n c.guard (c.lowerAt 0)).eval v+
      (r 11-converted)*(bExpr n c.guard a.guard).eval v) at htotal
  omega



end
end ThreeBoundRankNumeric



end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {n : Nat} {I V : Type} [inst : Fintype.{0} I] [inst_1 : Fintype.{0} V]
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
  (a c : Sensitivity213981Formal.ThreeBoundRankNumeric.Entry)
  (matchE : @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.EntryMatch n I V S F i j P a c)
  (input : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool)
  (hoff : @Eq.{1} Bool (@Sensitivity213981Formal.ThreeBoundWitness.parent (Fin n) I V inst_1 S F i input) Bool.false)
  (hQ :
    @LE.le.{0} Nat instLENat (@Sensitivity213981Formal.ThreeBoundWitness.Stage.tolerance (Fin n) I V S j)
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
  (caps : Sensitivity213981Formal.ThreeBoundNumeric.Caps) (perfect : Nat)
  (hcaps :
    @Sensitivity213981Formal.ThreeBoundRankNumeric.CapsSound V inst_1
      (fun (a b : V) => Classical.propDecidable (@Eq.{1} V a b))
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj (Fin n) I V S)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label (Fin n) I V S) caps perfect)
  (v : Sensitivity213981Formal.ThreeBoundFullProfile.Profile n)
  (hv : @Sensitivity213981Formal.ThreeBoundFullProfile.Upper n I inst F v)
  (hordered : @Sensitivity213981Formal.ThreeBoundNumeric.Ordered n v),
  @Exists.{1} (List.{0} Nat) fun (xs : List.{0} Nat) =>
    And
      (@Membership.mem.{0, 0} (List.{0} Nat) (List.{0} (List.{0} Nat)) (@List.instMembership.{0} (List.{0} Nat))
        Sensitivity213981Formal.ThreeBoundQ3.records xs)
      (@Exists.{1} Nat fun (e : Nat) =>
        And
          (@LE.le.{0} Nat instLENat e
            (Sensitivity213981Formal.ThreeBoundNumeric.recordOfList xs
              (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))))
          (And
            (@Eq.{1} Bool
              (Sensitivity213981Formal.ThreeBoundRankNumeric.recordAllowed n caps a c
                (Sensitivity213981Formal.ThreeBoundNumeric.recordOfList xs))
              Bool.true)
            (@LE.le.{0} Nat instLENat
              (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
                (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
                  (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_1 Bool.fintype)
                    inst)
                  (@Sensitivity213981Formal.ThreeBoundWitness.parent (Fin n) I V inst_1 S F j) Bool.true input))
              (@Sensitivity213981Formal.ThreeBoundNumeric.Expr.eval n v
                (Sensitivity213981Formal.ThreeBoundRankNumeric.recordCost n caps perfect a c
                  (Sensitivity213981Formal.ThreeBoundNumeric.recordOfList xs) e))))) := @Sensitivity213981Formal.ThreeBoundRankNumeric.actual_record_cost
