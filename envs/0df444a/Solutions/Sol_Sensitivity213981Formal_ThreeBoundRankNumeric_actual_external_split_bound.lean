-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundRankNumeric.actual_external_split_bound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:33:24.980709+00:00
-- url     : https://prove2.me/submissions/15620c24-e373-4e8d-947a-e1e8c5fe055e

import Definitions.Def_Sensitivity213981Formal_GlobalAccounting
import Definitions.Def_Sensitivity213981Formal_MinmaxCandidates
import Definitions.Def_Sensitivity213981Formal_MinmaxPairData
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankExternalSplit
import Definitions.Def_Sensitivity213981Formal_Supplement_GradedPositiveBoundary
import Definitions.Def_Sensitivity213981Formal_Supplement_NumericExpressions
import Definitions.Def_Sensitivity213981Formal_WitnessLifting
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
/-
Common block and positive-sensitivity witnesses for a broad two-child
guarded construction. These are lower-bound witnesses; no upper sensitivity
transfer theorem is asserted here.
-/


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ThreeBoundWitness
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320

variable {L I V : Type}









theorem parent_true_iff [Fintype V] (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (l : L)
    (x : ((V × Bool) × I) → Bool) :
    parent S F l x = true ↔ ∃ v : V,
      (failed S F l x v).card ≤  S.tolerance l ∧
      S.target l (failed S F l x v).card (child x v false) (child x v true) = true := by
  classical
  simp [parent]















































/- Reindexing lemmas follow the accepted Apache-2.0 source by @yousofy:
   Sol_Paley11987Verified_CompactFiniteProfile11987_actual_seeds_of_label_and_certificate,
   together with Definitions.Def_Paley11987Support_053. -/










end ThreeBoundWitness








end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/-
Actual positive-boundary transfer for equal-target graded rows.
Every guard count and bit flip below uses the concrete guarded construction.
This is one part of the upper transfer, not a complete seed proof.
-/


set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false

namespace ThreeBoundPositive
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles
open scoped BigOperators Classical
noncomputable section

variable {L I V : Type} [Preorder L] [Fintype I] [Fintype V]





















@[simp] theorem card_liftBits (v : V) (c : Bool) (s : Finset I) :
    (liftBits v c s).card = s.card := Finset.card_map _

























end
end ThreeBoundPositive






end
end Sensitivity213981Formal

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







end
end ThreeBoundAccounting




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



theorem bExpr_bound (F : Fin n → (I → Bool) → Bool) (v : Profile n)
    (hv : Upper F v) (i j : Fin n) (hij : i ≤  j) :
    BBound F i j ((bExpr n i.val j.val).eval v) := by
  simpa only [bExpr, dif_pos i.isLt, dif_pos j.isLt, Expr.eval] using hv (.b i j) hij







end ThreeBoundNumeric





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



theorem mm_mono (F : L → (I → Bool) → Bool) (hF : Nested F)
    (ti ui tj uj : L) (ht : ti ≤  tj) (hu : ui ≤  uj) (x y : I → Bool)
    (h : mm F tj uj x y=true) : mm F ti ui x y=true := by
  rw [mm_true] at h ⊢
  exact ⟨hF _ _ ht _ h.1,hF _ _ ht _ h.2.1,
    h.2.2.elim (fun hh => Or.inl (hF _ _ hu _ hh)) (fun hh => Or.inr (hF _ _ hu _ hh))⟩



theorem parent_true_of_count (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (l : L) (t u : ℕ → L) (ht : Monotone t) (hu : Monotone u)
    (hdef : ∀ d a b, S.target l d a b=mm F (t d) (u d) a b)
    (x : ((V × Bool) × I) → Bool) (w : V) (d : ℕ)
    (hd : d ≤  S.tolerance l) (hc : (failed S F l x w).card ≤  d)
    (hm : mm F (t d) (u d) (child x w false) (child x w true)=true) : parent S F l x=true := by
  apply (parent_true_iff S F l x).2
  refine ⟨w,hc.trans hd,?_⟩
  rw [hdef]
  exact mm_mono F hF _ _ _ _ (ht hc) (hu hc) _ _ hm

theorem failed_weak_subset (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (w : V) : failed S F i x w ⊆ failed S F j x w := by
  intro z hz
  obtain ⟨_,hR,htrue⟩ := Finset.mem_filter.mp hz
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hR,hF _ _ P.guards _ htrue⟩





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









theorem guard_failures_eq (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
    (hoff : parent S F i x=false) (w : V) (b : ℕ)
    (hb : GuardCandidate S F P.strongLower P.strongUpper j x w b) :
    failed S F i x w=failed S F j x w := by
  have hs := failed_weak_subset S F hF i j P x w
  have hle := Finset.card_le_card hs
  have hnot : ¬ (failed S F i x w).card ≤  b := by
    intro hc
    have hmm := mm_mono F hF _ _ _ _ (P.lowerOrder b hb.1) (P.upperOrder b hb.1) _ _ hb.2.2
    have he := parent_true_of_count S F hF i P.weakLower P.weakUpper P.weakLowerMono P.weakUpperMono
      P.weakDef x w b (hb.1.trans P.tolerances) hc hmm
    rw [hoff] at he
    contradiction
  apply Finset.eq_of_subset_of_card_le hs
  have hd := hb.2.1
  omega

theorem guard_hit_eligible (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
    (hoff : parent S F i x=false) (v : V) (b : ℕ)
    (hb : GuardCandidate S F P.strongLower P.strongUpper j x v b)
    (w : V) (hw : w ∈ failed S F j x v) : F (S.guard i) (child x w (S.label v w))=true := by
  rw [← guard_failures_eq S F hF i j P x hoff v b hb] at hw
  exact (Finset.mem_filter.mp hw).2.2



end
end ThreeBoundMinmaxCandidates





end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- External guard arcs landing on negative targets have the stronger
lower-target downward cost. Counts retain their actual multiplicity. -/


set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundRankNumeric
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive ThreeBoundFullProfile ThreeBoundNumeric
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxHeads ThreeBoundMinmaxCandidates ThreeBoundMinmaxCover
open ThreeBoundRankProfiles
open ThreeBoundMinmaxNumeric (EntryMatch)
open scoped Classical BigOperators
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

theorem bool_eq_of_ne_third (a b c : Bool) (ha : a≠c) (hb : b≠c) : a=b := by
  cases a <;> cases b <;> cases c <;> simp_all

theorem negative_true_child_lower (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
    (w : V) (hw : w ∈ negativeTargets S F P.strongLower P.strongUpper j x)
    (z : Bool) (hz : F (S.guard j) (child x w z)=true) :
    F (P.strongLower 0) (child x w z)=true := by
  obtain ⟨b,_,hb⟩ := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hw).1).2
  have hf := negative_guard_false S F hF i j P x w hw
  have hne (d : Bool) (hd : F (S.guard j) (child x w d)=true) :
      d≠missing S F j x w := by
    intro he
    rw [he,hf] at hd
    contradiction
  have hzm := hne z hz
  have hone (d : Bool) (hd : F (P.strongLower b) (child x w d)=true) :
      F (P.strongLower 0) (child x w z)=true := by
    have hdm := hne d (hF _ _ (P.guardTarget b hb.1) _ hd)
    have he := bool_eq_of_ne_third z d _ hzm hdm
    rw [he]
    exact hF _ _ (P.strongLowerMono (Nat.zero_le b)) _ hd
  exact hb.2.2.2.elim (hone false) (hone true)



theorem sum_ite_mem_card (E N : Finset V) (s j : ℕ) :
    (∑ w ∈ E, if w ∈ N then j else s) = (E ∩ N).card*j+(E \ N).card*s := by
  rw [Finset.sum_ite]
  have h1 : E.filter (fun w => w ∈ N)=E ∩ N := by ext w; simp
  have h2 : E.filter (fun w => w ∉ N)=E \ N := by ext w; simp
  rw [h1,h2]
  simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id]



theorem externalBits_split_bound (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (j : Fin n)
    (x : ((V × Bool) × I) → Bool) (G H N : Finset V) (s l : ℕ)
    (hc : ∀ u ∈ G, ∀ w ∈ ThreeBoundAccounting.externalHeads S F j x H u,
      (flipsTo (F (S.guard j)) false (child x w (S.label u w))).card ≤ 
        if w ∈ N then l else s) :
    let total := ∑ u ∈ G, (ThreeBoundAccounting.externalHeads S F j x H u).card
    let converted := ∑ u ∈ G, (ThreeBoundAccounting.externalHeads S F j x H u ∩ N).card
    (ThreeBoundAccounting.externalBits S F j x G H).card ≤  converted*l+(total-converted)*s := by
  dsimp only
  let E := fun u => ThreeBoundAccounting.externalHeads S F j x H u
  have hsplit : (∑ u ∈ G, (E u \ N).card)+(∑ u ∈ G, (E u ∩ N).card)=
      ∑ u ∈ G, (E u).card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun u _ => Finset.card_sdiff_add_card_inter (E u) N)
  have hbound : (ThreeBoundAccounting.externalBits S F j x G H).card ≤ 
      (∑ u ∈ G, (E u ∩ N).card)*l+(∑ u ∈ G, (E u \ N).card)*s := by
    unfold ThreeBoundAccounting.externalBits
    calc
      _ ≤  ∑ u ∈ G, ((E u).biUnion fun w =>
          liftBits w (S.label u w) (flipsTo (F (S.guard j)) false (child x w (S.label u w)))).card :=
        Finset.card_biUnion_le
      _ ≤  ∑ u ∈ G, ((E u ∩ N).card*l+(E u \ N).card*s) := by
        apply Finset.sum_le_sum
        intro u hu
        apply Finset.card_biUnion_le.trans
        rw [← sum_ite_mem_card (E u) N s l]
        apply Finset.sum_le_sum
        intro w hw
        rw [card_liftBits]
        exact hc u hu w hw
      _ = _ := by simp only [Finset.sum_add_distrib,Finset.sum_mul]
  have he : (∑ u ∈ G, (E u \ N).card)=
      (∑ u ∈ G, (E u).card)-(∑ u ∈ G, (E u ∩ N).card) := by omega
  rw [he] at hbound
  exact hbound





theorem actual_external_split_bound (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (a c : Entry) (hm : EntryMatch S F i j P a c)
    (v : Profile n) (hv : Upper F v) (x : ((V × Bool) × I) → Bool)
    (hoff : parent S F i x=false) :
    let total := ∑ w ∈ guardSources S F P.strongLower P.strongUpper j x,
      ((failed S F j x w).card-((highHeads S F P.strongLower P.strongUpper j x).filter (S.Adj w)).card)
    let e := convertedCount S F P.strongLower P.strongUpper j x
    (ThreeBoundMinmaxCover.externalBits S F P.strongLower P.strongUpper j x).card ≤ 
      e*(bExpr n c.guard (c.lowerAt 0)).eval v+(total-e)*(bExpr n c.guard a.guard).eval v := by
  have hs := bExpr_bound F v hv (S.guard j) (S.guard i) P.guards
  have hj := bExpr_bound F v hv (S.guard j) (P.strongLower 0) (P.guardTarget 0 (Nat.zero_le _))
  have he := externalBits_split_bound S F j x
    (guardSources S F P.strongLower P.strongUpper j x)
    (highHeads S F P.strongLower P.strongUpper j x)
    (negativeTargets S F P.strongLower P.strongUpper j x)
    ((bExpr n c.guard a.guard).eval v) ((bExpr n c.guard (c.lowerAt 0)).eval v) (by
      intro u hu w hw
      obtain ⟨b,hb⟩ := (Finset.mem_filter.mp hu).2
      have hwf : w ∈ failed S F j x u := (Finset.mem_sdiff.mp hw).1
      by_cases hn : w ∈ negativeTargets S F P.strongLower P.strongUpper j x
      · rw [if_pos hn]
        have hl := negative_true_child_lower S F hF i j P x w hn (S.label u w)
          (Finset.mem_filter.mp hwf).2.2
        simpa only [hm.strongGuard,hm.strongLower 0 (Nat.zero_le _)] using hj _ hl
      · rw [if_neg hn]
        have hl := guard_hit_eligible S F hF i j P x hoff u b hb w hwf
        simpa only [hm.strongGuard,hm.weakGuard] using hs _ hl)
  simpa only [convertedCount,ThreeBoundMinmaxCover.externalBits,
    ThreeBoundAccounting.externalHeads_card S F j x _ (high_guards_true S F hF i j P x)] using he

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
  (v : Sensitivity213981Formal.ThreeBoundFullProfile.Profile n)
  (hv : @Sensitivity213981Formal.ThreeBoundFullProfile.Upper n I inst F v)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool)
  (hoff : @Eq.{1} Bool (@Sensitivity213981Formal.ThreeBoundWitness.parent (Fin n) I V inst_1 S F i x) Bool.false),
  have total : Nat :=
    @Finset.sum.{0, 0} V Nat Nat.instAddCommMonoid
      (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.guardSources (Fin n) I V inst_1 S F
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
        j x)
      fun (w : V) =>
      @HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
        (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundWitness.failed (Fin n) I V inst_1 S F j x w))
        (@Finset.card.{0} V
          (@Finset.filter.{0} V (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj (Fin n) I V S w)
            (fun (a : V) =>
              Classical.propDecidable (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj (Fin n) I V S w a))
            (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads (Fin n) I V inst_1 S F
              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
                (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
                (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
              j x)));
  have e : Nat :=
    @Sensitivity213981Formal.ThreeBoundRankNumeric.convertedCount n I V inst_1 S F
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
        (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
        (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
      j x;
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@Sensitivity213981Formal.ThreeBoundMinmaxCover.externalBits (Fin n) I V inst inst_1 S F
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
        j x))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) e
        (@Sensitivity213981Formal.ThreeBoundNumeric.Expr.eval n v
          (Sensitivity213981Formal.ThreeBoundNumeric.bExpr n
            (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.guard c)
            (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.lowerAt c
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) total e)
        (@Sensitivity213981Formal.ThreeBoundNumeric.Expr.eval n v
          (Sensitivity213981Formal.ThreeBoundNumeric.bExpr n
            (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.guard c)
            (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.guard a))))) := @Sensitivity213981Formal.ThreeBoundRankNumeric.actual_external_split_bound
