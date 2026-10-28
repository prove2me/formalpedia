-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxRank.row_capacity_data
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:32:16.381549+00:00
-- url     : https://prove2.me/submissions/eaaf7c0c-4c9a-407e-a4a6-c67825270af8

import Definitions.Def_Sensitivity213981Formal_MinmaxEntryMatch
import Definitions.Def_Sensitivity213981Formal_MinmaxPairData
import Definitions.Def_Sensitivity213981Formal_MinmaxRankData
import Definitions.Def_Sensitivity213981Formal_MinmaxRankExpressions
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
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
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
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

theorem mm_comm (F : L → (I → Bool) → Bool) (t u : L) (x y : I → Bool) :
    mm F t u x y=mm F t u y x := by
  simp only [mm,Bool.and_comm,Bool.or_comm]

theorem mm_mono (F : L → (I → Bool) → Bool) (hF : Nested F)
    (ti ui tj uj : L) (ht : ti ≤  tj) (hu : ui ≤  uj) (x y : I → Bool)
    (h : mm F tj uj x y=true) : mm F ti ui x y=true := by
  rw [mm_true] at h ⊢
  exact ⟨hF _ _ ht _ h.1,hF _ _ ht _ h.2.1,
    h.2.2.elim (fun hh => Or.inl (hF _ _ hu _ hh)) (fun hh => Or.inr (hF _ _ hu _ hh))⟩











end
end ThreeBoundMinmaxTransfer




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Exact rank states, numeric capacities and actual private-target boundaries. -/


set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxRank
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive ThreeBoundConditional
open ThreeBoundMinmaxTransfer ThreeBoundNumeric ThreeBoundFullProfile ThreeBoundRankProfiles
open scoped Classical
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

theorem accepted_spec (e : Entry) (d x y : ℕ) :
    accepted e d x y=true ↔ e.lowerAt d≤ x ∧ e.upperAt d≤ y := by
  simp only [accepted,decide_eq_true_eq]

theorem accepted_le_capacity (e : Entry) (d x y : ℕ) (hd : d≤ e.tolerance)
    (ha : accepted e d x y=true) : d+1≤ capacityHeight e x y := by
  have hh := Finset.le_sup (s:=Finset.range (e.tolerance+1))
    (f:=fun k => if accepted e k x y then k+1 else 0) (Finset.mem_range.mpr (by omega : d< e.tolerance+1))
  simpa only [capacityHeight,if_pos ha] using hh



theorem capacity_positive_data (e : Entry) (x y : ℕ) (hpos : 0< capacityHeight e x y) :
    capacityHeight e x y-1≤ e.tolerance ∧ accepted e (capacityHeight e x y-1) x y=true := by
  obtain ⟨d,hd,he⟩ := Finset.exists_mem_eq_sup (Finset.range (e.tolerance+1))
    ⟨0,Finset.mem_range.mpr (by omega)⟩ (fun k => if accepted e k x y then k+1 else 0)
  change capacityHeight e x y=(if accepted e d x y then d+1 else 0) at he
  by_cases ha : accepted e d x y=true
  · rw [if_pos ha] at he
    have hd' : d< e.tolerance+1 := Finset.mem_range.mp hd
    have hdEq : capacityHeight e x y-1=d := by omega
    exact ⟨by omega,hdEq.symm ▸ ha⟩
  · rw [if_neg ha] at he
    omega

theorem capacity_mono (a c : Entry) (x y : ℕ) (hq : c.tolerance≤ a.tolerance)
    (himp : ∀ d, d≤ c.tolerance → accepted c d x y=true → accepted a d x y=true) :
    capacityHeight c x y≤ capacityHeight a x y := by
  apply Finset.sup_le
  intro d hd
  have hd' : d≤ c.tolerance := by have hh := Finset.mem_range.mp hd; omega
  by_cases ha : accepted c d x y=true
  · rw [if_pos ha]
    exact accepted_le_capacity a d x y (hd'.trans hq) (himp d hd' ha)
  · rw [if_neg ha]
    exact Nat.zero_le _

theorem mm_rank_iff (F : Fin n → (I → Bool) → Bool) (t u : Fin n)
    (x y : I → Bool) (rx ry : Fin n) (hx : RankState F x rx) (hy : RankState F y ry) (hxy : rx≤ ry) :
    mm F t u x y=true ↔ t≤ rx ∧ u≤ ry := by
  rw [mm_true]
  constructor
  · rintro ⟨htx,hty,hu⟩
    exact ⟨(hx t).1 htx,hu.elim (fun hh => ((hx u).1 hh).trans hxy) (fun hh => (hy u).1 hh)⟩
  · rintro ⟨ht,hu⟩
    exact ⟨(hx t).2 ht,(hy t).2 (ht.trans hxy),Or.inr ((hy u).2 hu)⟩

theorem mm_reorder (F : Fin n → (I → Bool) → Bool) (t u : Fin n)
    (x : ((V × Bool) × I) → Bool) (w : V) (c : Bool) :
    mm F t u (child x w false) (child x w true)=mm F t u (child x w (!c)) (child x w c) := by
  cases c
  · exact mm_comm F t u _ _
  · rfl

theorem mm_row_rank_iff (F : Fin n → (I → Bool) → Bool) (t u : Fin n)
    (x : ((V × Bool) × I) → Bool) (w : V) (c : Bool) (rx ry : Fin n)
    (hx : RankState F (child x w (!c)) rx) (hy : RankState F (child x w c) ry) (hxy : rx≤ ry) :
    mm F t u (child x w false) (child x w true)=true ↔ t≤ rx ∧ u≤ ry := by
  rw [mm_reorder F t u x w c]
  exact mm_rank_iff F t u _ _ rx ry hx hy hxy

theorem matched_accepted_weak (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
    (i j : Fin n) (P : PairData S F i j) (a c : Entry)
    (hm : ThreeBoundMinmaxNumeric.EntryMatch S F i j P a c)
    (x : ((V × Bool) × I) → Bool) (w : V) (side : Bool) (rx ry : Fin n)
    (hx : RankState F (child x w (!side)) rx) (hy : RankState F (child x w side) ry) (hxy : rx≤ ry)
    (d : ℕ) (hd : d≤ S.tolerance i) :
    mm F (P.weakLower d) (P.weakUpper d) (child x w false) (child x w true)=true ↔
      accepted a d rx.val ry.val=true := by
  rw [mm_row_rank_iff F _ _ x w side rx ry hx hy hxy,accepted_spec]
  change ((P.weakLower d).val≤ rx.val ∧ (P.weakUpper d).val≤ ry.val) ↔ _
  rw [hm.weakLower d hd,hm.weakUpper d hd]

theorem matched_accepted_strong (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
    (i j : Fin n) (P : PairData S F i j) (a c : Entry)
    (hm : ThreeBoundMinmaxNumeric.EntryMatch S F i j P a c)
    (x : ((V × Bool) × I) → Bool) (w : V) (side : Bool) (rx ry : Fin n)
    (hx : RankState F (child x w (!side)) rx) (hy : RankState F (child x w side) ry) (hxy : rx≤ ry)
    (d : ℕ) (hd : d≤ S.tolerance j) :
    mm F (P.strongLower d) (P.strongUpper d) (child x w false) (child x w true)=true ↔
      accepted c d rx.val ry.val=true := by
  rw [mm_row_rank_iff F _ _ x w side rx ry hx hy hxy,accepted_spec]
  change ((P.strongLower d).val≤ rx.val ∧ (P.strongUpper d).val≤ ry.val) ↔ _
  rw [hm.strongLower d hd,hm.strongUpper d hd]

theorem need_valid (e : Entry) (d x y n : ℕ) (hxy : x≤ y) (ha : accepted e d x y=true) :
    need n e y d≤ x ∧ need n e x d≤ y := by
  obtain ⟨ht,hu⟩ := (accepted_spec e d x y).1 ha
  have hty : e.lowerAt d≤ y := ht.trans hxy
  constructor
  · simp only [need,if_pos hty,if_pos hu]
    exact ht
  · simp only [need,if_pos ht]
    split_ifs with hh
    · exact hty
    · exact hu



end
end ThreeBoundMinmaxRank




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Actual winning rows supply all feasible rank-capacity data used by the oracle. -/


set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxRank
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive ThreeBoundConditional
open ThreeBoundMinmaxTransfer ThreeBoundNumeric ThreeBoundFullProfile ThreeBoundRankProfiles
open scoped Classical
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]



theorem matched_capacity_mono (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
    (i j : Fin n) (P : PairData S F i j) (a c : Entry)
    (hm : ThreeBoundMinmaxNumeric.EntryMatch S F i j P a c) (rx ry : ℕ) :
    capacityHeight c rx ry≤ capacityHeight a rx ry := by
  apply capacity_mono a c rx ry (by simpa only [← hm.weakTolerance,← hm.strongTolerance] using P.tolerances)
  intro d hd hacc
  have hdj : d≤ S.tolerance j := by simpa only [hm.strongTolerance] using hd
  have hdi := hdj.trans P.tolerances
  have hl : a.lowerAt d≤ c.lowerAt d := by
    have hh : (P.weakLower d).val≤ (P.strongLower d).val := P.lowerOrder d hdj
    simpa only [hm.weakLower d hdi,hm.strongLower d hdj] using hh
  have hu : a.upperAt d≤ c.upperAt d := by
    have hh : (P.weakUpper d).val≤ (P.strongUpper d).val := P.upperOrder d hdj
    simpa only [hm.weakUpper d hdi,hm.strongUpper d hdj] using hh
  obtain ⟨hlo,hhi⟩ := (accepted_spec c d rx ry).1 hacc
  exact (accepted_spec a d rx ry).2 ⟨hl.trans hlo,hu.trans hhi⟩



theorem row_capacity_data (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
    (hF : Nested F) (i j : Fin n) (P : PairData S F i j) (a c : Entry)
    (hm : ThreeBoundMinmaxNumeric.EntryMatch S F i j P a c)
    (x : ((V × Bool) × I) → Bool) (w : V) (side : Bool) (rx ry : Fin n)
    (hx : RankState F (child x w (!side)) rx) (hy : RankState F (child x w side) ry) (hxy : rx≤ ry)
    (hcount : (failed S F j x w).card≤ S.tolerance j)
    (hstrong : mm F (P.strongLower (failed S F j x w).card) (P.strongUpper (failed S F j x w).card)
      (child x w false) (child x w true)=true) : RowCapacityData S F i j P a c x w rx ry := by
  have hacc := (matched_accepted_strong S F i j P a c hm x w side rx ry hx hy hxy _ hcount).1 hstrong
  have hle := accepted_le_capacity c (failed S F j x w).card rx.val ry.val
    (by simpa only [hm.strongTolerance] using hcount) hacc
  have hpos : 0< capacityHeight c rx.val ry.val := by omega
  have hcapmono := matched_capacity_mono S F i j P a c hm rx.val ry.val
  have hposa : 0< capacityHeight a rx.val ry.val := hpos.trans_le hcapmono
  obtain ⟨hdb,haccb⟩ := capacity_positive_data c rx.val ry.val hpos
  obtain ⟨hda,hacca⟩ := capacity_positive_data a rx.val ry.val hposa
  have hdb' : capacityHeight c rx.val ry.val-1≤ S.tolerance j := by simpa only [hm.strongTolerance] using hdb
  have hda' : capacityHeight a rx.val ry.val-1≤ S.tolerance i := by simpa only [hm.weakTolerance] using hda
  have htargetb := (matched_accepted_strong S F i j P a c hm x w side rx ry hx hy hxy _ hdb').2 haccb
  have htargeta := (matched_accepted_weak S F i j P a c hm x w side rx ry hx hy hxy _ hda').2 hacca
  have hweakb := mm_mono F hF _ _ _ _ (P.lowerOrder _ hdb') (P.upperOrder _ hdb') _ _ htargetb
  have haccab := (matched_accepted_weak S F i j P a c hm x w side rx ry hx hy hxy _ (hdb'.trans P.tolerances)).1 hweakb
  obtain ⟨hneed0,hneed1⟩ := need_valid a _ rx.val ry.val n hxy haccab
  exact ⟨hpos,hposa,hdb',hda',Nat.sub_le_sub_right hcapmono 1,by omega,htargetb,htargeta,hneed0,hneed1⟩



end
end ThreeBoundMinmaxRank




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
  (a c : Sensitivity213981Formal.ThreeBoundMinmaxRank.Entry)
  (hm : @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.EntryMatch n I V S F i j P a c)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (w : V) (side : Bool) (rx ry : Fin n)
  (hx :
    @Sensitivity213981Formal.ThreeBoundRankProfiles.RankState n I F
      (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w (Bool.not side)) rx)
  (hy :
    @Sensitivity213981Formal.ThreeBoundRankProfiles.RankState n I F
      (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w side) ry)
  (hxy : @LE.le.{0} (Fin n) (@instLEFin n) rx ry)
  (hcount :
    @LE.le.{0} Nat instLENat
      (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundWitness.failed (Fin n) I V inst S F j x w))
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.tolerance (Fin n) I V S j))
  (hstrong :
    @Eq.{1} Bool
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.mm (Fin n) I F
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P
          (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundWitness.failed (Fin n) I V inst S F j x w)))
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P
          (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundWitness.failed (Fin n) I V inst S F j x w)))
        (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w Bool.false)
        (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w Bool.true))
      Bool.true),
  @Sensitivity213981Formal.ThreeBoundMinmaxRank.RowCapacityData n I V inst S F i j P a c x w rx ry := @Sensitivity213981Formal.ThreeBoundMinmaxRank.row_capacity_data
