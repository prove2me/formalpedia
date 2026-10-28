-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxTransfer.minmax_B_row
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:16:25.903449+00:00
-- url     : https://prove2.me/submissions/203cae1b-8b09-433e-a2b3-b808cb718c32

import Definitions.Def_Sensitivity213981Formal_MinmaxB
import Definitions.Def_Sensitivity213981Formal_MinmaxPairData
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Supplement_GradedPositiveBoundary
import Definitions.Def_Sensitivity213981Formal_WitnessLifting
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxTransfer_mmTargetBits_eq_oriented
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundPositive_failed_after_subset_of_no_extra
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundPositive_guardBits_card_le
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundPositive_mem_liftBits


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



















theorem child_flip_same (x : ((V × Bool) × I) → Bool) (v : V) (c : Bool) (i : I) :
    child (_root_.OAI.Paper320.flip x {((v,c),i)}) v c = _root_.OAI.Paper320.flip (child x v c) {i} := by
  classical
  funext a
  simp [child, _root_.OAI.Paper320.flip]

theorem child_flip_other (x : ((V × Bool) × I) → Bool)
    (v w : V) (c e : Bool) (i : I) (h : (w,e) ≠ (v,c)) :
    child (_root_.OAI.Paper320.flip x {((v,c),i)}) w e = child x w e := by
  classical
  funext a
  have hh : ((w,e),a) ≠ ((v,c),i) := by
    intro he
    exact h (congrArg Prod.fst he)
  simp [child, _root_.OAI.Paper320.flip, hh]

























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



/-- Outside the changed child, every new weak failure was an old strong failure. -/
theorem failed_after_subset_insert (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (hg : S.guard j ≤  S.guard i)
    (x : ((V × Bool) × I) → Bool) (v w : V) (c : Bool) (a : I) :
    failed S F i (_root_.OAI.Paper320.flip x {((w,c),a)}) v ⊆ insert w (failed S F j x v) := by
  classical
  intro z hz
  by_cases hzw : z = w
  · exact Finset.mem_insert.mpr (Or.inl hzw)
  · apply Finset.mem_insert.mpr
    right
    rcases Finset.mem_filter.mp hz with ⟨_, hR, hf⟩
    have hp : (z, S.label v z) ≠ (w,c) := fun h => hzw (congrArg Prod.fst h)
    rw [child_flip_other x w z c (S.label v z) a hp] at hf
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hR, hF _ _ hg _ hf⟩



theorem failed_after_card_le_add_one (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (hg : S.guard j ≤  S.guard i)
    (x : ((V × Bool) × I) → Bool) (v w : V) (c : Bool) (a : I) :
    (failed S F i (_root_.OAI.Paper320.flip x {((w,c),a)}) v).card ≤  (failed S F j x v).card + 1 := by
  classical
  exact (Finset.card_le_card (failed_after_subset_insert S F hF i j hg x v w c a)).trans
    (Finset.card_insert_le _ _)













@[simp] theorem card_liftBits (v : V) (c : Bool) (s : Finset I) :
    (liftBits v c s).card = s.card := Finset.card_map _





@[simp] theorem mem_passing (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (j : L) (x : ((V × Bool) × I) → Bool) (v w : V) :
    w ∈ passing S F j x v ↔
      S.Adj v w ∧ F (S.guard j) (child x w (S.label v w)) = false := by
  simp only [passing, outgoing, failed, Finset.mem_sdiff, Finset.mem_filter,
    Finset.mem_univ, true_and]
  cases F (S.guard j) (child x w (S.label v w)) <;> simp



















end
end ThreeBoundPositive






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

theorem mm_comm (F : L → (I → Bool) → Bool) (t u : L) (x y : I → Bool) :
    mm F t u x y=mm F t u y x := by
  simp only [mm,Bool.and_comm,Bool.or_comm]

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







end
end ThreeBoundMinmaxTransfer




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Actual min/max downward transfer, with the upper-child improvement and
exact next-tier guard-destruction gate. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxTransfer
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional
open scoped Classical
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]









theorem orientedBits_card (F : L → (I → Bool) → Bool) (t u : L)
    (x : ((V × Bool) × I) → Bool) (w : V) (c : Bool) (a b : ℕ)
    (ha : (flipsTo (F t) false (child x w (!c))).card ≤  a)
    (hb : (flipsTo (F u) false (child x w c)).card ≤  b) :
    (orientedBits F t u x w c).card ≤  a+b := by
  exact (Finset.card_union_le _ _).trans (by simpa only [card_liftBits] using Nat.add_le_add ha hb)



theorem mmTargetBits_card (F : L → (I → Bool) → Bool) (hF : Nested F)
    (ti ui tj uj : L) (hlu : ti ≤  ui) (ht : ti ≤  tj) (hu : ui ≤  uj)
    (x : ((V × Bool) × I) → Bool) (w : V)
    (hstrong : mm F tj uj (child x w false) (child x w true)=true)
    (b0 b1 bu m : ℕ) (hb0 : BBound F ti tj b0) (hb1 : BBound F ti uj b1)
    (hbu : BBound F ui uj bu) (hm : MBound F ti tj ui m) :
    (mmTargetBits F ti ui x w).card ≤  max (b0+b1) (if tj< ui then bu+m else 0) := by
  obtain ⟨hl0,hl1,hup⟩ := (mm_true F tj uj _ _).1 hstrong
  have hor : ∃ c : Bool, F uj (child x w c)=true ∧ F tj (child x w (!c))=true := by
    rcases hup with hh | hh
    · exact ⟨false,hh,hl1⟩
    · exact ⟨true,hh,hl0⟩
  obtain ⟨c,hhigh,hlow⟩ := hor
  have hh := hF _ _ hu _ hhigh
  have hl := hF _ _ ht _ hlow
  rw [mmTargetBits_eq_oriented F hF ti ui hlu x w c hh hl]
  by_cases ho : F ui (child x w (!c))=true
  · rw [if_pos ho]
    exact (orientedBits_card F ti ti x w c b0 b1 (hb0 _ hlow) (hb1 _ hhigh)).trans (le_max_left _ _)
  · rw [if_neg ho]
    have ho' : F ui (child x w (!c))=false := by cases he : F ui (child x w (!c)) <;> simp_all
    have hlt : tj< ui := by
      by_contra hn
      have he := hF _ _ (le_of_not_gt hn) _ hlow
      rw [ho'] at he
      contradiction
    apply (orientedBits_card F ti ui x w c m bu (hm _ hlow ho') (hbu _ hhigh)).trans
    rw [if_pos hlt]
    omega

theorem own_mm_bit_mem (F : L → (I → Bool) → Bool) (t u : L)
    (x : ((V × Bool) × I) → Bool) (w : V) (c : Bool) (a : I)
    (hoff : mm F t u (child (_root_.OAI.Paper320.flip x {((w,c),a)}) w false)
      (child (_root_.OAI.Paper320.flip x {((w,c),a)}) w true)=false) :
    ((w,c),a) ∈ mmTargetBits F t u x w := by
  cases c
  · rw [child_flip_same,child_flip_other x w w false true a (by simp)] at hoff
    exact Finset.mem_union_left _ ((mem_liftBits _ _ _ _ _ _).2
      ⟨rfl,rfl,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hoff⟩⟩)
  · rw [child_flip_other x w w true false a (by simp),child_flip_same,mm_comm] at hoff
    exact Finset.mem_union_right _ ((mem_liftBits _ _ _ _ _ _).2
      ⟨rfl,rfl,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hoff⟩⟩)

theorem minmax_down_cover (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (v : V) (d : ℕ)
    (hd : (failed S F j x v).card=d) (hdq : d ≤  S.tolerance j)
    (hstrong : mm F (P.strongLower d) (P.strongUpper d) (child x v false) (child x v true)=true) :
    flipsTo (parent S F i) false x ⊆
      mmTargetBits F (P.weakLower d) (P.weakUpper d) x v ∪ guardBits S F i j x v := by
  intro bit hbit
  obtain ⟨⟨w,c⟩,a⟩ := bit
  have hoff := (Finset.mem_filter.mp hbit).2
  by_cases he : ExtraFailure S F i j x v w c a
  · apply Finset.mem_union_right
    obtain ⟨hR,hl,hbefore,hafter⟩ := he
    apply Finset.mem_biUnion.mpr
    refine ⟨w,(mem_passing S F j x v w).2 ⟨hR,by simpa only [hl] using hbefore⟩,?_⟩
    apply (mem_liftBits _ _ _ _ _ _).2
    exact ⟨rfl,hl.symm,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [hl] using hafter⟩⟩
  · have hcount : (failed S F i (_root_.OAI.Paper320.flip x {((w,c),a)}) v).card ≤  d := by
      rw [← hd]
      exact Finset.card_le_card (failed_after_subset_of_no_extra S F hF i j P.guards x v w c a he)
    have hweak := mm_mono F hF _ _ _ _ (P.lowerOrder d hdq) (P.upperOrder d hdq) _ _ hstrong
    have hfalse : mm F (P.weakLower d) (P.weakUpper d)
        (child (_root_.OAI.Paper320.flip x {((w,c),a)}) v false) (child (_root_.OAI.Paper320.flip x {((w,c),a)}) v true)=false := by
      cases hh : mm F (P.weakLower d) (P.weakUpper d)
          (child (_root_.OAI.Paper320.flip x {((w,c),a)}) v false) (child (_root_.OAI.Paper320.flip x {((w,c),a)}) v true) with
      | false => rfl
      | true =>
          have hon := parent_true_of_count S F hF i P.weakLower P.weakUpper P.weakLowerMono P.weakUpperMono
            P.weakDef _ v d (hdq.trans P.tolerances) hcount hh
          rw [hoff] at hon
          contradiction
    have hw : w=v := by
      by_contra hn
      rw [child_flip_other x w v c false a (fun h => hn (congrArg Prod.fst h).symm),
        child_flip_other x w v c true a (fun h => hn (congrArg Prod.fst h).symm),hweak] at hfalse
      contradiction
    subst w
    exact Finset.mem_union_left _ (own_mm_bit_mem F _ _ x v c a hfalse)

theorem minmax_safe_next_survives (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (v : V) (d : ℕ)
    (hd : (failed S F j x v).card=d)
    (hnext : d+1 ≤  S.tolerance i ∧ P.weakLower (d+1) ≤  P.strongLower d ∧ P.weakUpper (d+1) ≤  P.strongUpper d)
    (hstrong : mm F (P.strongLower d) (P.strongUpper d) (child x v false) (child x v true)=true)
    (w : V) (c : Bool) (a : I) (hw : w≠v) : parent S F i (_root_.OAI.Paper320.flip x {((w,c),a)})=true := by
  have hcount := failed_after_card_le_add_one S F hF i j P.guards x v w c a
  rw [hd] at hcount
  apply parent_true_of_count S F hF i P.weakLower P.weakUpper P.weakLowerMono P.weakUpperMono
    P.weakDef _ v (d+1) hnext.1 hcount
  rw [child_flip_other x w v c false a (fun h => hw (congrArg Prod.fst h).symm),
    child_flip_other x w v c true a (fun h => hw (congrArg Prod.fst h).symm)]
  exact mm_mono F hF _ _ _ _ hnext.2.1 hnext.2.2 _ _ hstrong

/-- Exact per-winning-row formula used by minmax_transfer.rawB. -/
theorem minmax_B_row (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (w : V) (d : ℕ)
    (hd : (failed S F j x w).card=d) (hdq : d ≤  S.tolerance j)
    (hstrong : mm F (P.strongLower d) (P.strongUpper d) (child x w false) (child x w true)=true)
    (a b0 b1 bu m : ℕ) (ha : ABound F (S.guard j) (S.guard i) a)
    (hb0 : BBound F (P.weakLower d) (P.strongLower d) b0)
    (hb1 : BBound F (P.weakLower d) (P.strongUpper d) b1)
    (hbu : BBound F (P.weakUpper d) (P.strongUpper d) bu)
    (hm : MBound F (P.weakLower d) (P.strongLower d) (P.weakUpper d) m) :
    (flipsTo (parent S F i) false x).card ≤ 
      max (b0+b1) (if P.strongLower d< P.weakUpper d then bu+m else 0)+
      if d+1 ≤  S.tolerance i ∧ P.weakLower (d+1) ≤  P.strongLower d ∧ P.weakUpper (d+1) ≤  P.strongUpper d
      then 0 else ((outgoing S w).card-d)*a := by
  have htarget := mmTargetBits_card F hF _ _ _ _ (P.weakLowerUpper d (hdq.trans P.tolerances))
    (P.lowerOrder d hdq) (P.upperOrder d hdq) x w hstrong b0 b1 bu m hb0 hb1 hbu hm
  have hcover := minmax_down_cover S F hF i j P x w d hd hdq hstrong
  by_cases hs : d+1 ≤  S.tolerance i ∧ P.weakLower (d+1) ≤  P.strongLower d ∧ P.weakUpper (d+1) ≤  P.strongUpper d
  · rw [if_pos hs,Nat.add_zero]
    apply (Finset.card_le_card (show flipsTo (parent S F i) false x ⊆
      mmTargetBits F (P.weakLower d) (P.weakUpper d) x w from ?_)).trans htarget
    intro bit hb
    obtain ht | hg := Finset.mem_union.mp (hcover hb)
    · exact ht
    · obtain ⟨z,hz,hbit⟩ := Finset.mem_biUnion.mp hg
      obtain ⟨hR,_⟩ := (mem_passing S F j x w z).1 hz
      obtain ⟨a,ha,he⟩ := Finset.mem_map.mp hbit
      change ((z,S.label w z),a)=bit at he
      subst bit
      have hzw : z≠w := fun he => by subst z; exact S.loopless w hR
      have hon := minmax_safe_next_survives S F hF i j P x w d hd hs hstrong z (S.label w z) a hzw
      have hoff := (Finset.mem_filter.mp hb).2
      rw [hoff] at hon
      contradiction
  · rw [if_neg hs]
    apply (Finset.card_le_card hcover).trans
    apply (Finset.card_union_le _ _).trans
    have hg := guardBits_card_le S F i j x w a ha
    rw [hd] at hg
    exact Nat.add_le_add htarget hg

end
end ThreeBoundMinmaxTransfer




end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {L I V : Type} [inst : LinearOrder.{0} L] [inst_1 : Fintype.{0} I] [inst_2 : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage L I V) (F : L → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested L I
      (@PartialOrder.toPreorder.{0} L
        (@SemilatticeInf.toPartialOrder.{0} L
          (@Lattice.toSemilatticeInf.{0} L
            (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
      F)
  (i j : L)
  (P :
    @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData L I V
      (@PartialOrder.toPreorder.{0} L
        (@SemilatticeInf.toPartialOrder.{0} L
          (@Lattice.toSemilatticeInf.{0} L
            (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
      S F i j)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (w : V) (d : Nat)
  (hd : @Eq.{1} Nat (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundWitness.failed L I V inst_2 S F j x w)) d)
  (hdq : @LE.le.{0} Nat instLENat d (@Sensitivity213981Formal.ThreeBoundWitness.Stage.tolerance L I V S j))
  (hstrong :
    @Eq.{1} Bool
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.mm L I F
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
          (@PartialOrder.toPreorder.{0} L
            (@SemilatticeInf.toPartialOrder.{0} L
              (@Lattice.toSemilatticeInf.{0} L
                (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
          S F i j P d)
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
          (@PartialOrder.toPreorder.{0} L
            (@SemilatticeInf.toPartialOrder.{0} L
              (@Lattice.toSemilatticeInf.{0} L
                (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
          S F i j P d)
        (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w Bool.false)
        (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w Bool.true))
      Bool.true)
  (a b0 b1 bu m : Nat)
  (ha :
    @Sensitivity213981Formal.ThreeBoundProfiles.ABound L I inst_1 F
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S j)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S i) a)
  (hb0 :
    @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst_1 F
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.weakLower L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F i j P d)
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F i j P d)
      b0)
  (hb1 :
    @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst_1 F
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.weakLower L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F i j P d)
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F i j P d)
      b1)
  (hbu :
    @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst_1 F
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.weakUpper L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F i j P d)
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F i j P d)
      bu)
  (hm :
    @Sensitivity213981Formal.ThreeBoundProfiles.MBound L I inst_1 F
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.weakLower L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F i j P d)
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F i j P d)
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.weakUpper L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F i j P d)
      m),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
        (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_2 Bool.fintype) inst_1)
        (@Sensitivity213981Formal.ThreeBoundWitness.parent L I V inst_2 S F i) Bool.false x))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@Max.max.{0} Nat Nat.instMax (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b0 b1)
        (@ite.{1} Nat
          (@LT.lt.{0} L
            (@Preorder.toLT.{0} L
              (@PartialOrder.toPreorder.{0} L
                (@SemilatticeInf.toPartialOrder.{0} L
                  (@Lattice.toSemilatticeInf.{0} L
                    (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
              (@PartialOrder.toPreorder.{0} L
                (@SemilatticeInf.toPartialOrder.{0} L
                  (@Lattice.toSemilatticeInf.{0} L
                    (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
              S F i j P d)
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.weakUpper L I V
              (@PartialOrder.toPreorder.{0} L
                (@SemilatticeInf.toPartialOrder.{0} L
                  (@Lattice.toSemilatticeInf.{0} L
                    (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
              S F i j P d))
          (@LinearOrder.toDecidableLT.{0} L inst
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
              (@PartialOrder.toPreorder.{0} L
                (@SemilatticeInf.toPartialOrder.{0} L
                  (@Lattice.toSemilatticeInf.{0} L
                    (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
              S F i j P d)
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.weakUpper L I V
              (@PartialOrder.toPreorder.{0} L
                (@SemilatticeInf.toPartialOrder.{0} L
                  (@Lattice.toSemilatticeInf.{0} L
                    (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
              S F i j P d))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bu m)
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@ite.{1} Nat
        (And
          (@LE.le.{0} Nat instLENat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@Sensitivity213981Formal.ThreeBoundWitness.Stage.tolerance L I V S i))
          (And
            (@LE.le.{0} L
              (@Preorder.toLE.{0} L
                (@PartialOrder.toPreorder.{0} L
                  (@SemilatticeInf.toPartialOrder.{0} L
                    (@Lattice.toSemilatticeInf.{0} L
                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.weakLower L I V
                (@PartialOrder.toPreorder.{0} L
                  (@SemilatticeInf.toPartialOrder.{0} L
                    (@Lattice.toSemilatticeInf.{0} L
                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                S F i j P
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                (@PartialOrder.toPreorder.{0} L
                  (@SemilatticeInf.toPartialOrder.{0} L
                    (@Lattice.toSemilatticeInf.{0} L
                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                S F i j P d))
            (@LE.le.{0} L
              (@Preorder.toLE.{0} L
                (@PartialOrder.toPreorder.{0} L
                  (@SemilatticeInf.toPartialOrder.{0} L
                    (@Lattice.toSemilatticeInf.{0} L
                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.weakUpper L I V
                (@PartialOrder.toPreorder.{0} L
                  (@SemilatticeInf.toPartialOrder.{0} L
                    (@Lattice.toSemilatticeInf.{0} L
                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                S F i j P
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                (@PartialOrder.toPreorder.{0} L
                  (@SemilatticeInf.toPartialOrder.{0} L
                    (@Lattice.toSemilatticeInf.{0} L
                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                S F i j P d))))
        (@instDecidableAnd
          (@LE.le.{0} Nat instLENat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@Sensitivity213981Formal.ThreeBoundWitness.Stage.tolerance L I V S i))
          (And
            (@LE.le.{0} L
              (@Preorder.toLE.{0} L
                (@PartialOrder.toPreorder.{0} L
                  (@SemilatticeInf.toPartialOrder.{0} L
                    (@Lattice.toSemilatticeInf.{0} L
                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.weakLower L I V
                (@PartialOrder.toPreorder.{0} L
                  (@SemilatticeInf.toPartialOrder.{0} L
                    (@Lattice.toSemilatticeInf.{0} L
                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                S F i j P
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                (@PartialOrder.toPreorder.{0} L
                  (@SemilatticeInf.toPartialOrder.{0} L
                    (@Lattice.toSemilatticeInf.{0} L
                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                S F i j P d))
            (@LE.le.{0} L
              (@Preorder.toLE.{0} L
                (@PartialOrder.toPreorder.{0} L
                  (@SemilatticeInf.toPartialOrder.{0} L
                    (@Lattice.toSemilatticeInf.{0} L
                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.weakUpper L I V
                (@PartialOrder.toPreorder.{0} L
                  (@SemilatticeInf.toPartialOrder.{0} L
                    (@Lattice.toSemilatticeInf.{0} L
                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                S F i j P
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                (@PartialOrder.toPreorder.{0} L
                  (@SemilatticeInf.toPartialOrder.{0} L
                    (@Lattice.toSemilatticeInf.{0} L
                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                S F i j P d)))
          (Nat.decLe
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@Sensitivity213981Formal.ThreeBoundWitness.Stage.tolerance L I V S i))
          (@instDecidableAnd
            (@LE.le.{0} L
              (@Preorder.toLE.{0} L
                (@PartialOrder.toPreorder.{0} L
                  (@SemilatticeInf.toPartialOrder.{0} L
                    (@Lattice.toSemilatticeInf.{0} L
                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.weakLower L I V
                (@PartialOrder.toPreorder.{0} L
                  (@SemilatticeInf.toPartialOrder.{0} L
                    (@Lattice.toSemilatticeInf.{0} L
                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                S F i j P
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                (@PartialOrder.toPreorder.{0} L
                  (@SemilatticeInf.toPartialOrder.{0} L
                    (@Lattice.toSemilatticeInf.{0} L
                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                S F i j P d))
            (@LE.le.{0} L
              (@Preorder.toLE.{0} L
                (@PartialOrder.toPreorder.{0} L
                  (@SemilatticeInf.toPartialOrder.{0} L
                    (@Lattice.toSemilatticeInf.{0} L
                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.weakUpper L I V
                (@PartialOrder.toPreorder.{0} L
                  (@SemilatticeInf.toPartialOrder.{0} L
                    (@Lattice.toSemilatticeInf.{0} L
                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                S F i j P
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                (@PartialOrder.toPreorder.{0} L
                  (@SemilatticeInf.toPartialOrder.{0} L
                    (@Lattice.toSemilatticeInf.{0} L
                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                S F i j P d))
            (@LinearOrder.toDecidableLE.{0} L inst
              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.weakLower L I V
                (@PartialOrder.toPreorder.{0} L
                  (@SemilatticeInf.toPartialOrder.{0} L
                    (@Lattice.toSemilatticeInf.{0} L
                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                S F i j P
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                (@PartialOrder.toPreorder.{0} L
                  (@SemilatticeInf.toPartialOrder.{0} L
                    (@Lattice.toSemilatticeInf.{0} L
                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                S F i j P d))
            (@LinearOrder.toDecidableLE.{0} L inst
              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.weakUpper L I V
                (@PartialOrder.toPreorder.{0} L
                  (@SemilatticeInf.toPartialOrder.{0} L
                    (@Lattice.toSemilatticeInf.{0} L
                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                S F i j P
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                (@PartialOrder.toPreorder.{0} L
                  (@SemilatticeInf.toPartialOrder.{0} L
                    (@Lattice.toSemilatticeInf.{0} L
                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                S F i j P d))))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundPositive.outgoing L I V inst_2 S w)) d)
          a))) := @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.minmax_B_row
