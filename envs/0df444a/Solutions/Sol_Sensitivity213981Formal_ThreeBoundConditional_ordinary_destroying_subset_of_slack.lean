-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundConditional.ordinary_destroying_subset_of_slack
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T19:33:07.223433+00:00
-- url     : https://prove2.me/submissions/ad95c150-d849-4bb6-9690-ed4ce49f5901

import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_WitnessLifting
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
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
open OAI.Paper320

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
Ordinary-component conditional transfers for the actual guarded Boolean family.
This development uses the shared campaign bit-flip definitions throughout.
-/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace ThreeBoundConditional
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped BigOperators Classical
noncomputable section

variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]









@[simp] theorem ordinary_failed (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g l : L) (q : ℕ) (x : ((V × Bool) × I) → Bool) (v : V) :
    failed (ordinaryStage S F t g q) F l x v = guardFailures S F g x v := rfl

@[simp] theorem ordinary_parent_true (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (q : ℕ) (x : ((V × Bool) × I) → Bool) :
    ordinaryParent S F t g q x = true ↔ ∃ v, ordinaryRow S F t g q x v := by
  simp only [ordinaryParent, parent_true_iff, ordinary_failed, ordinaryStage,
    Bool.and_eq_true, ordinaryRow]
  constructor
  · rintro ⟨v,hc,hf,ht⟩
    exact ⟨v, fun c => by cases c <;> assumption, hc⟩
  · rintro ⟨v,ht,hc⟩
    exact ⟨v,hc,ht false,ht true⟩

@[simp] theorem mem_guardFailures (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (g : L) (x : ((V × Bool) × I) → Bool) (v w : V) :
    w ∈ guardFailures S F g x v ↔ S.Adj v w ∧ F g (child x w (S.label v w)) = true := by
  simp [guardFailures]
























theorem guardFailures_after_subset_insert (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (gi gj : L) (hg : gj ≤  gi)
    (x : ((V × Bool) × I) → Bool) (v w : V) (c : Bool) (a : I) :
    guardFailures S F gi (_root_.OAI.Paper320.flip x {((w,c),a)}) v ⊆ insert w (guardFailures S F gj x v) := by
  intro z hz
  by_cases hzw : z = w
  · exact Finset.mem_insert.mpr (Or.inl hzw)
  · have hp : (z,S.label v z) ≠ (w,c) := fun h => hzw (congrArg Prod.fst h)
    obtain ⟨hR,hf⟩ := (mem_guardFailures S F gi _ v z).1 hz
    rw [child_flip_other x w z c (S.label v z) a hp] at hf
    exact Finset.mem_insert.mpr (Or.inr ((mem_guardFailures S F gj x v z).2
      ⟨hR,hF _ _ hg _ hf⟩))





/-- Actual guard slack removes all guard-only destruction coordinates. -/
theorem ordinary_destroying_subset_of_slack (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (ti tj gi gj : L)
    (ht : ti ≤  tj) (hg : gj ≤  gi) (qi q : ℕ) (hq : q ≤  qi)
    (x : ((V × Bool) × I) → Bool) (v : V) (hv : ordinaryRow S F tj gj q x v)
    (hslack : (guardFailures S F gj x v).card <  qi) :
    flipsTo (ordinaryParent S F ti gi qi) false x ⊆ targetBits F ti x v := by
  intro p hp
  rcases p with ⟨⟨w,c⟩,a⟩
  have hoff := (Finset.mem_filter.mp hp).2
  have hc : (guardFailures S F gi (_root_.OAI.Paper320.flip x {((w,c),a)}) v).card ≤  qi :=
    (Finset.card_le_card (guardFailures_after_subset_insert S F hF gi gj hg x v w c a)).trans
      ((Finset.card_insert_le _ _).trans (by omega))
  by_cases hw : w = v
  · subst w
    have hf : F ti (_root_.OAI.Paper320.flip (child x v c) {a}) = false := by
      cases h : F ti (_root_.OAI.Paper320.flip (child x v c) {a}) with
      | false => rfl
      | true =>
        have hon : ordinaryParent S F ti gi qi (_root_.OAI.Paper320.flip x {((v,c),a)}) = true := by
          apply (ordinary_parent_true S F ti gi qi _).2
          refine ⟨v,?_,hc⟩
          intro e
          by_cases hec : e = c
          · subst e; simpa only [child_flip_same] using h
          · rw [child_flip_other x v v c e a (fun h => hec (congrArg Prod.snd h))]
            exact hF _ _ ht _ (hv.1 e)
        rw [hoff] at hon
        contradiction
    have hm : a ∈ flipsTo (F ti) false (child x v c) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf⟩
    cases c
    · exact Finset.mem_union.mpr (Or.inl ((mem_liftBits _ _ _ _ _ _).2 ⟨rfl,rfl,hm⟩))
    · exact Finset.mem_union.mpr (Or.inr ((mem_liftBits _ _ _ _ _ _).2 ⟨rfl,rfl,hm⟩))
  · have hon : ordinaryParent S F ti gi qi (_root_.OAI.Paper320.flip x {((w,c),a)}) = true := by
      apply (ordinary_parent_true S F ti gi qi _).2
      refine ⟨v,?_,hc⟩
      intro e
      rw [child_flip_other x w v c e a (fun h => hw (congrArg Prod.fst h).symm)]
      exact hF _ _ ht _ (hv.1 e)
    rw [hoff] at hon
    contradiction






























end
end ThreeBoundConditional




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
  (ti tj gi gj : L)
  (ht :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      ti tj)
  (hg :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      gj gi)
  (qi q : Nat) (hq : @LE.le.{0} Nat instLENat q qi) (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (v : V)
  (hv : @Sensitivity213981Formal.ThreeBoundConditional.ordinaryRow L I V inst_2 S F tj gj q x v)
  (hslack :
    @LT.lt.{0} Nat instLTNat
      (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundConditional.guardFailures L I V inst_2 S F gj x v)) qi),
  @LE.le.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
    (@Preorder.toLE.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
      (@PartialOrder.toPreorder.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
        (@Finset.instPartialOrder.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))))
    (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_2 Bool.fintype) inst_1)
      (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryParent L I V inst_2 S F ti gi qi) Bool.false x)
    (@Sensitivity213981Formal.ThreeBoundPositive.targetBits L I V inst_1 F ti x v) := @Sensitivity213981Formal.ThreeBoundConditional.ordinary_destroying_subset_of_slack
