-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundConditional.ordinary_guard_defect_down
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T19:37:33.236178+00:00
-- url     : https://prove2.me/submissions/40ab23cc-4ccb-4146-81bb-fc9534cbd615

import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Supplement_GradedPositiveBoundary
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_ordinaryGuardBits_card_special
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_ordinary_destroying_subset
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_ordinary_destroying_subset_of_slack


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
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles
open scoped BigOperators Classical
noncomputable section

variable {L I V : Type} [Preorder L] [Fintype I] [Fintype V]





















@[simp] theorem card_liftBits (v : V) (c : Bool) (s : Finset I) :
    (liftBits v c s).card = s.card := Finset.card_map _













theorem targetBits_card_le (F : L → (I → Bool) → Bool) (ti tj : L)
    (x : ((V × Bool) × I) → Bool) (v : V) (b : ℕ)
    (hb : BBound F ti tj b) (hstrong : ∀ c : Bool, F tj (child x v c) = true) :
    (targetBits F ti x v).card ≤  2*b := by
  calc
    (targetBits F ti x v).card ≤ 
        (flipsTo (F ti) false (child x v false)).card +
        (flipsTo (F ti) false (child x v true)).card := by
      simpa only [targetBits, card_liftBits] using Finset.card_union_le
        (liftBits v false (flipsTo (F ti) false (child x v false)))
        (liftBits v true (flipsTo (F ti) false (child x v true)))
    _ ≤  b+b := Nat.add_le_add (hb _ (hstrong false)) (hb _ (hstrong true))
    _ = 2*b := by omega











end
end ThreeBoundPositive






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













@[simp] theorem mem_guardFailures (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (g : L) (x : ((V × Bool) × I) → Bool) (v w : V) :
    w ∈ guardFailures S F g x v ↔ S.Adj v w ∧ F g (child x w (S.label v w)) = true := by
  simp [guardFailures]














@[simp] theorem mem_passingGuards (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (g : L) (x : ((V × Bool) × I) → Bool) (v w : V) :
    w ∈ passingGuards S F g x v ↔
      S.Adj v w ∧ F g (child x w (S.label v w)) = false := by
  simp only [passingGuards, outgoing, guardFailures, Finset.mem_sdiff,
    Finset.mem_filter, Finset.mem_univ, true_and]
  cases F g (child x w (S.label v w)) <;> simp




















/-- In the guard-defect branch one actual guard lies in the conditional gap. -/
theorem ordinary_guard_defect_down (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (ti tj tk gi gj gk : L)
    (ht : ti ≤  tj) (hg : gj ≤  gi) (qi q : ℕ) (hq : q ≤  qi)
    (x : ((V × Bool) × I) → Bool) (v : V) (hv : ordinaryRow S F tj gj q x v)
    (htk : ∀ c : Bool, F tk (child x v c) = true)
    (hguard : q <  (guardFailures S F gk x v).card)
    (degree b a p : ℕ) (hdegree : (outgoing S v).card = degree)
    (hb : BBound F ti tk b) (ha : ABound F gj gi a) (hp : PBound F gk gj gi p) :
    (flipsTo (ordinaryParent S F ti gi qi) false x).card ≤ 
      2*b + if qi=q then (degree-q-1)*a+p else 0 := by
  have htarget := targetBits_card_le F ti tk x v b hb htk
  by_cases hslack : (guardFailures S F gj x v).card <  qi
  · have h := (Finset.card_le_card (ordinary_destroying_subset_of_slack
      S F hF ti tj gi gj ht hg qi q hq x v hv hslack)).trans htarget
    exact h.trans (Nat.le_add_right _ _)
  · have he : qi=q := by have hh := hv.2; omega
    have hc : (guardFailures S F gj x v).card = q := by have hh := hv.2; omega
    have hex : ∃ w ∈ guardFailures S F gk x v, w ∉ guardFailures S F gj x v := by
      by_contra hn
      have hsub : guardFailures S F gk x v ⊆ guardFailures S F gj x v := by
        intro w hw
        by_contra hj
        exact hn ⟨w,hw,hj⟩
      have hh := Finset.card_le_card hsub
      omega
    obtain ⟨w,hwk,hwj⟩ := hex
    obtain ⟨hR,hk⟩ := (mem_guardFailures S F gk x v w).1 hwk
    have hj : F gj (child x w (S.label v w)) = false := by
      cases h : F gj (child x w (S.label v w)) with
      | false => rfl
      | true => exact False.elim (hwj ((mem_guardFailures S F gj x v w).2 ⟨hR,h⟩))
    have hw : w ∈ passingGuards S F gj x v := (mem_passingGuards S F gj x v w).2 ⟨hR,hj⟩
    rw [if_pos he]
    calc
      _ ≤  (targetBits F ti x v ∪ ordinaryGuardBits S F gi gj x v).card :=
        Finset.card_le_card (ordinary_destroying_subset S F hF ti tj gi gj ht hg qi q hq x v hv)
      _ ≤  (targetBits F ti x v).card+(ordinaryGuardBits S F gi gj x v).card := Finset.card_union_le _ _
      _ ≤  _ := Nat.add_le_add htarget (by
        simpa only [hdegree,hc] using ordinaryGuardBits_card_special S F gi gj gk x v w a p ha hp hw hk)

























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
  (ti tj tk gi gj gk : L)
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
  (htk : ∀ (c : Bool), @Eq.{1} Bool (F tk (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v c)) Bool.true)
  (hguard :
    @LT.lt.{0} Nat instLTNat q
      (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundConditional.guardFailures L I V inst_2 S F gk x v)))
  (degree b a p : Nat)
  (hdegree :
    @Eq.{1} Nat (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundPositive.outgoing L I V inst_2 S v)) degree)
  (hb : @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst_1 F ti tk b)
  (ha : @Sensitivity213981Formal.ThreeBoundProfiles.ABound L I inst_1 F gj gi a)
  (hp : @Sensitivity213981Formal.ThreeBoundProfiles.PBound L I inst_1 F gk gj gi p),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
        (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_2 Bool.fintype) inst_1)
        (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryParent L I V inst_2 S F ti gi qi) Bool.false x))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
      (@ite.{1} Nat (@Eq.{1} Nat qi q) (instDecidableEqNat qi q)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) degree q)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            a)
          p)
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) := @Sensitivity213981Formal.ThreeBoundConditional.ordinary_guard_defect_down
