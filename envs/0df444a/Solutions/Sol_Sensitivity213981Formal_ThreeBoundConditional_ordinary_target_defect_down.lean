-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundConditional.ordinary_target_defect_down
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T19:37:29.840013+00:00
-- url     : https://prove2.me/submissions/f9fe9418-0881-4dc0-8760-24d92275bb46

import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_ordinaryGuardBits_card_le
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_ordinary_destroying_subset
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_ordinary_destroying_subset_of_slack
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_targetBits_conditional_card


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















































/-- An ordinary winner's target-defect boundary uses both child states. -/
theorem ordinary_target_defect_down (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (ti tj tk gi gj : L)
    (ht : ti ≤  tj) (hg : gj ≤  gi) (qi q : ℕ) (hq : q ≤  qi)
    (x : ((V × Bool) × I) → Bool) (v : V) (hv : ordinaryRow S F tj gj q x v)
    (hmiss : ∃ c : Bool, F tk (child x v c) = false)
    (degree m b a : ℕ) (hdegree : (outgoing S v).card = degree)
    (hm : MBound F ti tj tk m) (hb : BBound F ti tk b) (ha : ABound F gj gi a) :
    (flipsTo (ordinaryParent S F ti gi qi) false x).card ≤ 
      max (2*m) (m+b) + if qi=q then (degree-q)*a else 0 := by
  have htarget := targetBits_conditional_card F ti tj tk x v m b hm hb hv.1 hmiss
  by_cases hslack : (guardFailures S F gj x v).card <  qi
  · have h := (Finset.card_le_card (ordinary_destroying_subset_of_slack
      S F hF ti tj gi gj ht hg qi q hq x v hv hslack)).trans htarget
    exact h.trans (Nat.le_add_right _ _)
  · have he : qi=q := by have hh := hv.2; omega
    have hc : (guardFailures S F gj x v).card = q := by have hh := hv.2; omega
    rw [if_pos he]
    calc
      _ ≤  (targetBits F ti x v ∪ ordinaryGuardBits S F gi gj x v).card :=
        Finset.card_le_card (ordinary_destroying_subset S F hF ti tj gi gj ht hg qi q hq x v hv)
      _ ≤  (targetBits F ti x v).card+(ordinaryGuardBits S F gi gj x v).card := Finset.card_union_le _ _
      _ ≤  _ := Nat.add_le_add htarget (by
        simpa only [hdegree,hc] using ordinaryGuardBits_card_le S F gi gj x v a ha)



























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
  (ti tj tk gi gj : L)
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
  (hmiss :
    @Exists.{1} Bool fun (c : Bool) =>
      @Eq.{1} Bool (F tk (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v c)) Bool.false)
  (degree m b a : Nat)
  (hdegree :
    @Eq.{1} Nat (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundPositive.outgoing L I V inst_2 S v)) degree)
  (hm : @Sensitivity213981Formal.ThreeBoundProfiles.MBound L I inst_1 F ti tj tk m)
  (hb : @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst_1 F ti tk b)
  (ha : @Sensitivity213981Formal.ThreeBoundProfiles.ABound L I inst_1 F gj gi a),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
        (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_2 Bool.fintype) inst_1)
        (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryParent L I V inst_2 S F ti gi qi) Bool.false x))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@Max.max.{0} Nat Nat.instMax
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m b))
      (@ite.{1} Nat (@Eq.{1} Nat qi q) (instDecidableEqNat qi q)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) degree q) a)
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) := @Sensitivity213981Formal.ThreeBoundConditional.ordinary_target_defect_down
