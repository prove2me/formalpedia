-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundConditional.ordinary_destroying_subset
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T19:35:31.268654+00:00
-- url     : https://prove2.me/submissions/acdfcc9b-7130-4d08-af10-091c221ddb8f

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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_ordinary_destroying_cover
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundPositive_mem_liftBits


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




























@[simp] theorem mem_passingGuards (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (g : L) (x : ((V × Bool) × I) → Bool) (v w : V) :
    w ∈ passingGuards S F g x v ↔
      S.Adj v w ∧ F g (child x w (S.label v w)) = false := by
  simp only [passingGuards, outgoing, guardFailures, Finset.mem_sdiff,
    Finset.mem_filter, Finset.mem_univ, true_and]
  cases F g (child x w (S.label v w)) <;> simp













theorem ordinary_destroying_subset (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (ti tj gi gj : L)
    (ht : ti ≤  tj) (hg : gj ≤  gi) (qi q : ℕ) (hq : q ≤  qi)
    (x : ((V × Bool) × I) → Bool) (v : V) (hv : ordinaryRow S F tj gj q x v) :
    flipsTo (ordinaryParent S F ti gi qi) false x ⊆
      targetBits F ti x v ∪ ordinaryGuardBits S F gi gj x v := by
  intro p hp
  rcases p with ⟨⟨w,c⟩,a⟩
  have hoff := (Finset.mem_filter.mp hp).2
  rcases ordinary_destroying_cover S F hF ti tj gi gj ht hg qi q hq x v hv w c a hoff with hh | he
  · obtain ⟨hw,hf⟩ := hh
    subst w
    apply Finset.mem_union.mpr
    left
    have hm : a ∈ flipsTo (F ti) false (child x v c) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf⟩
    cases c
    · exact Finset.mem_union.mpr (Or.inl ((mem_liftBits _ _ _ _ _ _).2 ⟨rfl,rfl,hm⟩))
    · exact Finset.mem_union.mpr (Or.inr ((mem_liftBits _ _ _ _ _ _).2 ⟨rfl,rfl,hm⟩))
  · obtain ⟨hR,hl,hbefore,hafter⟩ := he
    apply Finset.mem_union.mpr
    right
    apply Finset.mem_biUnion.mpr
    refine ⟨w,(mem_passingGuards S F gj x v w).2 ⟨hR,?_⟩,?_⟩
    · simpa only [hl] using hbefore
    · apply (mem_liftBits _ _ _ _ _ _).2
      refine ⟨rfl,hl.symm,?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [hl] using hafter⟩
































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
  (hv : @Sensitivity213981Formal.ThreeBoundConditional.ordinaryRow L I V inst_2 S F tj gj q x v),
  @LE.le.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
    (@Preorder.toLE.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
      (@PartialOrder.toPreorder.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
        (@Finset.instPartialOrder.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))))
    (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_2 Bool.fintype) inst_1)
      (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryParent L I V inst_2 S F ti gi qi) Bool.false x)
    (@Union.union.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
      (@Finset.instUnion.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I) fun (a b : Prod.{0, 0} (Prod.{0, 0} V Bool) I) =>
        @instDecidableEqProd.{0, 0} (Prod.{0, 0} V Bool) I
          (fun (a b : Prod.{0, 0} V Bool) =>
            @instDecidableEqProd.{0, 0} V Bool (fun (a b : V) => Classical.propDecidable (@Eq.{1} V a b))
              instDecidableEqBool a b)
          (fun (a b : I) => Classical.propDecidable (@Eq.{1} I a b)) a b)
      (@Sensitivity213981Formal.ThreeBoundPositive.targetBits L I V inst_1 F ti x v)
      (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryGuardBits L I V inst_1 inst_2 S F gi gj x v)) := @Sensitivity213981Formal.ThreeBoundConditional.ordinary_destroying_subset
