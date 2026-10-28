-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundConditional.strict_incoming_repair
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T19:41:08.687989+00:00
-- url     : https://prove2.me/submissions/02122a25-d74c-43c2-b957-f531050158e6

import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_StrictPositive
import Definitions.Def_Sensitivity213981Formal_StrictUnion
import Definitions.Def_Sensitivity213981Formal_WitnessLifting
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
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













@[simp] theorem mem_guardFailures (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (g : L) (x : ((V × Bool) × I) → Bool) (v w : V) :
    w ∈ guardFailures S F g x v ↔ S.Adj v w ∧ F g (child x w (S.label v w)) = true := by
  simp [guardFailures]





























































end
end ThreeBoundConditional




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Strict conditional union transfer for actual Boolean rows and parents. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false

namespace ThreeBoundConditional
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped BigOperators Classical
noncomputable section

variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

theorem zero_row_guard_false (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (x : ((V × Bool) × I) → Bool) (v : V)
    (hv : ordinaryRow S F t g 0 x v) (w : V) (hvw : S.Adj v w) :
    F g (child x w (S.label v w)) = false := by
  have hempty : guardFailures S F g x v = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hv.2)
  cases hf : F g (child x w (S.label v w)) with
  | false => rfl
  | true =>
    have hm := (mem_guardFailures S F g x v w).2 ⟨hvw,hf⟩
    rw [hempty] at hm
    exact False.elim (Finset.notMem_empty _ hm)



































end
end ThreeBoundConditional



end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Refined strict conditional positive transfer, including source-labeled cap. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false

namespace ThreeBoundConditional
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped BigOperators Classical
noncomputable section

variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]













/-- Cross winners incoming to the fixed weak row destroy a selected guard child. -/
theorem strict_incoming_repair (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (tj gj tl gl : L) (hgt : gl ≤  tj)
    (x : ((V × Bool) × I) → Bool) (p v w : V) (c : Bool) (a : I)
    (hp : ordinaryRow S F tj gj 0 x p) (hvp : S.Adj v p)
    (hv : ordinaryRow S F tl gl 0 (_root_.OAI.Paper320.flip x {((w,c),a)}) v) :
    ((w,c),a) ∈ targetBits F gl x p := by
  have hz := zero_row_guard_false S F tl gl _ v hv p hvp
  have hloc : (p,S.label v p)=(w,c) := by
    by_contra hn
    rw [child_flip_other x w p c (S.label v p) a hn] at hz
    have ht := hF _ _ hgt _ (hp.1 (S.label v p))
    rw [hz] at ht
    contradiction
  have hpw : p=w := congrArg Prod.fst hloc
  subst w
  have hc : S.label v p=c := congrArg Prod.snd hloc
  rw [hc,child_flip_same] at hz
  have hm : a ∈ flipsTo (F gl) false (child x p c) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩
  cases c
  · exact Finset.mem_union_left _ ((mem_liftBits _ _ _ _ _ _).2 ⟨rfl,rfl,hm⟩)
  · exact Finset.mem_union_right _ ((mem_liftBits _ _ _ _ _ _).2 ⟨rfl,rfl,hm⟩)























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
  (tj gj tl gl : L)
  (hgt :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      gl tj)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (p v w : V) (c : Bool) (a : I)
  (hp :
    @Sensitivity213981Formal.ThreeBoundConditional.ordinaryRow L I V inst_2 S F tj gj
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x p)
  (hvp : @Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj L I V S v p)
  (hv :
    @Sensitivity213981Formal.ThreeBoundConditional.ordinaryRow L I V inst_2 S F tl gl
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@OAI.Paper320.flip (Prod.{0, 0} (Prod.{0, 0} V Bool) I) x
        (@Singleton.singleton.{0, 0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
          (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
          (@Finset.instSingleton.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
          (@Prod.mk.{0, 0} (Prod.{0, 0} V Bool) I (@Prod.mk.{0, 0} V Bool w c) a)))
      v),
  @Membership.mem.{0, 0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I) (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
    (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
      (Prod.{0, 0} (Prod.{0, 0} V Bool) I) (@Finset.instSetLike.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)))
    (@Sensitivity213981Formal.ThreeBoundPositive.targetBits L I V inst_1 F gl x p)
    (@Prod.mk.{0, 0} (Prod.{0, 0} V Bool) I (@Prod.mk.{0, 0} V Bool w c) a) := @Sensitivity213981Formal.ThreeBoundConditional.strict_incoming_repair
