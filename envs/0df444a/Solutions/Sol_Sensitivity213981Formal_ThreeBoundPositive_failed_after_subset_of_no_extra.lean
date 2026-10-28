-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundPositive.failed_after_subset_of_no_extra
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T18:27:56.365524+00:00
-- url     : https://prove2.me/submissions/e696ba9f-bfd1-42cf-9f24-6001714ad1e2

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_Supplement_GradedPositiveBoundary
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





/-- If no previously passing guard is activated, the old strong count suffices. -/
theorem failed_after_subset_of_no_extra (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (hg : S.guard j ≤  S.guard i)
    (x : ((V × Bool) × I) → Bool) (v w : V) (c : Bool) (a : I)
    (he : ¬ ExtraFailure S F i j x v w c a) :
    failed S F i (_root_.OAI.Paper320.flip x {((w,c),a)}) v ⊆ failed S F j x v := by
  classical
  intro z hz
  rcases Finset.mem_filter.mp hz with ⟨_, hR, hf⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, hR, ?_⟩
  by_cases hp : (z, S.label v z) = (w,c)
  · have hzw : z = w := congrArg Prod.fst hp
    have hl : S.label v z = c := congrArg Prod.snd hp
    subst z
    rw [hl, child_flip_same] at hf
    cases hb : F (S.guard j) (child x w c) with
    | true => simpa only [hl] using hb
    | false => exact False.elim (he ⟨hR, hl, hb, hf⟩)
  · rw [child_flip_other x w z c (S.label v z) a hp] at hf
    exact hF _ _ hg _ hf









































end
end ThreeBoundPositive






end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {L I V : Type} [inst : Preorder.{0} L] [Fintype.{0} I] [inst_2 : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage L I V) (F : L → (I → Bool) → Bool)
  (hF : @Sensitivity213981Formal.ThreeBoundProfiles.Nested L I inst F) (i j : L)
  (hg :
    @LE.le.{0} L (@Preorder.toLE.{0} L inst) (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S j)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S i))
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (v w : V) (c : Bool) (a : I)
  (he : Not (@Sensitivity213981Formal.ThreeBoundPositive.ExtraFailure L I V S F i j x v w c a)),
  @LE.le.{0} (Finset.{0} V)
    (@Preorder.toLE.{0} (Finset.{0} V) (@PartialOrder.toPreorder.{0} (Finset.{0} V) (@Finset.instPartialOrder.{0} V)))
    (@Sensitivity213981Formal.ThreeBoundWitness.failed L I V inst_2 S F i
      (@OAI.Paper320.flip (Prod.{0, 0} (Prod.{0, 0} V Bool) I) x
        (@Singleton.singleton.{0, 0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
          (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
          (@Finset.instSingleton.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
          (@Prod.mk.{0, 0} (Prod.{0, 0} V Bool) I (@Prod.mk.{0, 0} V Bool w c) a)))
      v)
    (@Sensitivity213981Formal.ThreeBoundWitness.failed L I V inst_2 S F j x v) := @Sensitivity213981Formal.ThreeBoundPositive.failed_after_subset_of_no_extra
