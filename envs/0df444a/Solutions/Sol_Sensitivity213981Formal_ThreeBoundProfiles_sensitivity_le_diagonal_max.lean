-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundProfiles.sensitivity_le_diagonal_max
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T18:31:58.218035+00:00
-- url     : https://prove2.me/submissions/1d0c2ba2-8285-41cb-b291-df07568a56f1

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_ProfileClosures
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset


namespace Sensitivity213981Formal
section
/-
Dimension-independent semantics and closure rules for the five sensitivity
profiles. These prove the local soundness of the closure operations, not the
raw graded/min-max transfer formulas or their finite case-table coverage.
-/


set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ThreeBoundProfiles
open OAI.Paper320
noncomputable section
open scoped Classical

variable {L I : Type} [Preorder L] [Fintype I]































































/-- The two diagonal profile bounds bound global sensitivity. -/
theorem sensitivity_le_diagonal_max (F : L → (I → Bool) → Bool) (i : L) (a b : ℕ)
    (ha : ABound F i i a) (hb : BBound F i i b) : _root_.OAI.Paper320.sensitivity (F i) ≤  max a b := by
  classical
  apply Finset.sup_le
  intro x _
  cases hx : F i x with
  | false =>
      have he : _root_.OAI.Paper320.sensitivityAt (F i) x = (flipsTo (F i) true x).card := by
        simp [_root_.OAI.Paper320.sensitivityAt, flipsTo, hx]
      rw [he]
      exact (ha x hx).trans (le_max_left _ _)
  | true =>
      have he : _root_.OAI.Paper320.sensitivityAt (F i) x = (flipsTo (F i) false x).card := by
        simp [_root_.OAI.Paper320.sensitivityAt, flipsTo, hx]
      rw [he]
      exact (hb x hx).trans (le_max_right _ _)

end
end ThreeBoundProfiles






end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {L I : Type} [Preorder.{0} L] [inst : Fintype.{0} I] (F : L → (I → Bool) → Bool) (i : L) (a b : Nat)
  (ha : @Sensitivity213981Formal.ThreeBoundProfiles.ABound L I inst F i i a)
  (hb : @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst F i i b),
  @LE.le.{0} Nat instLENat (@OAI.Paper320.sensitivity I inst (F i)) (@Max.max.{0} Nat Nat.instMax a b) := @Sensitivity213981Formal.ThreeBoundProfiles.sensitivity_le_diagonal_max
