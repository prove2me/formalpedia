-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.h_span_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:50:37.458052+00:00
-- url     : https://prove2.me/submissions/ee2fcf01-7126-4e2d-b07c-2969bef0b4d8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HermitianIsotropicProjComplement
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_add_left
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_smul_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.SemiG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
open PI.LevelKSplit.W.SemiG.Dat
variable {D : Dat A n r}
namespace PI.LevelKSplit.W.SemiG.Dat
theorem _root_.solution {x y : n → A} (hx : x ∈ Submodule.span A (Set.range D.e))
    (hy : ∀ b, D.h (D.e b) y = 0) : D.h x y = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact hy a
  | zero => simp [Dat.h, hform]
  | add x x' _ _ h1 h2 => rw [h_add_left, h1, h2, add_zero]
  | smul c x _ h1 => rw [h_smul_left, h1, mul_zero]
end PI.LevelKSplit.W.SemiG.Dat
