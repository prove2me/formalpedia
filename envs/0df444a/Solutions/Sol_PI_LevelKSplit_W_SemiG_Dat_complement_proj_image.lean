-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.complement_proj_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:57:30.936655+00:00
-- url     : https://prove2.me/submissions/0a6d4a77-2c41-4771-bae1-7b0eadcb526e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HermitianIsotropicProjComplement
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_isotropic_proj_image_complement

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
theorem _root_.solution {S : (n → A) →ₗ[A] (n → A)} (hW : D.MapW S) {w : n → A} (hw : IsW D w) :
    D.pW (S w) = S w - D.pX (S w) := by
  simp only [pW, LinearMap.sub_apply, LinearMap.id_apply]
  rw [isotropic_proj_image_complement hW hw]
end PI.LevelKSplit.W.SemiG.Dat
