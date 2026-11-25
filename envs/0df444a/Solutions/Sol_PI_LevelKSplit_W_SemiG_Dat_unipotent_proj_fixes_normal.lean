-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.unipotent_proj_fixes_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:00:46.597061+00:00
-- url     : https://prove2.me/submissions/ffb375d3-7d06-4d30-8d88-fe1a140ba0f8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HermitianIsotropicProjComplement
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_orthogonal_proj_normal_zero
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pU_z_eq


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
theorem _root_.solution (H : D.Hyp) (S : (n → A) →ₗ[A] (n → A)) : D.Pi S D.z = D.z := by
  simp only [Pi, LinearMap.add_apply, LinearMap.comp_apply, pU_z_eq H, orthogonal_proj_normal_zero H, map_zero, add_zero]
end PI.LevelKSplit.W.SemiG.Dat
