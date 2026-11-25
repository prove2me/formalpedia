-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.Pi_f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:57:55.874186+00:00
-- url     : https://prove2.me/submissions/2117efd9-7920-4ba8-90b9-c66d1a3ed2ec

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HermitianIsotropicProjComplement
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pU_f
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pW_f


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
theorem _root_.solution (H : D.Hyp) (S : (n → A) →ₗ[A] (n → A)) (a : Fin r) : D.Pi S (D.f a) = D.f a := by
  simp only [Pi, LinearMap.add_apply, LinearMap.comp_apply, pU_f H, pW_f H, map_zero, add_zero]
end PI.LevelKSplit.W.SemiG.Dat
