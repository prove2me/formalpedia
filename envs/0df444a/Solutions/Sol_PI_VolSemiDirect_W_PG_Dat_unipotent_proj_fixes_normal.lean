-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.unipotent_proj_fixes_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:18:35.684141+00:00
-- url     : https://prove2.me/submissions/386cc884-06f0-4292-9445-5d54d623842e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianIsotropicProjComplement
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_Pi_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_orthogonal_proj_normal_zero
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pU_z_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.PG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
open PI.VolSemiDirect.W.PG.Dat
variable {D : Dat A n r}
namespace PI.VolSemiDirect.W.PG.Dat
theorem _root_.solution (H : D.Hyp) (S : (n → A) →ₗ[A] (n → A)) : D.Pi S D.z = D.z := by
  rw [Pi_apply, pU_z_eq H, orthogonal_proj_normal_zero H, map_zero, map_zero, add_zero]
end PI.VolSemiDirect.W.PG.Dat
