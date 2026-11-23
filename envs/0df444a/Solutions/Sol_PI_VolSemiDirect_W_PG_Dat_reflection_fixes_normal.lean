-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.reflection_fixes_normal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:57:23.247892+00:00
-- url     : https://prove2.me/submissions/2fb93fb7-adea-43b7-8fb4-bacbcd1c27da

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ReflectionFixesNormal
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_L_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_smul_right
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_orthogonal_proj_normal_zero


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
theorem _root_.solution (H : D.Hyp) (w : Fin r → n → A) (s : Fin r → Fin r → A) : D.L w s D.z = D.z := by
  have hz0 : ∀ x, D.h x 0 = 0 := fun x => by simpa using h_smul_right (D := D) x 0 0
  simp [L_apply, orthogonal_proj_normal_zero H, H.ez, hz0]
end PI.VolSemiDirect.W.PG.Dat
