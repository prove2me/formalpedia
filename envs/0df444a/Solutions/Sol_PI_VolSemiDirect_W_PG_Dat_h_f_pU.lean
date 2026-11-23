-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.h_f_pU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:50:36.401306+00:00
-- url     : https://prove2.me/submissions/dba2ecc3-b16b-48ef-abe3-d3f035f4ac12

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_add_right
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_smul_right
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_sum_right
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_fe
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pX_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pXv_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pz_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pU_apply

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
variable (D : Dat A n r)
variable {D}
variable (D)
variable {D}
namespace PI.VolSemiDirect.W.PG.Dat
theorem _root_.solution (H : D.Hyp) (a : Fin r) (v : n → A) : D.h (D.f a) (D.pU v) = D.h (D.f a) v := by
  simp [pU_apply, pX_apply, pXv_apply, pz_apply, h_add_right, h_sum_right, h_smul_right, fe H, H.ff, H.fz]
end PI.VolSemiDirect.W.PG.Dat
