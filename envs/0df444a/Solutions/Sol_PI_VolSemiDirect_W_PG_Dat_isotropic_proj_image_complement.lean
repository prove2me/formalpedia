-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.isotropic_proj_image_complement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:53:51.198784+00:00
-- url     : https://prove2.me/submissions/3fee4da1-233c-4d8c-9fea-b70f9a4794f0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianIsotropicProjComplement
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_e_S
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_z_S
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pU_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pXv_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pz_apply


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
theorem _root_.solution {S : (n → A) →ₗ[A] (n → A)} (hS : D.FixEZ S) (hU : D.Uni S) {w : n → A}
    (hw : IsW D w) : D.pU (S w) = D.pX (S w) := by
  rw [pU_apply, pXv_apply, pz_apply]
  simp [h_e_S hS hU, h_z_S hS hU, hw.1, hw.2.2]
end PI.VolSemiDirect.W.PG.Dat
