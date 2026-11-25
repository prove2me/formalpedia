-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.complement_proj_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:01:56.3409+00:00
-- url     : https://prove2.me/submissions/5d4479a9-4fe2-4ec3-b185-2509c579e021

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianIsotropicProjComplement
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_isotropic_proj_image_complement

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
    (hw : IsW D w) : D.pW (S w) = S w - D.pX (S w) := by
  rw [Dat.pW.eq_1, LinearMap.sub_apply, LinearMap.id_apply, isotropic_proj_image_complement hS hU hw]
end PI.VolSemiDirect.W.PG.Dat
