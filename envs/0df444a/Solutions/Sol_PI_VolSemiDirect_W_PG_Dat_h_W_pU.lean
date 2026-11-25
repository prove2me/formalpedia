-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.h_W_pU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:50:10.457392+00:00
-- url     : https://prove2.me/submissions/de74a5f0-de2a-4e91-b3b1-cbafe7f4b973

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianIsotropicProjComplement
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_hermitian_isotropic_proj_complement
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_symm


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
theorem _root_.solution (H : D.Hyp) {w : n → A} (hw : IsW D w) (x : n → A) : D.h w (D.pU x) = 0 := by
  rw [h_symm H, hermitian_isotropic_proj_complement H hw, map_zero]
end PI.VolSemiDirect.W.PG.Dat
