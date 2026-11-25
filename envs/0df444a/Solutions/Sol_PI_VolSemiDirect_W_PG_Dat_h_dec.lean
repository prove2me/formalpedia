-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.h_dec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:03:02.525093+00:00
-- url     : https://prove2.me/submissions/32709d66-3a98-4fbc-9cdd-ec0569fd4811

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianIsotropicProjComplement
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_hermitian_isotropic_proj_complement
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_W_pU
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_add_left
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_add_right
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_isW_pW
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pW_apply


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
theorem _root_.solution (H : D.Hyp) (x y : n → A) :
    D.h x y = D.h (D.pU x) (D.pU y) + D.h (D.pW x) (D.pW y) := by
  have ex : x = D.pU x + D.pW x := by rw [pW_apply]; abel
  have ey : y = D.pU y + D.pW y := by rw [pW_apply]; abel
  conv_lhs => rw [ex, ey]
  rw [h_add_left, h_add_right, h_add_right, hermitian_isotropic_proj_complement H (isW_pW H y), h_W_pU H (isW_pW H x)]
  ring
end PI.VolSemiDirect.W.PG.Dat
