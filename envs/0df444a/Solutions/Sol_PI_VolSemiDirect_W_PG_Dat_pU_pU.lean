-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.pU_pU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:58:01.321628+00:00
-- url     : https://prove2.me/submissions/3a00deb4-ec64-4aa4-b550-d44fca135d14

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pX_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pXv_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pz_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pU_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_e_pU
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_f_pU
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_z_pU

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
theorem _root_.solution (H : D.Hyp) (v : n → A) : D.pU (D.pU v) = D.pU v := by
  rw [pU_apply D (D.pU v), pX_apply D (D.pU v), pXv_apply D (D.pU v), pz_apply D (D.pU v)]
  simp only [h_f_pU H, h_e_pU H, h_z_pU H]
  rw [← pX_apply, ← pXv_apply, ← pz_apply, ← pU_apply]
end PI.VolSemiDirect.W.PG.Dat
