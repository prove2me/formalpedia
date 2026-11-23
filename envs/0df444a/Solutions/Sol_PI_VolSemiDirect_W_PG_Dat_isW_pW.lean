-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.isW_pW
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:58:01.393536+00:00
-- url     : https://prove2.me/submissions/f18830c2-171f-4576-a354-7891e3f84c9b

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_sub_right
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pW_apply
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
theorem _root_.solution (H : D.Hyp) (v : n → A) : IsW D (D.pW v) := by
  exact ⟨fun a => by rw [pW_apply, h_sub_right, h_e_pU H, sub_self],
    fun a => by rw [pW_apply, h_sub_right, h_f_pU H, sub_self],
    by rw [pW_apply, h_sub_right, h_z_pU H, sub_self]⟩
end PI.VolSemiDirect.W.PG.Dat
