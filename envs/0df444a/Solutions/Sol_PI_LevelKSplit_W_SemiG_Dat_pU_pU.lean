-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.pU_pU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:42:58.180328+00:00
-- url     : https://prove2.me/submissions/7ff437fd-ea33-4386-a357-c54b551cb1de

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pX_apply
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pXv_apply
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pz_apply
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pU_apply
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_e_pU
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_f_pU
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_z_pU

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
variable (D : Dat A n r)
variable {D}
variable (D)
variable {D}
namespace PI.LevelKSplit.W.SemiG.Dat
theorem _root_.solution (H : D.Hyp) (v : n → A) : D.pU (D.pU v) = D.pU v := by
  rw [D.pU_apply (D.pU v), D.pX_apply (D.pU v), D.pXv_apply (D.pU v), D.pz_apply (D.pU v)]
  simp only [h_e_pU H, h_f_pU H, h_z_pU H]
  rw [← D.pX_apply v, ← D.pXv_apply v, ← D.pz_apply v, ← D.pU_apply v]
end PI.LevelKSplit.W.SemiG.Dat
