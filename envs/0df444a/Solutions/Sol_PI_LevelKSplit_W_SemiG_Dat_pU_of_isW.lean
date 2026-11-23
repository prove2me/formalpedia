-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.pU_of_isW
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:19.414277+00:00
-- url     : https://prove2.me/submissions/4b83bb0c-8f9f-4ca4-98c9-064cfddf4de8

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pX_apply
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pXv_apply
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pz_apply
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pU_apply

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
theorem _root_.solution {w : n → A} (hw : IsW D w) : D.pU w = 0 := by
  obtain ⟨h1, h2, h3⟩ := hw
  rw [pU_apply, pX_apply, pXv_apply, pz_apply]
  simp [h1, h2, h3]
end PI.LevelKSplit.W.SemiG.Dat
