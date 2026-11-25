-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_sigTop_mul_self_5c5b61b99b20
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:36:52.136631+00:00
-- url     : https://prove2.me/submissions/d159190a-b111-41ef-830f-248b490f5fa6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_FlagPsLine
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open Polynomial Matrix
noncomputable section
variable {N : ℕ}
variable (p i : ℕ) (hi : i ≤ N) (L : Matrix (Fin N) (Fin N) ℂ)
namespace GroundTheory.Heights₂.Heights.FourB
theorem _root_.solution : sigTop p i hi * sigTop p i hi = 1 := by
  rw [sigTop, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  unfold sigSign
  split_ifs <;> simp
end GroundTheory.Heights₂.Heights.FourB
