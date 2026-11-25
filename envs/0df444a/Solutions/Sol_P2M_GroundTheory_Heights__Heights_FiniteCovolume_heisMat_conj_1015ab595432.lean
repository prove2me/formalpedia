-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_conj_1015ab595432
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:54:26.418526+00:00
-- url     : https://prove2.me/submissions/01be5dbc-2da7-4286-b0ff-b78528878763

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusMatrix
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_mulVec_of_unitary_4c2fa1afaeb5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_matrix_ext_mulVec_52bd164b4cc0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_mulVec_debb3da7c3fb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open Matrix
noncomputable section
variable {ι : Type*} [Fintype ι]
variable [DecidableEq ι]
variable {H : Matrix ι ι ℂ} {a : ι → ℂ}
variable (hH : H.IsHermitian) (ha : hForm H a a = 0)
include hH ha
omit hH ha
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution {g : Matrix ι ι ℂ} (hg : gᴴ * H * g = H) (hga : g *ᵥ a = a) (y : ι → ℂ)
    (s : ℂ) : g * heisMat H a y s = heisMat H a (g *ᵥ y) s * g := by
  refine matrix_ext_mulVec fun z => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, heisMat_mulVec, heisMat_mulVec]
  conv_rhs => rw [← hga, hForm_mulVec_of_unitary H hg, hForm_mulVec_of_unitary H hg, hga]
  simp only [mulVec_add, mulVec_sub, mulVec_smul, hga]
end GroundTheory.Heights₂.Heights.FiniteCovolume
