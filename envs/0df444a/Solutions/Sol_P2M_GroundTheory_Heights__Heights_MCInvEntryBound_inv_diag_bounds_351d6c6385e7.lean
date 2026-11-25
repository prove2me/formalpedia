-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCInvEntryBound_inv_diag_bounds_351d6c6385e7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:18:21.974186+00:00
-- url     : https://prove2.me/submissions/447ed604-8ae6-4ee2-beba-e1a7eb41ce3b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PInvEntryBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCInvEntryBound_single_dot_mulVec_single_8f7831771cf8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_inv_le_of_ge_22d5970a02ea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_posDef_of_ge_c2392ab1fa43
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_quad_nonneg_28912038225c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.MCInvEntryBound
namespace GroundTheory.Heights₂.Heights.MCInvEntryBound
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : Matrix ι ι ℝ} {c : ℝ}
    (hc : 0 < c) (h : (Y - c • (1 : Matrix ι ι ℝ)).PosSemidef) (j : ι) :
    0 ≤ Y⁻¹ j j ∧ Y⁻¹ j j ≤ c⁻¹ := by
  have hinv : (Y⁻¹).PosSemidef := (MCBounds.posDef_of_ge hc h).inv.posSemidef
  have hle := MCBounds.quad_nonneg (MCBounds.inv_le_of_ge hc h) (Pi.single j 1)
  have hge := MCBounds.quad_nonneg hinv (Pi.single j 1)
  rw [single_dot_mulVec_single] at hle hge
  refine ⟨hge, ?_⟩
  simpa [Matrix.sub_apply, Matrix.smul_apply] using hle
end GroundTheory.Heights₂.Heights.MCInvEntryBound
