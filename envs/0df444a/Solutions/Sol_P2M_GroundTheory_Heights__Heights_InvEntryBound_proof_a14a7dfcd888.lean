-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_InvEntryBound_proof_a14a7dfcd888
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:57:22.785548+00:00
-- url     : https://prove2.me/submissions/7bf19c9c-ec5b-4792-9743-8358046f3dfd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PInvEntryBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCInvEntryBound_single_dot_mulVec_single_8f7831771cf8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCInvEntryBound_inv_diag_bounds_351d6c6385e7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_posDef_of_ge_c2392ab1fa43
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_quad_cs_de43f5f0f21c


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
namespace GroundTheory.Heights₂.Heights
namespace InvEntryBound
theorem _root_.solution : InvEntryBound.Statement := by
  intro g Y c hc h j l
  have hinv : (Y⁻¹).PosSemidef := (MCBounds.posDef_of_ge hc h).inv.posSemidef
  have hcs := MCBounds.quad_cs hinv (Pi.single j 1) (Pi.single l 1)
  simp only [MCInvEntryBound.single_dot_mulVec_single] at hcs
  obtain ⟨hj0, hj⟩ := MCInvEntryBound.inv_diag_bounds hc h j
  obtain ⟨hl0, hl⟩ := MCInvEntryBound.inv_diag_bounds hc h l
  have hci : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have hsq : (Y⁻¹ j l) ^ 2 ≤ c⁻¹ ^ 2 := by
    calc (Y⁻¹ j l) ^ 2 ≤ Y⁻¹ j j * Y⁻¹ l l := hcs
      _ ≤ c⁻¹ * c⁻¹ := mul_le_mul hj hl hl0 hci
      _ = c⁻¹ ^ 2 := (sq _).symm
  exact abs_le_of_sq_le_sq' hsq hci |> fun h => abs_le.mpr h
end InvEntryBound
end GroundTheory.Heights₂.Heights
