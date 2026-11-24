-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCCusp_qf_nonneg_d6a602480fda
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:13.829986+00:00
-- url     : https://prove2.me/submissions/c0666443-de0f-4af7-baa7-a2e8dd3b771b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_HermValueIsLeast
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCCusp
open Matrix GroundTheory.Heights₂.Heights.MCSchur
noncomputable section
variable {ι : Type*} [Fintype ι]
namespace GroundTheory.Heights₂.Heights.MCCusp
theorem _root_.solution {Z : Matrix ι ι ℝ} (hZ : Z.PosSemidef) (u : ι → ℝ) : 0 ≤ qf Z u := by
  have := hZ.dotProduct_mulVec_nonneg u
  simpa [qf] using this
end GroundTheory.Heights₂.Heights.MCCusp
