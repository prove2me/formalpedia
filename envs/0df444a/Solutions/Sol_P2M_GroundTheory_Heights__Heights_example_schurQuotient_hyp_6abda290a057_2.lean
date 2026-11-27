-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_example_schurQuotient_hyp_6abda290a057
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:10:42.421622+00:00
-- url     : https://prove2.me/submissions/111e8947-7d81-456e-97d5-90b9a8ce2690

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements

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
theorem _root_.solution :
    (Matrix.diagonal (Sum.elim (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => 2))).PosDef :=
  Matrix.posDef_diagonal_iff.mpr fun k => by cases k <;> norm_num
end GroundTheory.Heights₂.Heights
