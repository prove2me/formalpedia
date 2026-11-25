-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PlueckerNormSqAlt_rowsOf_conjTranspose_e6b7b0baa3b1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:47:16.300706+00:00
-- url     : https://prove2.me/submissions/8035d8fe-3b46-427a-9fb4-60d723bf0f64

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PPlueckerNormSq

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
open Matrix Finset
noncomputable section
open GroundTheory.Heights₂.Heights.PlueckerNormSqAlt
namespace GroundTheory.Heights₂.Heights.PlueckerNormSqAlt
theorem _root_.solution {j N : ℕ} (A : Matrix (Fin j) (Fin N) ℂ)
    (I : {I : Finset (Fin N) // I.card = j}) : rowsOf Aᴴ I = (colsOf A I)ᴴ := by
  ext a b
  simp [rowsOf, colsOf, conjTranspose_apply]
end GroundTheory.Heights₂.Heights.PlueckerNormSqAlt
