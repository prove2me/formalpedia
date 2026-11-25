-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_R_LevelData_inv_mem___78c8e7adc78b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:38:12.682877+00:00
-- url     : https://prove2.me/submissions/02c14b08-2a0e-447f-98e8-0f374eb0a252

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.PInv
open Matrix LevelData
variable {A : Type} [Ring A] [Algebra ℂ A]
variable {r : ℕ} (L : LevelData A r)
namespace Formalism.FourierDecayAlt.R.PInv
namespace _root_.Formalism.FourierDecayAlt.R.LevelData
theorem _root_.solution : L.ζ ∈ L.fns := by simp [LevelData.fns]
end _root_.Formalism.FourierDecayAlt.R.LevelData
end Formalism.FourierDecayAlt.R.PInv
