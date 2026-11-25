-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_RuleSS_mem__b_cce97eb16fae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:38:12.711566+00:00
-- url     : https://prove2.me/submissions/c53968b9-0fa8-40bc-9417-e09ea6e44b6c

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RuleSS
open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData
variable {A : Type} [Ring A] [Algebra ℂ A]
variable {r : ℕ} (L : LevelData A r)
namespace Formalism.FourierDecayAlt.P.RuleSS
theorem _root_.solution : L.ζb ∈ L.fns := by simp [LevelData.fns]
end Formalism.FourierDecayAlt.P.RuleSS
