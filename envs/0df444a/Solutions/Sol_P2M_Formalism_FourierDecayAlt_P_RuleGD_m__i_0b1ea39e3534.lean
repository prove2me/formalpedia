-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_RuleGD_m__i_0b1ea39e3534
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:41:39.550071+00:00
-- url     : https://prove2.me/submissions/c886afde-3c65-4641-bab1-b056453b9706

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RuleGD
open Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Matrix
variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}
variable (L : LevelData A r)
namespace Formalism.FourierDecayAlt.P.RuleGD
theorem _root_.solution : L.ζi ∈ L.fns := by simp [LevelData.fns]
end Formalism.FourierDecayAlt.P.RuleGD
