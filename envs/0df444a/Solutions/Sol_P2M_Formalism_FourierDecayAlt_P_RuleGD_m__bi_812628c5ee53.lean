-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_RuleGD_m__bi_812628c5ee53
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:41:28.807327+00:00
-- url     : https://prove2.me/submissions/965e68e8-5748-4d16-b965-0ce9d4dfa06d

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
theorem _root_.solution : L.ζbi ∈ L.fns := by simp [LevelData.fns]
end Formalism.FourierDecayAlt.P.RuleGD
