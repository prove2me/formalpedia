-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_mixedDiff_of_fin_zero_39ff712c69c1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:44.235877+00:00
-- url     : https://prove2.me/submissions/b3a4d2c8-69b3-42d3-95ff-d9d535f244c3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsDegLTGrowth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PDegLTGrowth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open GroundTheory.Heights₂.Heights.NumbersDVR
variable {K : Type} [Fintype K] [DecidableEq K]
omit [Fintype K] [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution (bs : Fin 0 → K → ℤ) (f : (K → ℤ) → ℤ) : mixedDiff bs f = f := by
  simp [mixedDiff]
end GroundTheory.Heights₂.Heights.HilbertSamuel
