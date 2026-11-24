-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereLawBasic_firstRow_apply_5143842c4916
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:50.718742+00:00
-- url     : https://prove2.me/submissions/27d79ef0-daa6-4516-b182-5d645f9dcb6f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSphereLawBasic

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
open MeasureTheory ProbabilityTheory
noncomputable section
open GroundTheory.Heights₂.Heights.SphereLawBasic
namespace GroundTheory.Heights₂.Heights.SphereLawBasic
theorem _root_.solution (N : ℕ) (u : Fin 1 × Fin N → ℂ) (j : Fin N) : firstRow N u j = u (0, j) :=
  rfl
end GroundTheory.Heights₂.Heights.SphereLawBasic
