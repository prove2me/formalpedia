-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_firstCoordVec_eq_basisFun_7b02b35d9e45
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:39:52.719611+00:00
-- url     : https://prove2.me/submissions/401e8ae5-8d61-4705-b93d-2d3ec72debd5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentGaussInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PTangentGaussInvariant

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
open MeasureTheory Module
open scoped Matrix
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n : ℕ} (hn : 0 < n) :
    firstCoordVec n = EuclideanSpace.basisFun (Fin n) ℂ ⟨0, hn⟩ := by
  ext j
  simp [firstCoordVec, EuclideanSpace.basisFun_apply, Fin.ext_iff]
end GroundTheory.Heights₂.Heights
