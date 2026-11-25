-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isDegZeroSmooth_const_9ac4e995dbbc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:41:46.36827+00:00
-- url     : https://prove2.me/submissions/f0042ed6-d8ca-45b5-b24f-0e642c000744

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StokesObjects

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (a : ℝ) : IsDegZeroSmooth (ι := ι) (fun _ => a) :=
  ⟨contDiffOn_const, fun _ _ _ => rfl⟩
end GroundTheory.Heights₂.Heights
