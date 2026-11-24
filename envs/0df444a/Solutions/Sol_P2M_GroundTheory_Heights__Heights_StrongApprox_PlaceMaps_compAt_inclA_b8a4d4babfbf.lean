-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_compAt_inclA_b8a4d4babfbf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:21.93132+00:00
-- url     : https://prove2.me/submissions/523e66eb-87d1-4508-b9ee-8e7d350b561f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PPlaceMaps
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_compAt_tmul_635eb167447d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_compAt_tmul_e1d8fccf6a3e


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
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct ReciprocityTheory.ChartRestriction.G.SA
open GroundTheory.Heights₂.Heights.StrongApprox.PlaceMaps
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]
namespace GroundTheory.Heights₂.Heights.StrongApprox.PlaceMaps
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (x : E) :
    compAt E v (inclA F E x) = inclV E v x := by
  show compAt E v (1 ⊗ₜ x) = 1 ⊗ₜ x
  rw [compAt_tmul, map_one]
end GroundTheory.Heights₂.Heights.StrongApprox.PlaceMaps
