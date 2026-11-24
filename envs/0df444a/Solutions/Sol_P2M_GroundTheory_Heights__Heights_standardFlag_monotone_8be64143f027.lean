-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_standardFlag_monotone_8be64143f027
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:58.724387+00:00
-- url     : https://prove2.me/submissions/da8ddc44-0eaf-4417-b3f3-255435f53dd1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField TensorProduct ComplexAt
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution : Monotone (standardFlag K) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [standardFlag]
end GroundTheory.Heights₂.Heights
