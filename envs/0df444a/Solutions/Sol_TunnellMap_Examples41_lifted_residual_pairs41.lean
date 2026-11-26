-- Prove2me | solution 1 for TunnellMap.Examples41.lifted_residual_pairs41
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:47:43.317711+00:00
-- url     : https://prove2.me/submissions/b7d6c198-6b37-4f8d-939e-4cc1545207cb

import Definitions.Def_TunnellMap_Examples41Generator
import Definitions.Def_TunnellMap_Sharpness
import Definitions.Def_TunnellMap_Examples41Matching
import Theorems.Thm_TunnellMap_Examples41_preferredTarget_s2_t2
import Theorems.Thm_TunnellMap_Examples41_preferredTarget_s3_t4
import Theorems.Thm_TunnellMap_Examples41_preferredTarget_s4_t3
import Theorems.Thm_TunnellMap_Examples41_signed_orbit_edge_prefers_negative_target


set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open GloballyRanked
set_option maxRecDepth 10000
namespace TunnellMap.Examples41
theorem _root_.solution :
    residualTargetLift (preferredTarget s1 t1) = ⟨4, 3, 0⟩ ∧
      residualTargetLift (preferredTarget s2 t2) = ⟨4, -3, 0⟩ ∧
      residualTargetLift (preferredTarget s3 t4) = ⟨0, -3, 4⟩ ∧
      residualTargetLift (preferredTarget s4 t3) = ⟨0, -3, -4⟩ := by
  rw [signed_orbit_edge_prefers_negative_target, preferredTarget_s2_t2,
    preferredTarget_s3_t4, preferredTarget_s4_t3]
  norm_num [negAResidual, negA, negTriple, residualTargetLift, aLift,
    t1, t2, t3, t4]
end TunnellMap.Examples41
