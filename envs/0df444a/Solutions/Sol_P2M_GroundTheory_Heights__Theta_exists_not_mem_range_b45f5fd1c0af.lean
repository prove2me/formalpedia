-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_exists_not_mem_range_b45f5fd1c0af
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:55:57.460062+00:00
-- url     : https://prove2.me/submissions/86a5c70d-e97b-4697-ac85-e693b7ff882e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_QuadraticConj
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_CMDatum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open NumberField GroundTheory.Automorphic
variable (F E : Type*) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
  [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {F E}
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution : ∃ x : E, x ∉ Set.range (algebraMap F E) := by
  by_contra hall
  push Not at hall
  have hsurj : Function.Surjective (Algebra.linearMap F E) := fun x => hall x
  have h1 := LinearMap.finrank_range_le (Algebra.linearMap F E)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
    Algebra.IsQuadraticExtension.finrank_eq_two] at h1
  omega
end GroundTheory.Heights₂.Theta
