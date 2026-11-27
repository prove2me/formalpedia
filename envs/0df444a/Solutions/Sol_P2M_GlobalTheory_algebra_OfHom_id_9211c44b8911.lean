-- Prove2me | solution 1 for P2M_GlobalTheory_algebra_OfHom_id_9211c44b8911
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:52:24.537362+00:00
-- url     : https://prove2.me/submissions/2256f994-d0ec-4b8c-a1b5-a49998085117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ToAbSheafPreservesFiniteLimits
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Theorems.Thm_GlobalTheory_restrictGlobal_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
universe t v u
noncomputable section
open GlobalTheory
variable {X : Scheme.{u}}
namespace GlobalTheory
theorem _root_.solution (R : Type u) [CommRing R] :
    algebraΓOfHom (𝟙 (Spec (.of R))) = algebraΓSpec (.of R) :=
  Algebra.algebra_ext _ _ fun r ↦ (restrictGlobal_top ((Scheme.ΓSpecIso (.of R)).inv r)).symm
end GlobalTheory
