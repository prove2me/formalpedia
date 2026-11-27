-- Prove2me | solution 2 for P2M_GlobalTheory_algebra_OfHom_algebraMap_6568cc1e9975
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:52:21.568206+00:00
-- url     : https://prove2.me/submissions/82327aeb-47c6-4cb6-9e09-e21cf98ea8cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ToAbSheafPreservesFiniteLimits
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton

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
theorem _root_.solution {R : Type u} [CommRing R] (f : X ⟶ Spec (.of R)) (r : R) :
    letI := algebraΓOfHom f
    algebraMap R Γ(X, ⊤) r = f.appTop ((Scheme.ΓSpecIso (.of R)).inv r) := rfl
end GlobalTheory
