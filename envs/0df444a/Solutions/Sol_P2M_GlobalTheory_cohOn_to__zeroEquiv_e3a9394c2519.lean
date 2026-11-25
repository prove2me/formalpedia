-- Prove2me | solution 1 for P2M_GlobalTheory_cohOn_to__zeroEquiv_e3a9394c2519
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:44:12.825927+00:00
-- url     : https://prove2.me/submissions/8438d4cf-2854-48bb-af31-7d9a5d85a8ad

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
open GlobalTheory.cohOn
variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]
variable {F G : X.Modules} {U V : X.Opens}
namespace GlobalTheory.cohOn
theorem _root_.solution (x : cohOn F U 0) :
    sectionsOn.toΓ F U (zeroEquiv R F U x) =
      SiteCoh.zeroEquiv ((toAbSheaf X).obj F) U (toH' F U 0 x) := rfl
end GlobalTheory.cohOn
