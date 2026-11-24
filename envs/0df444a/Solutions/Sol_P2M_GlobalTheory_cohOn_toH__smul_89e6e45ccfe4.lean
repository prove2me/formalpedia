-- Prove2me | solution 1 for P2M_GlobalTheory_cohOn_toH__smul_89e6e45ccfe4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:31:22.873675+00:00
-- url     : https://prove2.me/submissions/2dacddc9-8ffc-40d4-bc3e-ab1e44bbe415

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
variable {R}
namespace GlobalTheory.cohOn
theorem _root_.solution {F : X.Modules} {U : X.Opens} {n : ℕ} (r : R) (x : cohOn F U n) :
    toH' F U n (r • x) =
      SiteCoh.map ((toAbSheaf X).map (smulHom F (algebraMap R Γ(X, ⊤) r))) n U (toH' F U n x) :=
  (WithAction.toBase_smul (action F U n) r x).trans (action_apply F U n _ _)
end GlobalTheory.cohOn
