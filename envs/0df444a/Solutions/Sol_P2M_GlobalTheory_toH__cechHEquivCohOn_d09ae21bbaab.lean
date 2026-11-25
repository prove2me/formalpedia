-- Prove2me | solution 1 for P2M_GlobalTheory_toH__cechHEquivCohOn_d09ae21bbaab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:04:59.260024+00:00
-- url     : https://prove2.me/submissions/60b80d86-3a54-49a4-b7f5-faece3677a31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PresheafCubeExactAtSuccOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsAddEquivOfSurjectiveOfKerIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CechModulesFunctorShortExactOfAcyclic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite
universe v u
noncomputable section
open GlobalTheory
variable {X : Scheme.{u}} {ι : Type}
variable {V : X.Opens} {U : ι → X.Opens} {F G : X.Modules}
variable [LinearOrder ι] (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]
variable [Finite ι] (hc : V ≤ ⨆ i, U i)
namespace GlobalTheory
theorem _root_.solution (hF : CechAcyclicMod V U F) (n : ℕ) (x : cechAbH F.presheaf V U n) :
    cohOn.toH' F V n (cechHEquivCohOn R hc hF n (cechAbHEquiv R F V U n x)) =
      cechAbHEquivH' (T := X.toPresheafedSpace.carrier) hc (cechAcyclicMod_iff.1 hF) n x :=
  toH'_cechHAddEquivCohOn R hc hF n x
end GlobalTheory
