-- Prove2me | solution 1 for P2M_GlobalTheory_Cube_trunc_Incl_bijective_7f26f77d74d4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:04:30.231907+00:00
-- url     : https://prove2.me/submissions/617b19ab-3484-412d-8a38-aed054766bd1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex
universe v u
open GlobalTheory
open GlobalTheory.Cube
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R : Type u} [Ring R]
namespace GlobalTheory.Cube
theorem _root_.solution (A : Cube.{v} ι R) {s : Finset ι} (hs : s.Nonempty) :
    Function.Bijective ((trunc₁Incl A).app s).hom :=
  (suppIncl_app A ordConnected_nonempty isUpperSet_nonempty hs) ▸
    (suppEquiv A ordConnected_nonempty hs).bijective
end GlobalTheory.Cube
