-- Prove2me | solution 1 for P2M_GlobalTheory_Cube_trunc_Incl_bijective_15000a487b45
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:56:39.039836+00:00
-- url     : https://prove2.me/submissions/6c51d738-507a-4fd9-b6c9-88746cba9052

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
theorem _root_.solution (A : Cube.{v} (ι ⊕ₗ κ) R) {s : Finset ι} {t : Finset κ}
    (hs : s.Nonempty) (ht : t.Nonempty) :
    Function.Bijective ((trunc₂Incl A).app (sumVertex s t)).hom :=
  have h : sumVertex s t ∈ partsIn (inlEmb ι κ) (inrEmb ι κ) {s | s.Nonempty} {t | t.Nonempty} := by
    simp [hs, ht]
  (suppIncl_app A (ordConnected_partsIn _ _ ordConnected_nonempty ordConnected_nonempty)
    (isUpperSet_partsIn_nonempty _ _) h) ▸ (suppEquiv A _ h).bijective
end GlobalTheory.Cube
