-- Prove2me | solution 1 for P2M_GlobalTheory_Cube_subsingleton_trunc__e70445e4868d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:04:24.56791+00:00
-- url     : https://prove2.me/submissions/403fe540-5b44-4406-9677-f33ce0242be5

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
    (h : s = ∅ ∨ t = ∅) : Subsingleton ((trunc₂ A).obj (sumVertex s t)) :=
  subsingleton_supp A (ordConnected_partsIn _ _ ordConnected_nonempty ordConnected_nonempty)
    (by rcases h with rfl | rfl <;> simp)
end GlobalTheory.Cube
