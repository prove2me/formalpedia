-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplOrbit_symplCons_one_zero_81f42b193b60
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:46:09.671831+00:00
-- url     : https://prove2.me/submissions/4633c873-b419-43d7-9195-48b063da591c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplOrbit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
open GroundTheory.Heights₂.Heights.PSymplOrbit
namespace GroundTheory.Heights₂.Heights.PSymplOrbit
theorem _root_.solution {R : Type*} [CommRing R] {n : ℕ} :
    symplCons (1 : R) 0 (0 : Fin n ⊕ Fin n → R) = Pi.single (Sum.inl 0) 1 := by
  funext x
  rcases x with i | i <;> refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [symplCons, Fin.succ_ne_zero]
end GroundTheory.Heights₂.Heights.PSymplOrbit
