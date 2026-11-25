-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HadamardPSDAux_det_eq_zero_of_diag_eq_zero_459d5de6f62b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:25:29.285519+00:00
-- url     : https://prove2.me/submissions/76805414-2e07-493b-83f0-dfbfc4aecd15

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHadamardPSD

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
open Matrix Finset
open scoped ComplexOrder
open GroundTheory.Heights₂.Heights.HadamardPSDAux
namespace GroundTheory.Heights₂.Heights.HadamardPSDAux
theorem _root_.solution {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef)
    {i : Fin n} (hi : A i i = 0) : A.det = 0 := by
  have h0 : star (Pi.single i (1 : ℂ)) ⬝ᵥ A *ᵥ Pi.single i 1 = 0 := by
    simpa using hi
  have hcol := (hA.dotProduct_mulVec_zero_iff _).mp h0
  refine det_eq_zero_of_column_eq_zero i fun k => ?_
  simpa using congrFun hcol k
end GroundTheory.Heights₂.Heights.HadamardPSDAux
