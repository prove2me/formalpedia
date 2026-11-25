-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SymplCons_proof_e1b11fc7b5f9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:53:59.223948+00:00
-- url     : https://prove2.me/submissions/8dd02da8-deac-4855-bd9a-66cc1d4d04d4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplCons
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplCons_symplOmega_eq_sum_d38ace7a12fb

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
open PSymplCons
namespace GroundTheory.Heights₂.Heights
namespace SymplCons
theorem _root_.solution : SymplCons.Statement := by
  intro R _ n
  refine ⟨fun u => ?_, fun p q p' q' w w' => ?_⟩
  · funext x
    rcases x with i | i <;> refine Fin.cases ?_ (fun j => ?_) i <;> simp [symplCons, symplTail]
  · rw [symplOmega_eq_sum, symplOmega_eq_sum, Fin.sum_univ_succ]
    simp [symplCons]
end SymplCons
end GroundTheory.Heights₂.Heights
