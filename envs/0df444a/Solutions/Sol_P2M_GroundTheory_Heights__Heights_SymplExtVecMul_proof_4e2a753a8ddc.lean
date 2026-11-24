-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SymplExtVecMul_proof_4e2a753a8ddc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:24.810289+00:00
-- url     : https://prove2.me/submissions/e397a688-0c84-4596-b17d-83d0df64d2e3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplExtVecMul

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
namespace GroundTheory.Heights₂.Heights
namespace SymplExtVecMul
theorem _root_.solution : SymplExtVecMul.Statement := by
  intro R _ n α β γ δ p q Q w
  funext y
  rcases y with y | y <;> refine Fin.cases ?_ (fun j => ?_) y <;>
    simp [vecMul, dotProduct, symplCons, symplExt, Fintype.sum_sum_type, Fin.sum_univ_succ]
end SymplExtVecMul
end GroundTheory.Heights₂.Heights
