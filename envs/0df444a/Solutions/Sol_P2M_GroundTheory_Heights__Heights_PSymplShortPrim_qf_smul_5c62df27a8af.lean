-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplShortPrim_qf_smul_5c62df27a8af
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:46:25.622166+00:00
-- url     : https://prove2.me/submissions/3eb9aa60-5295-4c56-baa2-8eaaf37bc718

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplShortPrim

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
open GroundTheory.Heights₂.Heights.PSymplShortPrim
namespace GroundTheory.Heights₂.Heights.PSymplShortPrim
theorem _root_.solution {ι : Type} [Fintype ι] (Y : Matrix ι ι ℝ) (c : ℝ) (x : ι → ℝ) :
    qf Y (c • x) = c ^ 2 * qf Y x := by
  simp only [qf, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring
end GroundTheory.Heights₂.Heights.PSymplShortPrim
