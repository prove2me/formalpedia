-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplGramMem_gram_diag_bad6209e6409
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:46:01.420561+00:00
-- url     : https://prove2.me/submissions/5b7a16c5-06ea-4735-9ab6-f4fa398716aa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplGramMem

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
open GroundTheory.Heights₂.Heights.PSymplGramMem
namespace GroundTheory.Heights₂.Heights.PSymplGramMem
theorem _root_.solution {l : Type*} [Fintype l] (P : Matrix l l ℤ) (G : Matrix l l ℝ) (x : l) :
    symplGram P G x x = qf G (intVec (P x)) := by
  unfold symplGram qf intVec
  rw [Matrix.mul_mul_apply]
  rfl
end GroundTheory.Heights₂.Heights.PSymplGramMem
