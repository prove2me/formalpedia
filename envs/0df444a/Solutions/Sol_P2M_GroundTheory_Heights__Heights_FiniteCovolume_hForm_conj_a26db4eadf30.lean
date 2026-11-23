-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_conj_a26db4eadf30
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:05.56913+00:00
-- url     : https://prove2.me/submissions/44da079f-4b00-4045-86d5-0068ff5355f9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open Matrix
noncomputable section
variable {ι : Type*} [Fintype ι]
variable (H : Matrix ι ι ℂ)
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (u z : ι → ℂ) :
    starRingEnd ℂ (hForm H u z) = hForm H z u := by
  simp only [hForm]
  conv_rhs => rw [star_dotProduct, star_mulVec, hH.eq, ← dotProduct_mulVec]
  rfl
end GroundTheory.Heights₂.Heights.FiniteCovolume
