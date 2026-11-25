-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_star_dotProduct_mulVec_of_isHermitian_f0205efbd7ec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:12:11.813796+00:00
-- url     : https://prove2.me/submissions/623f3f23-7013-4a8f-8d25-b418e4c8de3e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PEigenReflectionMaps

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
open scoped ComplexOrder
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution {P : Matrix ι ι ℂ} (hP : P.IsHermitian)
    (x y : ι → ℂ) : star (star y ⬝ᵥ (P *ᵥ x)) = star x ⬝ᵥ (P *ᵥ y) := by
  have h1 : star y ⬝ᵥ (P *ᵥ x) = star (P *ᵥ y) ⬝ᵥ x := by
    rw [dotProduct_mulVec, star_mulVec, hP.eq]
  rw [h1, star_dotProduct, star_star]
end GroundTheory.Heights₂.Heights.FiniteCovolume
