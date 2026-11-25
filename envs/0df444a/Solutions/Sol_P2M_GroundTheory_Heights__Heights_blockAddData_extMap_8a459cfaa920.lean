-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_blockAddData_extMap_8a459cfaa920
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:25:37.946482+00:00
-- url     : https://prove2.me/submissions/41f01d4d-7a9a-4dc4-97c2-edde0a8c178c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples

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
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (n : ι → ℕ) (k₀ : ι)
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution :
    (blockAddData n k₀).extMap = (MvPolynomial.map (ArithVariety.whole n).mkF).comp (blockSubst n k₀) := by
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun v ↦ ?_)
  · simp [AddBlockData.extMap, blockSubst]
  · rw [RingHom.comp_apply, AddBlockData.extMap, blockSubst, eval₂Hom_X', eval₂Hom_X', map_mul, map_C, map_X]
    rcases v with ⟨_ | k, i⟩ <;> rfl
end GroundTheory.Heights₂.Heights
