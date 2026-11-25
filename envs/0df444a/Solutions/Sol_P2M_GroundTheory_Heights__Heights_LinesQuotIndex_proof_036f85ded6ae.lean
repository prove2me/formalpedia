-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LinesQuotIndex_proof_036f85ded6ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:37:48.168039+00:00
-- url     : https://prove2.me/submissions/9e42d109-a282-4b3a-8915-3c7fcf1494e5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesQuotIndex
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesQuotIndex_genIndex_comap_of_surjective_02ea8afefbb6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesQuotIndex_coordProj_surjective_59e6542cb5fd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesQuotIndex_ker_coordProj_eba1c16731d0

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
open NumberField
open KLinesQuotIndex
namespace GroundTheory.Heights₂.Heights
namespace LinesQuotIndex
theorem _root_.solution : LinesQuotIndex.Statement := by
  intro K _ n m k B L c
  set π' := (coordProj B).restrictScalars (𝓞 K) with hπ'
  set W := (Submodule.span K (Set.range fun i => B (Sum.inl i))).restrictScalars (𝓞 K) with hW
  have hker : LinearMap.ker π' = W := by
    rw [hπ', LinearMap.ker_restrictScalars, ker_coordProj]
  have hsurj : Function.Surjective π'.toAddMonoidHom := coordProj_surjective B
  have hcomap : ∀ N : Submodule (𝓞 K) (Fin n → K),
      (N ⊔ W).toAddSubgroup = (N.map π').toAddSubgroup.comap π'.toAddMonoidHom := by
    intro N
    rw [← hker, ← Submodule.comap_map_eq]
    rfl
  have hspan : (Submodule.span (𝓞 K) (Set.range c)).map π' =
      Submodule.span (𝓞 K) (Set.range (coordProj B ∘ c)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [hcomap, hcomap, genIndex_comap_of_surjective _ hsurj, hspan]
end LinesQuotIndex
end GroundTheory.Heights₂.Heights
