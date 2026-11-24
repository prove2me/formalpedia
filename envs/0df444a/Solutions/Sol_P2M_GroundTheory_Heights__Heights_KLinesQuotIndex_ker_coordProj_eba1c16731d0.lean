-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesQuotIndex_ker_coordProj_eba1c16731d0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:30.421339+00:00
-- url     : https://prove2.me/submissions/6e51cb90-e74c-4cf9-b7e7-0ee0a4c44c5c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesQuotIndex

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
open GroundTheory.Heights₂.Heights.KLinesQuotIndex
namespace GroundTheory.Heights₂.Heights.KLinesQuotIndex
theorem _root_.solution {K : Type*} [Field K] {n m k : ℕ}
    (B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K)) :
    LinearMap.ker (coordProj B) = Submodule.span K (Set.range fun i => B (Sum.inl i)) := by
  ext v
  have hr : (Set.range fun i => B (Sum.inl i)) = B '' Set.range Sum.inl := by
    rw [← Set.range_comp]; rfl
  rw [hr, Module.Basis.mem_span_image, LinearMap.mem_ker]
  constructor
  · intro h x hx
    rcases x with i | j
    · exact ⟨i, rfl⟩
    · exact absurd (congr_fun h j) (by simpa [coordProj] using hx)
  · intro h
    funext j
    have : Sum.inr j ∉ (B.repr v).support := fun hj => by
      obtain ⟨i, hi⟩ := h hj
      exact Sum.inl_ne_inr hi
    simpa [coordProj] using this
end GroundTheory.Heights₂.Heights.KLinesQuotIndex
