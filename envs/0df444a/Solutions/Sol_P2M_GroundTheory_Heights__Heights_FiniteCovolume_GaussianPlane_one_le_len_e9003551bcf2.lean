-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_one_le_len_e9003551bcf2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:49:24.807632+00:00
-- url     : https://prove2.me/submissions/590a268e-929d-4c03-9fdb-51d7f9be9dee

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianDisc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Examples
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_one_le_norm_embedding_a7bf02bfbb23
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_mem_LaG_ed2258b343aa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_len_MG_aa64f7e65299
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_invApply_one_389908aaaa8a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_vecAt_apply_44afb2b4bdbb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Heights₂.Heights.FiniteCovolume.GaussianPlane
open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped Pointwise ComplexOrder ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.GaussianPlane
theorem _root_.solution {x : Fin 2 → Eg} (hx : x ∈ LaG) (hx0 : x ≠ 0) :
    1 ≤ MG.len (invApply (1 : archUnitary hG vG) (vecAt vG x)) := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace Eg) := inferInstance
  rw [invApply_one, len_MG _ w, vecAt_apply, vecAt_apply]
  rw [Real.one_le_sqrt]
  have key : ∀ i, x i ≠ 0 → 1 ≤ ‖w.embedding (x i)‖ ^ 2 := by
    intro i hi
    have h1 := one_le_norm_embedding w (a := ⟨x i, mem_LaG.1 hx i⟩)
      (fun h => hi (congrArg (fun a : 𝓞 Eg => (a : Eg)) h))
    change 1 ≤ ‖w.embedding (x i)‖ at h1
    nlinarith
  by_cases h0 : x 0 = 0
  · have h1 : x 1 ≠ 0 := by
      intro h1
      apply hx0
      funext i
      fin_cases i
      · exact h0
      · exact h1
    have := key 1 h1
    linarith [sq_nonneg ‖w.embedding (x 0)‖]
  · have := key 0 h0
    linarith [sq_nonneg ‖w.embedding (x 1)‖]
end GroundTheory.Heights₂.Heights.FiniteCovolume.GaussianPlane
