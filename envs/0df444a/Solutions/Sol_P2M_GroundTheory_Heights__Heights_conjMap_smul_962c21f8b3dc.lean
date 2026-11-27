-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_conjMap_smul_962c21f8b3dc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:11:30.026961+00:00
-- url     : https://prove2.me/submissions/0c658477-2252-4c98-9109-40d46898865f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianLattice
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexAt_conj_smul_60104c53b1e0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct
noncomputable section
open ComplexAt
variable {K : Type*} [Field K]
variable (σ : K →+* ℂ) (E : Type*) [AddCommGroup E] [Module (𝓞 K) E]
variable {σ E}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (c : ℂ) (x : Fibre σ E) :
    conjMap σ E (c • x) = starRingEnd ℂ c • conjMap σ E x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul z e => rw [smul_tmul', conjMap_tmul, conjMap_tmul, smul_tmul', conj_smul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
end GroundTheory.Heights₂.Heights
