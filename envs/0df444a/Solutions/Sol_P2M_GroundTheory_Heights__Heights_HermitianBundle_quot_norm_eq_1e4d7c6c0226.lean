-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermitianBundle_quot_norm_eq_1e4d7c6c0226
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:50.231741+00:00
-- url     : https://prove2.me/submissions/4ae127d2-5ae0-47ef-8a8d-8ef0c873fd75

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsBundles

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
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Heights₂.Heights.HermitianBundle
variable (M : HermitianBundle K) (F : Submodule (𝓞 K) M.carrier) (hF : M.Saturated F)
namespace GroundTheory.Heights₂.Heights.HermitianBundle
theorem _root_.solution (σ : K →+* ℂ) (ξ : Fibre σ (M.carrier ⧸ F)) :
    ‖FibreSpace.equiv (M.quot F hF).metric σ ξ‖ = ‖quotFibreMap M F hF σ ξ‖ := by
  have h1 := norm_sq_eq_re_inner (𝕜 := ℂ) (FibreSpace.equiv (M.quot F hF).metric σ ξ)
  have h2 := norm_sq_eq_re_inner (𝕜 := ℂ) (quotFibreMap M F hF σ ξ)
  have h3 : ‖FibreSpace.equiv (M.quot F hF).metric σ ξ‖ ^ 2 = ‖quotFibreMap M F hF σ ξ‖ ^ 2 := by
    rw [h1, h2]
    rfl
  rw [← Real.sqrt_sq (norm_nonneg (FibreSpace.equiv (M.quot F hF).metric σ ξ)), h3,
    Real.sqrt_sq (norm_nonneg _)]
end GroundTheory.Heights₂.Heights.HermitianBundle
