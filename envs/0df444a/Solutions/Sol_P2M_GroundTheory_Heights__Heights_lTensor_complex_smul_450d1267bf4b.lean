-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_lTensor_complex_smul_450d1267bf4b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:50.991366+00:00
-- url     : https://prove2.me/submissions/f54fdffc-b4cb-4c29-b615-35a039e83e91

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
omit [NumberField K]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (σ : K →+* ℂ) {M N : Type*} [AddCommGroup M] [Module (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N] (f : M →ₗ[𝓞 K] N) (c : ℂ) (x : Fibre σ M) :
    f.lTensor (ComplexAt σ) (c • x) = c • f.lTensor (ComplexAt σ) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul z m => rw [smul_tmul', LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, smul_tmul']
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
end GroundTheory.Heights₂.Heights
