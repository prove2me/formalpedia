-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_gramDet_comap_641348eb9df1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:30.588161+00:00
-- url     : https://prove2.me/submissions/acaa5f43-1378-4de9-b9bc-02118721ef7c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_LinearIndependentSumElimOfExact

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
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
open scoped ComplexOrder
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {E M : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
    [Module.Projective (𝓞 K) E] [AddCommGroup M] [Module (𝓞 K) M] [Module.Finite (𝓞 K) M]
    [Module.Projective (𝓞 K) M] (h : HermitianMetric K E) (f : M →ₗ[𝓞 K] E)
    (hf : Function.Injective f) (σ : K →+* ℂ) {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι → M) :
    gramDet (h.comap f hf) σ s = gramDet h σ (fun i ↦ f (s i)) := by
  simp only [gramDet]
  congr 3
end GroundTheory.Heights₂.Heights
