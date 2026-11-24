-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermitianExtension_finrank_eq_7a942c89c61a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:34.208307+00:00
-- url     : https://prove2.me/submissions/a13f24a0-0e04-4f49-8235-c003f440f40d

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
open GroundTheory.Heights₂.Heights.HermitianExtension
variable {E' E E'' : HermitianBundle K} (X : HermitianExtension E' E E'')
include X
namespace GroundTheory.Heights₂.Heights.HermitianExtension
theorem _root_.solution : Module.finrank (𝓞 K) E.carrier =
    Module.finrank (𝓞 K) E'.carrier + Module.finrank (𝓞 K) E''.carrier := by
  have h1 := rank_quotient_add_rank_of_isDomain (LinearMap.range X.incl)
  have hker : LinearMap.ker X.proj = LinearMap.range X.incl := X.exact.linearMap_ker_eq
  let e1 : (E.carrier ⧸ LinearMap.range X.incl) ≃ₗ[𝓞 K] E''.carrier :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans
      (X.proj.quotKerEquivOfSurjective X.proj_surjective)
  let e2 : E'.carrier ≃ₗ[𝓞 K] LinearMap.range X.incl :=
    LinearEquiv.ofInjective X.incl X.incl_injective
  rw [← Module.finrank_eq_rank, ← Module.finrank_eq_rank, ← Module.finrank_eq_rank] at h1
  norm_cast at h1
  rw [e1.finrank_eq, ← e2.finrank_eq] at h1
  omega
end GroundTheory.Heights₂.Heights.HermitianExtension
