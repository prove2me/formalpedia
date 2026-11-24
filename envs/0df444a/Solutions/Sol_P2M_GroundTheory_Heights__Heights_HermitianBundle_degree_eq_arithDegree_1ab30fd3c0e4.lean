-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermitianBundle_degree_eq_arithDegree_1ab30fd3c0e4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:33.33389+00:00
-- url     : https://prove2.me/submissions/d880b87a-35d7-4188-a8ed-841aec35820c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal

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
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights
namespace HermitianBundle
theorem _root_.solution (E : HermitianBundle K)
    (F : Submodule (𝓞 K) E.carrier) :
    E.degree F = GroundTheory.Heights₂.Heights.arithDegree (E.metric.comap F.subtype F.injective_subtype) := by
  have hf := (HermitianBundle.exists_linearIndependent_rank E F).choose_spec
  set f := (HermitianBundle.exists_linearIndependent_rank E F).choose
  rw [arithDegree_eq _ hf (Fintype.card_fin _)]
  simp only [HermitianBundle.degree, HermitianBundle.degreeWith, degreeWith]
  congr 2
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  congr 1
  have hG : (gram ℂ fun i ↦ fibreVec (E.metric.comap F.subtype F.injective_subtype) σ (f i)) =
      Matrix.of fun i j ↦ (E.metric.form σ).inner
        ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] (f i : E.carrier)) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] (f j : E.carrier)) := by
    ext i j
    rfl
  have hD := (posSemidef_gram ℂ fun i ↦
    fibreVec (E.metric.comap F.subtype F.injective_subtype) σ (f i)).det_nonneg
  rw [hG] at hD
  simp only [GroundTheory.Heights₂.Heights.gramDet, HermitianBundle.gramDet]
  rw [hG]
  have := congrArg Complex.re (Complex.norm_of_nonneg' hD)
  simpa [f] using this
end HermitianBundle
end GroundTheory.Heights₂.Heights
