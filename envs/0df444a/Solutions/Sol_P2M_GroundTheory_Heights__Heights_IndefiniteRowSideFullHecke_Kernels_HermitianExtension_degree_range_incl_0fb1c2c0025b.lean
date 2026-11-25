-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_HermitianExtension_degree_range_incl_0fb1c2c0025b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:46:31.635832+00:00
-- url     : https://prove2.me/submissions/b83f86ba-82bc-419c-81d9-b95532b0757e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StdCoordMapInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_DegreeTopEqArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PLocalChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DegreeRangeIncl
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianBundle_degree_eq_arithDegree_1ab30fd3c0e4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_arithDegree_congr_5fb6b845d5f9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_fibreMap_tmul_6f6be11e0e36


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
open NumberField TensorProduct GroundTheory.Heights₂.Heights
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
namespace HermitianExtension
theorem _root_.solution {K : Type} [Field K] [NumberField K]
    {E' E E'' : HermitianBundle.{0} K} (Y : HermitianExtension E' E E'') :
    E.degree (LinearMap.range Y.incl) = E'.arithDegree := by
  rw [HermitianBundle.degree_eq_arithDegree]
  symm
  refine LatticeLemmas.arithDegree_congr _ _ (LinearEquiv.ofInjective Y.incl Y.incl_injective)
    fun σ x y ↦ ?_
  rw [HermitianMetric.comap_inner, fibreMap_tmul, fibreMap_tmul]
  have h := Y.incl_isometric σ ((1 : ComplexAt σ) ⊗ₜ x) ((1 : ComplexAt σ) ⊗ₜ y)
  simp only [LinearMap.lTensor_tmul] at h
  exact h.symm
end HermitianExtension
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
