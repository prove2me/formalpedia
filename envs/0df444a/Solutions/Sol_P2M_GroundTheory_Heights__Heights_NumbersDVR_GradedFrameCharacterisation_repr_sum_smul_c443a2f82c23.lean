-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_GradedFrameCharacterisation_repr_sum_smul_c443a2f82c23
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:47.525892+00:00
-- url     : https://prove2.me/submissions/01156fc8-bc98-48db-ad84-ac82d83e5e59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueSat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinGradedFrameIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
universe u v w
open GroundTheory.Heights₂.Heights.NumbersDVR.GradedFrameCharacterisation
variable {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.NumbersDVR.GradedFrameCharacterisation
theorem _root_.solution {τ : Type*} [Fintype τ] (w : Module.Basis (Fin N) Ω E) (a : τ → Ω) (bb : τ → E)
    (j : Fin N) :
    w.repr (∑ q, a q • bb q) j = ∑ q, a q * w.repr (bb q) j := by
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul]
end GroundTheory.Heights₂.Heights.NumbersDVR.GradedFrameCharacterisation
