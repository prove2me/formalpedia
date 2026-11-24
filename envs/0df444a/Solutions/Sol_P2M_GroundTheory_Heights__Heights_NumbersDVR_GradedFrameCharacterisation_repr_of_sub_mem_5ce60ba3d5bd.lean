-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_GradedFrameCharacterisation_repr_of_sub_mem_5ce60ba3d5bd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:47.628502+00:00
-- url     : https://prove2.me/submissions/864aa834-9139-4794-9708-a6c0f7ee1880

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
theorem _root_.solution (w : Module.Basis (Fin N) Ω E) {x : E} {i : Fin N} {t : Ω}
    (hx : x - t • w i ∈
      Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < ((Fin.castSucc i : Fin (N + 1)) : ℕ)})) :
    (∀ j, i < j → w.repr x j = 0) ∧ w.repr x i = t := by
  rw [Module.Basis.mem_span_image] at hx
  have key : ∀ j : Fin N, i ≤ j → w.repr x j - t * (Finsupp.single i (1 : Ω) j) = 0 := by
    intro j hj
    have hj' : j ∉ (w.repr (x - t • w i)).support := fun hm => by
      have hlt := hx (Finset.mem_coe.mpr hm)
      simp only [Set.mem_ofPred_eq, Fin.val_castSucc] at hlt
      exact absurd hj (not_le.mpr (Fin.lt_def.mpr hlt))
    rw [Finsupp.notMem_support_iff, map_sub, map_smul, Module.Basis.repr_self, Finsupp.sub_apply,
      Finsupp.smul_apply, smul_eq_mul] at hj'
    exact hj'
  refine ⟨fun j hj => ?_, ?_⟩
  · have h0 := key j hj.le
    rwa [Finsupp.single_eq_of_ne (ne_of_gt hj), mul_zero, sub_zero] at h0
  · have h0 := key i le_rfl
    rwa [Finsupp.single_eq_same, mul_one, sub_eq_zero] at h0
end GroundTheory.Heights₂.Heights.NumbersDVR.GradedFrameCharacterisation
