-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_comap_pointIdeal_blockIncl_bac95bce694c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:07:34.504813+00:00
-- url     : https://prove2.me/submissions/f7175944-b5c7-40b6-b524-3076a80c2d64

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagCutProjection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagCutLiesOver

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {R : Type*} [CommRing R] {Φ : Type*} [Field Φ] [Algebra R Φ] {K K' : Type*}
    (j : K ↪ K') {ι' : K' → Type*} (pt : (Σ k', ι' k') → Φ) :
    (pointIdeal R pt).comap (rename (FieldNumbers.blockIncl j ι')) =
      pointIdeal R (fun p => pt (FieldNumbers.blockIncl j ι' p)) := by
  have key : ((pointConeMap R pt).comp (rename (FieldNumbers.blockIncl j ι'))) =
      ((rename j).restrictScalars R).comp (pointConeMap R (fun p => pt (FieldNumbers.blockIncl j ι' p))) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [pointConeMap, FieldNumbers.blockIncl]
  ext f
  simp only [pointIdeal, Ideal.mem_comap, RingHom.mem_ker]
  have hf := congrArg (fun φ => φ f) key
  simp only [AlgHom.comp_apply] at hf
  rw [hf, AlgHom.restrictScalars_apply]
  exact map_eq_zero_iff _ (rename_injective _ j.injective)
end GroundTheory.Heights₂.Heights.NumbersDVR
