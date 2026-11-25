-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PlaceCentredSum_apply_algebraMap_fc47d50d1873
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:56:46.895028+00:00
-- url     : https://prove2.me/submissions/eb39f4d9-3fa3-4bbf-9630-b7e840bfac4f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightPlaceCentredSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PPlaceCentredSum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PlaceCentredSum_toNNReal_pow_078164fd0600

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
open NumberField IsDedekindDomain Ideal
open GroundTheory.Heights₂.Heights.PlaceCentredSum
variable {L K : Type} [Field L] [NumberField L] [Field K] [NumberField K] [Algebra L K]
namespace GroundTheory.Heights₂.Heights.PlaceCentredSum
theorem _root_.solution (v : FinitePlace K) (x : L) :
    v (algebraMap L K x) = FinitePlace.mk (below v) x ^ deg L v := by
  have hQ : (below (L := L) v).asIdeal ≠ ⊥ := (below v).ne_bot
  have hf : (below (L := L) v).asIdeal.inertiaDeg' v.maximalIdeal.asIdeal ≠ 0 :=
    (inertiaDeg'_pos' _ _).ne'
  have hN := absNorm_eq_pow_inertiaDeg'_of_liesOver v.maximalIdeal.asIdeal (below (L := L) v).asIdeal
    inferInstance hQ
  rw [← FinitePlace.norm_embedding_eq v, FinitePlace.mk_apply, FinitePlace.norm_embedding',
    FinitePlace.norm_embedding', ← HeightOneSpectrum.valuation_liesOver K (below (L := L) v) v.maximalIdeal, map_pow,
    toNNReal_pow _ (NumberField.HeightOneSpectrum.absNorm_ne_zero (below (L := L) v)) hf (by rw [hN]; push_cast; rfl), deg,
    ramificationIdx'_eq_ramificationIdx _ _ hQ, inertiaDeg'_eq_inertiaDeg, ← pow_mul]
  push_cast
  rw [mul_comm]
end GroundTheory.Heights₂.Heights.PlaceCentredSum
