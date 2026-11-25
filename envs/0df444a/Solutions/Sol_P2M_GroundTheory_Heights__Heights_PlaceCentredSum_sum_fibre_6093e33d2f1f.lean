-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PlaceCentredSum_sum_fibre_6093e33d2f1f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:47:27.494424+00:00
-- url     : https://prove2.me/submissions/efa0e4a6-2d6d-47a1-8b61-94f3fc230edc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightPlaceCentredSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PPlaceCentredSum

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
theorem _root_.solution (Q : HeightOneSpectrum (𝓞 L)) :
    ∑ v : {v : FinitePlace K // below v = Q}, deg L v.1 = Module.finrank L K := by
  rw [← (fibreEquiv Q).symm.sum_comp, IsFractionRing.finrank_eq (𝓞 L) L (𝓞 K) K,
    ← sum_ramification_inertia_eq_finrank Q.asIdeal (𝓞 K)]
  refine Finset.sum_congr rfl fun P _ ↦ ?_
  simp only [deg, fibreEquiv, Equiv.coe_fn_symm_mk, FinitePlace.maximalIdeal_mk]
end GroundTheory.Heights₂.Heights.PlaceCentredSum
