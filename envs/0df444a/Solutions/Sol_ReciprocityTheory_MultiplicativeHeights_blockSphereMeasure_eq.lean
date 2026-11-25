-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.blockSphereMeasure_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:20:28.782245+00:00
-- url     : https://prove2.me/submissions/119d1c52-e758-4e7a-af20-034093aa16ee

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (B n : ℕ) :
    blockSphereProb B n = ((volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ)⁻¹ ^ B •
      Measure.pi fun _ : Fin B => (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere := by
  unfold blockSphereProb
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul]
  simp only [sphereProb, ProbabilityTheory.cond_apply MeasurableSet.univ, Set.univ_inter,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
end ReciprocityTheory.MultiplicativeHeights
