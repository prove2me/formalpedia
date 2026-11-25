-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.sphProb_compl_sphere
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:31:06.876205+00:00
-- url     : https://prove2.me/submissions/751ab225-c747-4ebe-b7db-071a2cecb5e9

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomStA
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sphMonom_continuous_sqN
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sphMonom_measurable_normalize
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sphMonom_sqN_normalize


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (D : ℕ) : sphProb (D + 1) {z | sqN z = 1}ᶜ = 0 := by
  unfold sphProb
  rw [Measure.map_apply sphMonom_measurable_normalize
    ((isClosed_eq sphMonom_continuous_sqN continuous_const).measurableSet.compl)]
  apply measure_mono_null (t := {0})
  · intro z hz
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_ofPred_eq] at hz
    rw [Set.mem_singleton_iff]
    by_contra h0
    exact hz (sphMonom_sqN_normalize z h0)
  · unfold gaussC
    exact withDensity_absolutelyContinuous _ _ (measure_singleton 0)
end ReciprocityTheory.GeometryOfNumbersTheory
