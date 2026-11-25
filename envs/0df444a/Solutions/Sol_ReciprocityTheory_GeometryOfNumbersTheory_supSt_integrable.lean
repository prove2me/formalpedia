-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.supSt_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:54:14.036601+00:00
-- url     : https://prove2.me/submissions/e057d192-db70-4ac9-b685-b867cbdf5e66

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDefs
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_SupStMonoNormSqPos
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_supSt_norm_mono_le
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sphMonom_continuous_f
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sphProb_compl_sphere


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
theorem _root_.solution {D : ℕ} (a b : Fin (D + 1) → ℕ) :
    Integrable (fun z => starRingEnd ℂ (monoC a z) * monoC b z) (sphProb (D + 1)) := by
  have hae : ∀ᵐ z ∂(sphProb (D + 1)), sqN z = 1 := mem_ae_iff.mpr (sphProb_compl_sphere D)
  refine Integrable.of_bound (sphMonom_continuous_f a b).aestronglyMeasurable 1 ?_
  filter_upwards [hae] with z hz
  rw [norm_mul, RCLike.norm_conj]
  have h1 := supSt_norm_mono_le a z hz
  have h2 := supSt_norm_mono_le b z hz
  nlinarith [norm_nonneg (monoC a z), norm_nonneg (monoC b z)]
end ReciprocityTheory.GeometryOfNumbersTheory
