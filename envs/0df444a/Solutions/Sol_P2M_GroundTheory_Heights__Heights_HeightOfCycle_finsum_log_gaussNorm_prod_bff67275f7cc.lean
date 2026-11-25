-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HeightOfCycle_finsum_log_gaussNorm_prod_bff67275f7cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:19:18.787806+00:00
-- url     : https://prove2.me/submissions/7bdfcb76-8082-4d25-a8e7-618462fbe00d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsFibreMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHeightOfCycle
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_finsum_log_gaussNorm_mul_2d474f4b01c5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNorm_C_3de71e041495


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
open MvPolynomial NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.HeightOfCycle
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights.HeightOfCycle
theorem _root_.solution {ι α : Type*} (s : Finset α) (L : α → MvPolynomial ι K)
    (hL : ∀ q, L q ≠ 0) :
    ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v (∏ q ∈ s, L q)) =
      ∑ q ∈ s, ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v (L q)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    rw [← C_1]
    simp_rw [gaussNorm_C, map_one, Real.log_one, finsum_zero]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, finsum_log_gaussNorm_mul (hL a)
      (Finset.prod_ne_zero_iff.mpr fun q _ ↦ hL q), ih, Finset.sum_insert ha]
end GroundTheory.Heights₂.Heights.HeightOfCycle
