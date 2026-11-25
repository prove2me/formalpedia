-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HeightOfPointAlt_adicAbv_sum_le_30e128122f54
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:35.401091+00:00
-- url     : https://prove2.me/submissions/e10923ec-2bf7-42ad-b6f8-08bc6e27dc38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHeightOfPoint

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
open MvPolynomial NumberField ComplexAt TensorProduct
noncomputable section
open GroundTheory.Heights₂.Heights.HeightOfPointAlt
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights.HeightOfPointAlt
theorem _root_.solution (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*} (s : Finset ι)
    (f : ι → K) {r : ℝ} (hr : 0 ≤ r)
    (hf : ∀ i ∈ s, NumberField.HeightOneSpectrum.adicAbv K v (f i) ≤ r) :
    NumberField.HeightOneSpectrum.adicAbv K v (∑ i ∈ s, f i) ≤ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hr
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v _ _).trans
      (max_le (hf a (Finset.mem_insert_self a s))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)))
end GroundTheory.Heights₂.Heights.HeightOfPointAlt
