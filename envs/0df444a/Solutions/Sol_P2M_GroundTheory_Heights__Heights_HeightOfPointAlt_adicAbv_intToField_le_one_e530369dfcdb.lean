-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HeightOfPointAlt_adicAbv_intToField_le_one_e530369dfcdb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:55:55.86083+00:00
-- url     : https://prove2.me/submissions/7f7d55f5-b7e0-4549-8421-b231f7c38b19

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
variable {F : Type*} [Field F] [NumberField F] [Algebra F K]
omit [NumberField F]
namespace GroundTheory.Heights₂.Heights.HeightOfPointAlt
theorem _root_.solution (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (a : 𝓞 F) :
    NumberField.HeightOneSpectrum.adicAbv K v (intToField F K a) ≤ 1 := by
  let b : 𝓞 K := ⟨algebraMap F K (a : F), (RingOfIntegers.isIntegral_coe a).algebraMap⟩
  have hb : intToField F K a = algebraMap (𝓞 K) K b := rfl
  rw [hb]
  exact v.adicAbv_coe_le_one (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) b
end GroundTheory.Heights₂.Heights.HeightOfPointAlt
