-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HeightOfPointAlt_finite_adicAbv_ne_one_e06b12e8b8b6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:40.428208+00:00
-- url     : https://prove2.me/submissions/774464b5-928e-4b55-bfc2-f4d6062cba82

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
theorem _root_.solution {c : K} (hc : c ≠ 0) :
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) |
      NumberField.HeightOneSpectrum.adicAbv K v c ≠ 1}.Finite := by
  have hfin : (Function.mulSupport fun w : FinitePlace K => w c).Finite :=
    FinitePlace.hasFiniteMulSupport hc
  refine (hfin.preimage (FinitePlace.equivHeightOneSpectrum.symm.injective.injOn)).subset ?_
  intro v hv
  simp only [Set.mem_preimage, Function.mem_mulSupport,
    FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding]
  exact hv
end GroundTheory.Heights₂.Heights.HeightOfPointAlt
