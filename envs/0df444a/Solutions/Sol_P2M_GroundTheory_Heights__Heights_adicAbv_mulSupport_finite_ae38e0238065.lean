-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_adicAbv_mulSupport_finite_ae38e0238065
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:25:54.394801+00:00
-- url     : https://prove2.me/submissions/6be7d5c8-513b-45d5-b546-946f200ee854

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite

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
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {x : K} (hx : x ≠ 0) :
    (Function.mulSupport fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      NumberField.HeightOneSpectrum.adicAbv K v x).Finite := by
  have h := FinitePlace.hasFiniteMulSupport hx
  have e : (Function.mulSupport fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      NumberField.HeightOneSpectrum.adicAbv K v x) =
      FinitePlace.equivHeightOneSpectrum.symm ⁻¹'
        (Function.mulSupport fun w : FinitePlace K => w x) := by
    ext v
    simp only [Function.mem_mulSupport, Set.mem_preimage,
      FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding]
  rw [e]
  exact Set.Finite.preimage (FinitePlace.equivHeightOneSpectrum.symm.injective.injOn) h
end GroundTheory.Heights₂.Heights
