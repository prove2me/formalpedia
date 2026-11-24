-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_ringKrullDim_mvPolynomial_complex_a419de08b2fb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:23.359257+00:00
-- url     : https://prove2.me/submissions/934fab90-1be1-4251-bd3d-9c3fc7f8a83b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjHomInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjHomInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.ComplexSets
theorem _root_.solution (d : ℕ) :
    ringKrullDim (MvPolynomial (Fin d) ℂ) = d := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp
end GroundTheory.Heights₂.Heights.ComplexSets
