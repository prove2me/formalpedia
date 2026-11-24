-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_secIdealOf_eq_map_a897c8efb2fb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:50.208666+00:00
-- url     : https://prove2.me/submissions/e7165158-1fe9-4465-b334-8834a362a2e4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsSecIdealOfPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecMax

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K))
    (W : Ideal (MvPolynomial (Fin n) (𝓞 K))) : secIdealOf e I v W = W.map (toSecB e I v) :=
  Ideal.map_map _ _
end GroundTheory.Heights₂.Heights.Vertical
