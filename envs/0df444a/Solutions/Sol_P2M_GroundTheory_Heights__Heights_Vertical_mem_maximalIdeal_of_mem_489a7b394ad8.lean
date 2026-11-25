-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_mem_maximalIdeal_of_mem_489a7b394ad8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:24:40.820806+00:00
-- url     : https://prove2.me/submissions/26227dfa-24e2-41eb-b7aa-3a6967ad7e0c

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
omit [NumberField K]
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution (e : ℕ) (v : HeightOneSpectrum (𝓞 K)) {a : 𝓞 K} (ha : a ∈ v.asIdeal) :
    algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (C a) ∈
      IsLocalRing.maximalIdeal (ParDVR e n v) :=
  (IsLocalization.AtPrime.to_map_mem_maximal_iff (ParDVR e n v) (parPrime e n v) _).mpr (Ideal.mem_map_of_mem _ ha)
end GroundTheory.Heights₂.Heights.Vertical
