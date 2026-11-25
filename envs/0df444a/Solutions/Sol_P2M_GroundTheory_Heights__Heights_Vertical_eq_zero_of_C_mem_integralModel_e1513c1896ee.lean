-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_eq_zero_of_C_mem_integralModel_e1513c1896ee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:24:22.617828+00:00
-- url     : https://prove2.me/submissions/ec3f5229-0a42-47d1-b391-601f20720387

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PVertSpec

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
variable {K : Type*} [Field K] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution {I : Ideal (MvPolynomial (Fin n) K)} (hI : I.IsPrime)
    {c : 𝓞 K} (hc : C c ∈ integralModel I) : c = 0 := by
  by_contra h
  apply hI.ne_top
  simp only [integralModel, Ideal.mem_comap, map_C] at hc
  have hu : IsUnit (C (algebraMap (𝓞 K) K c) : MvPolynomial (Fin n) K) :=
    (isUnit_iff_ne_zero.mpr
      ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).mpr h)).map C
  exact Ideal.eq_top_of_isUnit_mem _ hc hu
end GroundTheory.Heights₂.Heights.Vertical
