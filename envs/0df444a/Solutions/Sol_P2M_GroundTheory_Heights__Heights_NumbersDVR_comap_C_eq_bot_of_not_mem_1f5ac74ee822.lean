-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_comap_C_eq_bot_of_not_mem_1f5ac74ee822
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:35.337156+00:00
-- url     : https://prove2.me/submissions/7fe9bd43-9f74-4a6d-b401-732fd0997bd6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeOfAddOneLeSucc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemMinimalPrimesOfDivCycleNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {K : Type*} {ι : K → Type*} {O : Type*} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ)
    (H : Ideal (MRing ι O)) [hH : H.IsPrime] (hϖH : (C ϖ : MRing ι O) ∉ H) :
    H.comap (C : O →+* MRing ι O) = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun a ha => ?_
  by_contra ha0
  obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  rw [Ideal.mem_comap, map_mul, map_pow] at ha
  rcases hH.mem_or_mem ha with hv | hp
  · exact hH.ne_top (Ideal.eq_top_of_isUnit_mem _ hv ((Units.isUnit v).map C))
  · exact hϖH (hH.mem_of_pow_mem n hp)
end GroundTheory.Heights₂.Heights.NumbersDVR
