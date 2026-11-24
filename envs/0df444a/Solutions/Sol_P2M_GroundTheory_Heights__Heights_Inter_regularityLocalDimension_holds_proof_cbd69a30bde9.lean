-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_regularityLocalDimension_holds_proof_cbd69a30bde9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:09.165527+00:00
-- url     : https://prove2.me/submissions/6ea36174-4dc5-44ad-8b4a-bdcaf2ee26f6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerExtra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingNoeth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsBisBis
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_coordProd_not_mem_ea4019939c96
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_coordProd_8cb4f1e2e87b


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
namespace regularityLocalDimension_holds
theorem _root_.solution (hF : LocRingFrac.Statement) (hL : LocRingLocal.Statement) (hN : LocRingNoeth.Statement)
    (hPw : LocRingPow.Statement) : regularityLocalDimension_holds.Statement := by
  intro K _ ι _ P s a W hP hs hsP hW
  have hPp : P.IsPrime := hP.2.1.1
  have := hPp
  have hWp : W.IsPrime := hW.1.1.1
  have hPW : P ≤ W := le_sup_left.trans hW.1.1.2
  have hsW : s ∈ W := hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  obtain ⟨hloc, hunit⟩ := hL K ι P W hPp hWp hPW
  have hnoeth := hN K ι P W hPp hWp hPW hW.2
  have := hloc
  have := hnoeth
  refine ⟨hloc, hnoeth, ?_⟩
  choose c hc using hW.2
  have ht : IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ a k) a := AvoidRing.isMultiHomog_coordProd c a
  have htW : (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ a k) ∉ W := AvoidRing.coordProd_not_mem hWp c hc a
  have htP : Ideal.Quotient.mk P (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ a k) ∈ nonZeroDivisors (MRing ι ⧸ P) :=
    mem_nonZeroDivisors_of_ne_zero fun h => htW (hPW (Ideal.Quotient.eq_zero_iff_mem.mp h))
  set xF := IsLocalization.mk' (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) ⟨_, htP⟩ with hxF
  have hxmem : xF ∈ locRing P W := Subring.subset_closure ⟨s, _, a, htP, htW, hs, ht, rfl⟩
  have hxt : xF * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P))
      (Ideal.Quotient.mk P (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ a k)) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) :=
    IsLocalization.mk'_spec _ _ _
  set x : locRing P W := ⟨xF, hxmem⟩
  have hx0 : x ≠ 0 := by
    intro h
    have h' : xF = 0 := congrArg Subtype.val h
    rw [h', zero_mul, eq_comm, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at hxt
    exact hsP hxt
  have hxu : ¬ IsUnit x := fun h => (hunit x s _ a hs ht htW hxt).mp h hsW
  have hmin : IsLocalRing.maximalIdeal (locRing P W) ∈ (Ideal.span {x}).minimalPrimes := by
    refine ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem _).mpr hxu⟩, fun q hq _ y hy => ?_⟩
    obtain ⟨u, v, b, hu, hv, hvW, hyuv⟩ := hF K ι P W hPp hWp hPW y y.2
    have huW : u ∈ W := by
      by_contra h
      exact hy ((hunit y u v b hu hv hvW hyuv).mpr h)
    obtain ⟨n, z, hz, hyz⟩ :=
      hPw K ι P s _ a W xF u v b y hPp hP.2.1.2.1 hs hsP hW ht htW hxt hu hv huW hvW hyuv
    have e : y ^ n = x * ⟨z, hz⟩ := Subtype.ext (by simpa using hyz)
    have hq1 := hq.1
    exact hq1.mem_of_pow_mem n (e ▸ q.mul_mem_right _ (hq.2 (Ideal.mem_span_singleton_self x)))
  have h1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin
  have h2 := Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hx0) hxu
  have h3 := Ideal.height_mono hmin.1.2
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, le_antisymm h1 (h2 ▸ h3)]
  rfl
end regularityLocalDimension_holds
end GroundTheory.Heights₂.Heights.Inter
