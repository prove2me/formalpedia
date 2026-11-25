-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RegularityDenominator_proof_34da1ce71247
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:11:34.501486+00:00
-- url     : https://prove2.me/submissions/a464e8b6-f59b-4bde-ae88-f084e2052730

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LogCardLocIdealUnitMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsBisAlt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularityDenominator_isMultiHomog_C_6474a899c711
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isMultiHomog_C_8aa21e557757
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_coordProd_not_mem_ea4019939c96
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_coordProd_8cb4f1e2e87b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_one_6a94195931fa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_LocRingFrac_proof_cba16ef3484e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularityLocalProduct_proof_9a08042e03d8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_arithVarZero_56f17dda19d2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_frac_mem_locRing_a3c1c87b7867


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
namespace RegularityDenominator
theorem _root_.solution (hD : RegularityDivisorSupportClosed.Statement) (hPow : LocRingPow.Statement) :
    RegularityDenominator.Statement := by
  intro K _ ι _ P x hP
  have hPp : P.IsPrime := hP.2.1.1
  have hFL : (x : FractionRing (MRing ι ⧸ P)) ∈ locRing P P := by
    have hx := x.2
    unfold funField at hx
    unfold locRing
    refine Subring.closure_mono ?_ hx
    rintro _ ⟨u, v, a, hv, hu, hva, rfl⟩
    refine ⟨u, v, a, hv, fun h => ?_, hu, hva, rfl⟩
    have h0 : Ideal.Quotient.mk P v = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h
    exact zero_notMem_nonZeroDivisors (h0 ▸ hv)
  obtain ⟨u, v, a, hu, hva, hvP, hxv⟩ := LocRingFrac.proof K ι P P hPp hPp le_rfl _ hFL

  have key : ∀ W ∈ divSupp P v, ∃ m : ℤ, m ≠ 0 ∧
      (x : FractionRing (MRing ι ⧸ P)) * (m : FractionRing (MRing ι ⧸ P)) ∈ locRing P W := by
    intro W hW
    obtain ⟨hWc, hPW, -⟩ := (hD K ι P v a W hP hva hvP).1 hW
    have hWp : W.IsPrime := hWc.1.1
    have hvert : W.comap (C : ℤ →+* MRing ι) ≠ ⊥ := fun hh =>
      arithVarZero K ι W ⟨hP.1, hWc.1, hh, by rw [zero_add]; exact hWc.2⟩
    obtain ⟨n, hnW, hn0⟩ := (Submodule.ne_bot_iff _).mp hvert
    choose c hc using hW.2
    set t : MRing ι := ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ a k
    have ht : IsMultiHomog t a := AvoidRing.isMultiHomog_coordProd c a
    have htW : t ∉ W := AvoidRing.coordProd_not_mem hWp c hc a
    have ht0 : algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P t) ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact fun h => htW (hPW h)
    have h1W : (1 : MRing ι) ∉ W := fun h => hWp.ne_top ((Ideal.eq_top_iff_one _).mpr h)
    obtain ⟨N, z, hz, hNz⟩ := hPow K ι P v t a W _ (C n) 1 0 (n : FractionRing (MRing ι ⧸ P)) hPp hP.2.1.2.1 hva
      hvP hW ht htW (div_mul_cancel₀ _ ht0) (RegularityDenominator.isMultiHomog_C n) AvoidRing.isMultiHomog_one hnW h1W
      (by rw [map_one, map_one, mul_one, eq_intCast C n, map_intCast, map_intCast])
    refine ⟨n ^ N, pow_ne_zero _ hn0, ?_⟩
    have hut : algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) /
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P t) ∈ locRing P W :=
      frac_mem_locRing hPW hu ht htW (div_mul_cancel₀ _ ht0)
    rw [Int.cast_pow, hNz, ← mul_assoc, mul_div_assoc', hxv]
    exact mul_mem hut hz
  classical
  have hfin := divSupp_finite P v
  let mW : Ideal (MRing ι) → ℤ := fun W => if h : W ∈ divSupp P v then (key W h).choose else 1
  let M : ℤ := ∏ W ∈ hfin.toFinset, mW W
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.mpr fun W hW => by
    have hW' := hfin.mem_toFinset.mp hW
    simp only [mW, dif_pos hW']
    exact (key W hW').choose_spec.1
  refine ⟨(M : funField P), fun h => hM0 ?_, fun W hWc hPW => ⟨?_, ?_⟩⟩
  · have h' : ((M : funField P) : FractionRing (MRing ι ⧸ P)) = 0 := by rw [h]; rfl
    have h2 : algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (C M)) = 0 := by
      rw [eq_intCast C M, map_intCast, map_intCast]
      simp at h'
      exact h'
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h2
    have h3 : M ∈ P.comap (C : ℤ →+* MRing ι) := h2
    rw [hP.2.2.1] at h3
    exact Ideal.mem_bot.mp h3
  · have hc : ((M : funField P) : FractionRing (MRing ι ⧸ P)) = (M : FractionRing (MRing ι ⧸ P)) := by simp
    rw [hc]
    exact intCast_mem (locRing P W) M
  · have hc : ((x * (M : funField P) : funField P) : FractionRing (MRing ι ⧸ P)) =
        (x : FractionRing (MRing ι ⧸ P)) * (M : FractionRing (MRing ι ⧸ P)) := by simp
    rw [hc]
    by_cases hvW : v ∈ W
    · have hW : W ∈ divSupp P v := (hD K ι P v a W hP hva hvP).2 ⟨hWc, hPW, hvW⟩
      obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem mW (hfin.mem_toFinset.mpr hW)
      have hm := (key W hW).choose_spec.2
      rw [show M = mW W * r from hr, Int.cast_mul, ← mul_assoc]
      simp only [mW, dif_pos hW]
      exact mul_mem hm (intCast_mem _ r)
    · exact mul_mem (frac_mem_locRing hPW hu hva hvW hxv) (intCast_mem _ M)
end RegularityDenominator
end GroundTheory.Heights₂.Heights.Inter
