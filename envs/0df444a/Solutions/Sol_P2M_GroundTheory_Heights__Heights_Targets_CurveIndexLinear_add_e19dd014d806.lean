-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinear_add_e19dd014d806
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:00:05.538529+00:00
-- url     : https://prove2.me/submissions/3a2b8021-97d2-4f48-b3c5-b912ccf001e6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveIndexLinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveRingFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveClosedPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsInvertibleIndexMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveIndexLinear
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_gen_ne_zero_4ffc22541bb7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_gen_add_fc4f2d1db5eb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_mul_mem_secIdeal_3d741e7bcfab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_chartIndexLog_eq_f54d8e9c1200
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_local_gen_bde832597cf6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_gen_frac_40f19e092313

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open CurveIndexLinearAlt
namespace GroundTheory.Heights₂.Heights.Targets
namespace CurveIndexLinear
theorem _root_.solution (hF : CurveRingFinite.Statement) (hC : CurveClosedPointChart.Statement)
    (hI : InvertibleIndexMul.Statement) {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
    [Field Ω] {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hP : IsArithVar (mCoordIdeal y) 1)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (a a' : K → ℤ) :
    chartIndexLog y c (a + a') 1 = chartIndexLog y c a 1 + chartIndexLog y c a' 1 := by
  classical
  rw [chartIndexLog_eq hc, chartIndexLog_eq hc, chartIndexLog_eq hc]
  obtain ⟨m0, hm0⟩ := Ideal.exists_maximal (curveRing y)
  obtain ⟨c0, hc0, hr0⟩ := hC K ι Ω y hP m0 hm0
  have hfrac : ∀ (b : K → ℤ) (i : {c' : ∀ k, ι k // ∀ k, y ⟨k, c' k⟩ ≠ 0}),
      ∃ d ∈ curveRing y, d ≠ 0 ∧ d * gen y c b i.1 ∈ curveRing y :=
    fun b i => gen_frac hc hc0 hr0 i.1 i.2 b
  obtain ⟨h1, h2, h3⟩ := hI Ω (curveRing y) (secIdeal y c a) (secIdeal y c a') (secIdeal y c (a + a'))
    {c' : ∀ k, ι k // ∀ k, y ⟨k, c' k⟩ ≠ 0} (fun i => gen y c a i.1) (fun i => gen y c a' i.1)
    (hF K ι Ω y hP) (mul_mem_secIdeal hc) (mul_mem_secIdeal hc) (mul_mem_secIdeal hc)
    (fun i => gen_ne_zero hc i.2 a) (fun i => gen_ne_zero hc i.2 a') (hfrac a) (hfrac a') (fun m hm => by
      obtain ⟨c', hc', hr⟩ := hC K ι Ω y hP m hm
      refine ⟨⟨c', hc'⟩, local_gen hc hm.isPrime hc' hr a, local_gen hc hm.isPrime hc' hr a', ?_⟩
      simp only [← gen_add hc hc']
      exact local_gen hc hm.isPrime hc' hr (a + a'))
  rw [h3, Real.log_mul h1.ne' h2.ne']
end CurveIndexLinear
end GroundTheory.Heights₂.Heights.Targets
