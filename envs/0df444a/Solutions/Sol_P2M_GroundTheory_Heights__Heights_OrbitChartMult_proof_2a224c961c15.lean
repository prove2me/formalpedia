-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitChartMult_proof_2a224c961c15
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:14:31.007799+00:00
-- url     : https://prove2.me/submissions/b7e4f482-f6a5-44be-89e6-164514b98bd2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMultLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMult
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_multAt_eq_localQuotLength_of_083cc3b8006e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartCone_eq_zero_iff_f230138033b2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartCone_of_isWeightedHomogeneous_c74b1368637f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartEval_X_chart_5274b6332030
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_mem_of_chartEval_mem_chartPoint_99b4780cbeae
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_weightedHomogeneousComponent_mem_of_isMultiHomogIdeal_91ec1ac4e335
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitCurve_isMultiHomogIdeal_orbitIdeal_5ad0b5ef0050
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isMultiHomogIdeal_of_mem_minimalPrimes


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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G IsLocalRing
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace OrbitChartMult
theorem _root_.solution : OrbitChartMult.Statement := by
  intro ι _ _ _ n A x s _hx hs V hV c hXV hm
  classical
  have hVmin : V ∈ (orbitIdeal x ⊔ Ideal.span {s}).minimalPrimes := hV.1
  have hVp : V.IsPrime := hVmin.1.1
  have hWV : orbitIdeal x ≤ V := le_sup_left.trans hVmin.1.2
  obtain ⟨a, -, hsa, -⟩ := hs
  have hVh : Geo.IsMultiHomogIdeal (ι := blockIdx n) V :=
    Geo.isMultiHomogIdeal_of_mem_minimalPrimes (OrbitCurve.isMultiHomogIdeal_orbitIdeal x) hsa hVmin
  have hc : ∀ k, x k (c k) ≠ 0 := fun k h ↦ hXV k (hWV (by
    rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_X]
    simp [flatCone, h]))
  have hcomp : ∀ v ∈ V, ∀ e, weightedHomogeneousComponent (coordDeg n) e v ∈ V :=
    fun v hv e ↦ weightedHomogeneousComponent_mem_of_isMultiHomogIdeal hVh hv e
  have : (Ideal.map (chartEval x c) V).IsPrime := hm
  exact multAt_eq_localQuotLength_of (chartEval x c) (chartCone x c (chartRing x c))
    (fun hF ↦ by rw [chartCone_of_isWeightedHomogeneous x c _ hF, Algebra.algebraMap_self_apply])
    V (chartEval_surjective x c) (orbitIdeal x) (chartCone_eq_zero_iff x c hc) hcomp
    (fun hF hm' ↦ mem_of_chartEval_mem_chartPoint x c hc hWV hcomp hXV hF hm') c
    (chartEval_X_chart x c hc) hXV ((geoMultiHomog_iff s a).mp hsa)
end OrbitChartMult
end GroundTheory.Heights₂.Heights
