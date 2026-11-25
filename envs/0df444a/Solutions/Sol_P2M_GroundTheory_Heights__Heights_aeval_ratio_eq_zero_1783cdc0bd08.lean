-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_aeval_ratio_eq_zero_1783cdc0bd08
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:04:52.715687+00:00
-- url     : https://prove2.me/submissions/e0174548-ed90-4d68-b78c-9223a115a816

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitDegreeRatio
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegreeRatioLemmas
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_aeval_chartHomogQ_field_7f5667ad45c9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_coneMapQ_chartHomogQ_93cff86ca181
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitCurve_ker_coneMapQ_0aa641207f8f


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
variable {ι : Type} {n : ι → ℕ}
variable [Fintype ι]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, x k (c k) ≠ 0) {z : Coord n → ℂ} (hz : z ∈ Geo.mcPts (ι := blockIdx n) (orbitIdeal x))
    (hz0 : ∀ k, z ⟨k, c k⟩ ≠ 0) (f : MvPolynomial (Coord n) ℚ)
    (hf : aeval (fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)) f = 0) :
    aeval (fun p ↦ z p / z ⟨p.1, c p.1⟩) f = 0 := by
  have hx : aeval (flatCone x) (chartHomogQ c f) = 0 := by
    rw [aeval_chartHomogQ_field c f (flatCone x) hc]
    exact mul_eq_zero_of_right _ hf
  have hker : chartHomogQ c f ∈ RingHom.ker (OrbitCurve.coneMapQ x) := by
    rw [RingHom.mem_ker, coneMapQ_chartHomogQ, hx, map_zero, zero_mul]
  classical
  rw [OrbitCurve.ker_coneMapQ] at hker
  have hle : ReciprocityTheory.AnForm.R.extQ (orbitIdeal x) ≤
      RingHom.ker (aeval z : MvPolynomial (Coord n) ℚ →ₐ[ℚ] ℂ) := by
    refine Ideal.map_le_iff_le_comap.mpr fun g hg ↦ ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, ← algebraMap_int_eq, aeval_map_algebraMap, aeval_def,
      algebraMap_int_eq, ← eval_map]
    exact hz.2 g hg
  have h := hle hker
  rw [RingHom.mem_ker, aeval_chartHomogQ_field c f z hz0] at h
  exact (mul_eq_zero.mp h).resolve_left
    (Finset.prod_ne_zero_iff.mpr fun p _ ↦ pow_ne_zero _ (hz0 p.1))
end GroundTheory.Heights₂.Heights
