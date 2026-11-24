-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMetric_norm_sq_evalCone_scale_efe510351eca
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:58.065986+00:00
-- url     : https://prove2.me/submissions/f4b95bba-8ede-4a99-b178-4cbe08897662

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_NormSqEvalConeScale
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval__scale_of_isWeightedHomogeneous_6a2760d9d5f2


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
open MvPolynomial
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.ChartMetric
namespace GroundTheory.Heights₂.Heights.ChartMetric
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} (t : ι → ℂ) (z : Cone n ℂ)
    {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ} (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    ‖evalCone (fun k i ↦ t k * z k i) f‖ ^ 2 = (∏ k, ‖t k‖ ^ (2 * (δ k : ℤ))) * ‖evalCone z f‖ ^ 2 := by
  have h : evalCone (fun k i ↦ t k * z k i) f = (∏ k, t k ^ δ k) * evalCone z f :=
    eval₂_scale_of_isWeightedHomogeneous t (fun v ↦ z v.1 v.2) hf
  rw [h, norm_mul, mul_pow, norm_prod, ← Finset.prod_pow]
  congr 1
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [norm_pow, ← pow_mul, ← zpow_natCast]
  congr 1
  push_cast
  ring
end GroundTheory.Heights₂.Heights.ChartMetric
