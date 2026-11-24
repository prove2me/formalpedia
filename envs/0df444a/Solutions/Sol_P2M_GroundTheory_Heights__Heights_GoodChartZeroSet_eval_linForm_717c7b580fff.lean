-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GoodChartZeroSet_eval_linForm_717c7b580fff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:07:11.547407+00:00
-- url     : https://prove2.me/submissions/69bedf3b-efca-4645-b5a4-902ef4b16b05

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartZeroSet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartZeroSet
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalSmulOfIsHomogeneousAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PGoodChartZeroSet
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_scaleBlock_mem_zeroLocus


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Finset
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre scaleBlock scaleBlock_mem_zeroLocus)
open ComplexSets
open GroundTheory.Heights₂.Heights.GoodChartZeroSet
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.GoodChartZeroSet
theorem _root_.solution {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : Fin m → ℂ) :
    eval x (linForm σ Ψ) = Ψ (fun i' => x (σ.symm i')) 0 := by
  classical
  rw [linForm]
  have hv : (fun i' => x (σ.symm i')) = ∑ a, x a • fun i' => if σ a = i' then (1 : ℂ) else 0 := by
    rw [pi_eq_sum_univ (fun i' => x (σ.symm i'))]
    exact (Equiv.sum_comp σ _).symm.trans (by simp)
  rw [hv]
  simp only [map_sum, Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, map_mul, eval_C, eval_X]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm]
end GroundTheory.Heights₂.Heights.GoodChartZeroSet
