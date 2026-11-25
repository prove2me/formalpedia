-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MonomialMapNorm_form_div_mem_df5c07c6a0e3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:11:51.604362+00:00
-- url     : https://prove2.me/submissions/dc0a57ff-0cd3-45c9-9fd2-7f65ddf4e2b2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroBis
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_mkF_X_ne_zero_610853a0b298
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_chart_homogeneous_b02eed3f7c1c


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
noncomputable section
open GroundTheory.Heights₂.Heights.MonomialMapNorm
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable (P : ArithVariety n)
namespace GroundTheory.Heights₂.Heights.MonomialMapNorm
theorem _root_.solution {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) {e : MvPolynomial (Coord n) ℤ}
    {δ : ι → ℕ} (he : IsWeightedHomogeneous (coordDeg n) e δ) :
    P.mkF e / P.chartPow c (fun k ↦ (δ k : ℤ)) ∈ P.chartRing c := by
  have h := P.chart_homogeneous c hc he
  have hne : (∏ k, P.mkF (X ⟨k, c k⟩) ^ δ k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (mkF_X_ne_zero P hc k)
  have hp : P.chartPow c (fun k ↦ (δ k : ℤ)) = ∏ k, P.mkF (X ⟨k, c k⟩) ^ δ k := by
    simp only [ArithVariety.chartPow, zpow_natCast]
  rw [hp, ← h, mul_div_cancel_left₀ _ hne]
  exact eval₂_mem (fun i _ ↦ by rw [eq_intCast]; exact intCast_mem _ _)
    fun v ↦ Subring.subset_closure ⟨v, rfl⟩
end GroundTheory.Heights₂.Heights.MonomialMapNorm
