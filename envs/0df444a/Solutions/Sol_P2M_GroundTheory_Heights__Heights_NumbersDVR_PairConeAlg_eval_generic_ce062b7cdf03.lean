-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_PairConeAlg_eval_generic_ce062b7cdf03
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:40:33.354898+00:00
-- url     : https://prove2.me/submissions/94c79a36-c967-4f83-82d0-6779dd41c003

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairConeAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairConeAlg

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.PairConeAlg
namespace GroundTheory.Heights₂.Heights.NumbersDVR.PairConeAlg
theorem _root_.solution {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ]
    [Algebra Ω Φ] {N : ℕ} (e u : Module.Basis (Fin N) Ω E) (t : Fin N → Φ) (ψ : Module.Dual Ω E) :
    ∑ i, t i * algebraMap Ω Φ (ψ (e i)) =
      ∑ q, (∑ i, t i * algebraMap Ω Φ (u.repr (e i) q)) * algebraMap Ω Φ (ψ (u q)) := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : ψ (e i) = ∑ q, u.repr (e i) q * ψ (u q) := by
    conv_lhs => rw [← u.sum_repr (e i)]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
  rw [h, map_sum, Finset.mul_sum]
  simp only [map_mul, mul_assoc]
end GroundTheory.Heights₂.Heights.NumbersDVR.PairConeAlg
