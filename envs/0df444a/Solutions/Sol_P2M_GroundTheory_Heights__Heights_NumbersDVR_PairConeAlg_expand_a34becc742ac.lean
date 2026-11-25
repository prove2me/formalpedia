-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_PairConeAlg_expand_a34becc742ac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:25:22.446911+00:00
-- url     : https://prove2.me/submissions/c55e44ad-0d45-435a-ba22-cd709528e2f7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairConeAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairConeAlg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PairConeAlg_eval_generic_ce062b7cdf03

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
    [Algebra Ω Φ] {N : ℕ} {σ : Type*} (e u : Module.Basis (Fin N) Ω E) (t : Fin N → Φ)
    (ψ : Module.Dual Ω E) (Y Z : Ω) (o : σ) :
    ∑ q, C (algebraMap Ω Φ (ψ (u q) / Z)) *
        (C (algebraMap Ω Φ Y * ∑ i, t i * algebraMap Ω Φ (u.repr (e i) q)) * (X o : MvPolynomial σ Φ)) =
      C (algebraMap Ω Φ (Y / Z) * ∑ i, t i * algebraMap Ω Φ (ψ (e i))) * X o := by
  rw [eval_generic e u t ψ, Finset.mul_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← mul_assoc, ← map_mul]
  congr 2
  simp only [map_div₀]
  ring
end GroundTheory.Heights₂.Heights.NumbersDVR.PairConeAlg
