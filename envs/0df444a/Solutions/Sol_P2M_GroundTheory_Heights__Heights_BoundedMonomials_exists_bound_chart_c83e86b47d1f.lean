-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BoundedMonomials_exists_bound_chart_c83e86b47d1f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:53:09.003579+00:00
-- url     : https://prove2.me/submissions/ce95a7f8-5baa-4f8d-8bda-d21ef718a392

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BoundedMonomials_evalCone_X_bd364b1db4a5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BoundedMonomials_chartNorm_eq_93aea306bd91
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BoundedMonomials_chartNorm_scale_882ffc6428a7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BoundedMonomials_exists_bound_unitChart_e84cbb7a7312

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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.BoundedMonomials
namespace GroundTheory.Heights₂.Heights.BoundedMonomials
theorem _root_.solution {P : ArithVariety n} {A : HermLine n} (s : IntegralSection P A.deg)
    (c : (k : ι) → Fin (n k + 1)) :
    ∃ B : ℝ, ∀ z ∈ P.points ℂ, (∀ k, z k (c k) ≠ 0) → (∀ k i, ‖z k i‖ ≤ ‖z k (c k)‖) →
      ∀ (d : ι → ℕ) (e : MvPolynomial (Coord n) ℤ), IsChartForm P A.deg s.num s.den c d e →
        chartNorm A c d e z ≤ B := by
  by_cases hlive : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal
  · obtain ⟨d₀, e₀, he₀⟩ := s.regular c hlive
    obtain ⟨B, hB⟩ := exists_bound_unitChart A c d₀ e₀
    refine ⟨B, fun z hz hc hmax d e he ↦ ?_⟩
    obtain ⟨δ, hδe, hδ⟩ := he₀.1
    set u : ι → ℂ := fun k ↦ (z k (c k))⁻¹
    have hu : ∀ k, u k ≠ 0 := fun k ↦ inv_ne_zero (hc k)
    rw [chartNorm_eq s hz he he₀ hc hc, ← chartNorm_scale A c d₀ hδe hδ hu hz.1]
    refine hB _ ⟨fun k ↦ inv_mul_cancel₀ (hc k), fun k i ↦ ?_⟩
    rw [norm_mul, norm_inv, inv_mul_le_iff₀ (norm_pos_iff.mpr (hc k)), mul_one]
    exact hmax k i
  · refine ⟨0, fun z hz hc _ d e _ ↦ ?_⟩
    simp only [not_forall, not_not] at hlive
    obtain ⟨k, hk⟩ := hlive
    have h0 := hz.2 _ hk
    rw [evalCone_X] at h0
    exact absurd h0 (hc k)
end GroundTheory.Heights₂.Heights.BoundedMonomials
