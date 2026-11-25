-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_monomial_bound_07979692c060
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:07:01.760886+00:00
-- url     : https://prove2.me/submissions/f6a95f5b-8bc2-4432-bc0e-0b9b379f4543

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_MonomialValuesOneBlock
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_exists_split_140b0b462c0b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_prod_pow_add_fd787651d819

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
open scoped Pointwise
noncomputable section
open GroundTheory.Heights₂.Heights.SpanningAtDominantWeight
variable {ι : Type} [Fintype ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.SpanningAtDominantWeight
theorem _root_.solution {Q : Ideal (MvPolynomial (Coord n) ℤ)} {A : Geo.HermLine (blockIdx n)} {b : ι → ℕ}
    (hA : Geo.MonomialsBounded (ι := blockIdx n) Q A b) {z : Coord n → ℂ}
    (hz : z ∈ Geo.mcPts (ι := blockIdx n) Q) :
    ∀ τ : ℕ, ∀ μ : Coord n →₀ ℕ, (∀ k, ∑ i, μ ⟨k, i⟩ = (τ • b) k) → ‖∏ p, z p ^ μ p‖ ≤ A.h z ^ τ := by
  intro τ
  induction τ with
  | zero =>
    intro μ hμ
    have h0 : ∀ p, μ p = 0 := fun p ↦ by
      have := hμ p.1
      rw [zero_smul, Pi.zero_apply, Finset.sum_eq_zero_iff] at this
      exact this p.2 (Finset.mem_univ _)
    simp [h0]
  | succ τ ih =>
    intro μ hμ
    obtain ⟨μ₁, μ₂, rfl, h₁, h₂⟩ := exists_split μ (τ • b) b (fun k ↦ by rw [hμ k, succ_nsmul]; rfl)
    rw [prod_pow_add, norm_mul, pow_succ]
    exact mul_le_mul (ih μ₁ h₁) (hA z hz μ₂ h₂) (norm_nonneg _) (pow_nonneg (A.pos z hz.1).le _)
end GroundTheory.Heights₂.Heights.SpanningAtDominantWeight
