-- Prove2me | solution 1 for SWSSNet.Diffusion.remark_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T21:51:27.343838+00:00
-- url     : https://prove2.me/submissions/44a82b1a-c6f1-49d8-9fa4-94dc48c6c0c1

import Mathlib
import Definitions.Def_SWSSNet_Diffusion_Network
import Theorems.Thm_SWSSNet_Diffusion_theorem_3
import Theorems.Thm_SWSSNet_Diffusion_theorem_4

open Matrix MeasureTheory
open scoped NNReal ENNReal BigOperators

namespace SWSSRemark1Aux

open SWSSNet.Diffusion

/-- A tree network has at least one pool. -/
theorem exists_pool {I J : ℕ} (N : TreeNetwork I J) : Nonempty (Fin J) := by
  obtain ⟨v⟩ := N.isTree.isConnected.nonempty
  rcases v with i | j
  · by_contra hJ
    have hJ0 : J = 0 := by
      rcases Nat.eq_zero_or_pos J with h | h
      · exact h
      · exact absurd ⟨⟨0, h⟩⟩ hJ
    subst hJ0
    have h1 := N.xi_crp.1.2.2 i
    have h2 := N.lam_pos i
    simp at h1
    linarith
  · exact ⟨j⟩

/-- `⟨e, B₁⁻¹ p⟩ > 0` for a positive vector `p`, from the positivity of `eᵀB₁⁻¹`. -/
theorem denom_pos {I J : ℕ} (N : TreeNetwork I J) (ĵ : Fin J) (p : Fin I → ℝ)
    (hp : IsPosProb p) : 0 < ∑ i, ((B1 N ĵ)⁻¹ *ᵥ p) i := by
  have hpos := (theorem_3 N ĵ).2
  have hI : Nonempty (Fin I) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hp.2
    simp at this
  obtain ⟨i0⟩ := hI
  have hswap : ∑ i, ((B1 N ĵ)⁻¹ *ᵥ p) i = ∑ k, (∑ i, (B1 N ĵ)⁻¹ i k) * p k := by
    simp only [mulVec, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hswap]
  exact Finset.sum_pos (fun k _ => mul_pos (hpos k) (hp.1 k)) ⟨i0, Finset.mem_univ _⟩

theorem sign_div_pos (x d : ℝ) (hd : 0 < d) : SignType.sign (x / d) = SignType.sign x := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [sign_neg h, sign_neg (div_neg_of_neg_of_pos h hd)]
  · subst h; simp
  · rw [sign_pos h, sign_pos (div_pos h hd)]

end SWSSRemark1Aux

open SWSSNet.Diffusion SWSSRemark1Aux

theorem solution {I J : ℕ} (N : TreeNetwork I J) (p p' : Fin I → ℝ) (hp : IsPosProb p)
    (hp' : IsPosProb p') :
    SignType.sign (swss N p) = SignType.sign (swss N p') := by
  obtain ⟨ĵ⟩ := exists_pool N
  rw [theorem_4 N ĵ p hp, theorem_4 N ĵ p' hp', sign_div_pos _ _ (denom_pos N ĵ p hp),
    sign_div_pos _ _ (denom_pos N ĵ p' hp')]
