-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_exists_pow_mul_sub_rename_mem_1157a3bef5d7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:31:21.232672+00:00
-- url     : https://prove2.me/submissions/a62ccc21-ca81-4db5-9f57-fc900c180f05

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreRadicalAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RadicalAwayRabinowitsch

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
variable {R : Type*} [CommRing R] {ι : Type*}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (g : MvPolynomial ι R) (h : MvPolynomial (Option ι) R) :
    ∃ (N : ℕ) (f : MvPolynomial ι R), rename some g ^ N * h - rename some f ∈
      (Ideal.span {X none * rename some g - 1} : Ideal (MvPolynomial (Option ι) R)) := by
  induction h using MvPolynomial.induction_on with
  | C a => exact ⟨0, C a, by simp⟩
  | add p q hp hq =>
    obtain ⟨N₁, f₁, h₁⟩ := hp
    obtain ⟨N₂, f₂, h₂⟩ := hq
    refine ⟨N₁ + N₂, g ^ N₂ * f₁ + g ^ N₁ * f₂, ?_⟩
    have e : rename some g ^ (N₁ + N₂) * (p + q) - rename some (g ^ N₂ * f₁ + g ^ N₁ * f₂) =
        rename some g ^ N₂ * (rename some g ^ N₁ * p - rename some f₁) +
          rename some g ^ N₁ * (rename some g ^ N₂ * q - rename some f₂) := by
      simp only [map_add, map_mul, map_pow]; ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h₁) (Ideal.mul_mem_left _ _ h₂)
  | mul_X p j hp =>
    obtain ⟨N, f, hf⟩ := hp
    cases j with
    | none =>
      refine ⟨N + 1, f, ?_⟩
      have e : rename some g ^ (N + 1) * (p * X none) - rename some f =
          (rename some g ^ N * p - rename some f) +
            rename some g ^ N * p * (X none * rename some g - 1) := by ring
      rw [e]
      exact Ideal.add_mem _ hf (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))
    | some i =>
      refine ⟨N, f * X i, ?_⟩
      have e : rename some g ^ N * (p * X (some i)) - rename some (f * X i) =
          (rename some g ^ N * p - rename some f) * X (some i) := by
        simp only [map_mul, rename_X]; ring
      rw [e]
      exact Ideal.mul_mem_right _ _ hf
end GroundTheory.Heights₂.Heights
