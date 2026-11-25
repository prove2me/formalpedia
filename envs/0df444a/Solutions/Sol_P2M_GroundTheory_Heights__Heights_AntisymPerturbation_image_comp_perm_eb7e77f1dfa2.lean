-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AntisymPerturbation_image_comp_perm_eb7e77f1dfa2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:36:25.31181+00:00
-- url     : https://prove2.me/submissions/5717268e-06c9-43e8-8a7b-6457bfd2d9f0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymPerturbation

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
open MvPolynomial
open GroundTheory.Heights₂.Heights.AntisymPerturbation
variable {T : Type} [Fintype T] [DecidableEq T] {N j : ℕ}
omit [Fintype T] [DecidableEq T]
namespace GroundTheory.Heights₂.Heights.AntisymPerturbation
theorem _root_.solution (σ : Equiv.Perm (T × Fin N)) (τ : T) {a b a' b' : Fin N}
    (hσa : σ (τ, a) = (τ, a')) (hσb : σ (τ, b) = (τ, b')) {K : Set (T × Fin N → ℝ)}
    (hKc : IsCompact K) (hKH : K ⊆ diagHyperplane T N τ a' b')
    (hKO : ∃ O : Set (T × Fin N → ℝ), IsOpen O ∧ (O ∩ diagHyperplane T N τ a' b').Nonempty ∧
      O ∩ diagHyperplane T N τ a' b' ⊆ K) :
    IsCompact ((fun y => y ∘ ⇑σ) '' K) ∧ (fun y => y ∘ ⇑σ) '' K ⊆ diagHyperplane T N τ a b ∧
      ∃ O : Set (T × Fin N → ℝ), IsOpen O ∧ (O ∩ diagHyperplane T N τ a b).Nonempty ∧
        O ∩ diagHyperplane T N τ a b ⊆ (fun y => y ∘ ⇑σ) '' K := by
  have hinv_a : σ⁻¹ (τ, a') = (τ, a) := by rw [← hσa]; simp
  have hinv_b : σ⁻¹ (τ, b') = (τ, b) := by rw [← hσb]; simp
  refine ⟨hKc.image (continuous_pi fun p => continuous_apply _), ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    show y (σ (τ, a)) = y (σ (τ, b))
    rw [hσa, hσb]
    exact hKH hy
  · obtain ⟨O, hO, ⟨y0, hy0O, hy0H⟩, hOK⟩ := hKO
    refine ⟨(fun x => x ∘ ⇑σ⁻¹) ⁻¹' O, hO.preimage (continuous_pi fun p => continuous_apply _),
      ⟨y0 ∘ ⇑σ, ?_, ?_⟩, ?_⟩
    · have e : (y0 ∘ ⇑σ) ∘ ⇑σ⁻¹ = y0 := by funext p; simp
      show (y0 ∘ ⇑σ) ∘ ⇑σ⁻¹ ∈ O
      rw [e]
      exact hy0O
    · show y0 (σ (τ, a)) = y0 (σ (τ, b))
      rw [hσa, hσb]
      exact hy0H
    · rintro x ⟨hxO, hxH⟩
      refine ⟨x ∘ ⇑σ⁻¹, hOK ⟨hxO, ?_⟩, ?_⟩
      · show x (σ⁻¹ (τ, a')) = x (σ⁻¹ (τ, b'))
        rw [hinv_a, hinv_b]
        exact hxH
      · funext p; simp
end GroundTheory.Heights₂.Heights.AntisymPerturbation
