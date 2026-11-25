-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_exists_pow_mul_mem_of_mem_span_1463fb00a4ce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:19:14.840613+00:00
-- url     : https://prove2.me/submissions/d9615e26-dc15-44e5-80a1-444a08744076

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsJoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefPlusAmple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleTwistGenerated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
open scoped Pointwise
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {B : Subalgebra k Ω} {J : Chart x} {T : Set Ω}
    {s b z : Ω} {n : ℕ} (hs : s ≠ 0) (hb : b ∈ B) (hT : ∀ y ∈ T, y / s ^ n ∈ B)
    (hcoef : ∀ c ∈ chartRing k x J, ∃ E : ℕ, b ^ E * c ∈ B)
    (hz : z * s ^ n ∈ Submodule.span (chartRing k x J) T) : ∃ E : ℕ, b ^ E * z ∈ B := by
  have key : ∀ y ∈ Submodule.span (chartRing k x J) T, ∃ E : ℕ, b ^ E * y / s ^ n ∈ B := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact ⟨0, by rw [pow_zero, one_mul]; exact hT y hy⟩
    | zero => exact ⟨0, by simp⟩
    | add y₁ y₂ _ _ h₁ h₂ =>
      obtain ⟨E₁, h₁⟩ := h₁
      obtain ⟨E₂, h₂⟩ := h₂
      refine ⟨E₁ + E₂, ?_⟩
      have h7 : b ^ (E₁ + E₂) * (y₁ + y₂) / s ^ n =
          b ^ E₂ * (b ^ E₁ * y₁ / s ^ n) + b ^ E₁ * (b ^ E₂ * y₂ / s ^ n) := by ring
      rw [h7]
      exact add_mem (mul_mem (pow_mem hb _) h₁) (mul_mem (pow_mem hb _) h₂)
    | smul c y _ h =>
      obtain ⟨E, h⟩ := h
      obtain ⟨E', hE'⟩ := hcoef c c.2
      refine ⟨E' + E, ?_⟩
      rw [chartRing_smul_def]
      have h8 : b ^ (E' + E) * ((c : Ω) * y) / s ^ n = b ^ E' * (c : Ω) * (b ^ E * y / s ^ n) := by
        ring
      rw [h8]
      exact mul_mem hE' h
  obtain ⟨E, hE⟩ := key _ hz
  refine ⟨E, ?_⟩
  have h9 : b ^ E * (z * s ^ n) / s ^ n = b ^ E * z := by
    field_simp
  rwa [h9] at hE
end GroundTheory.Heights₂.Heights.Kleiman
