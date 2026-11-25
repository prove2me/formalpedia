-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleSecs_exists_pow_mul_mem_pow_84ca433e9bcd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:21:14.613801+00:00
-- url     : https://prove2.me/submissions/5195df3e-770a-4d53-95aa-903f0029080e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleSecsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleSecs

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
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleSecs
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω]
namespace GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleSecs
theorem _root_.solution {A : Subalgebra k Ω} {L : Submodule A Ω} {r : ℕ}
    {h : Fin (r + 1) → Ω} (hL : ∀ l, h l ∈ L) {j : Fin (r + 1)} (hj : h j ≠ 0) {t : Ω}
    (ht : t ∈ ampleBase (S := k) h j) : ∃ e, h j ^ e * t ∈ L ^ e := by
  induction ht using Algebra.adjoin_induction with
  | mem t ht =>
    obtain ⟨l, rfl⟩ := ht
    exact ⟨1, by rw [pow_one, pow_one, mul_div_cancel₀ _ hj]; exact hL l⟩
  | algebraMap c =>
    refine ⟨0, ?_⟩
    rw [pow_zero, pow_zero, one_mul, Submodule.mem_one]
    exact ⟨⟨_, Subalgebra.algebraMap_mem A c⟩, rfl⟩
  | add t₁ t₂ _ _ h₁ h₂ =>
    obtain ⟨e₁, he₁⟩ := h₁
    obtain ⟨e₂, he₂⟩ := h₂
    refine ⟨e₁ + e₂, ?_⟩
    have hs : h j ^ (e₁ + e₂) * (t₁ + t₂) = h j ^ e₂ * (h j ^ e₁ * t₁) + h j ^ e₁ * (h j ^ e₂ * t₂) := by
      ring
    rw [hs, pow_add]
    exact Submodule.add_mem _
      (by rw [mul_comm (L ^ e₁)]; exact Submodule.mul_mem_mul (Submodule.pow_mem_pow _ (hL j) _) he₁)
      (Submodule.mul_mem_mul (Submodule.pow_mem_pow _ (hL j) _) he₂)
  | mul t₁ t₂ _ _ h₁ h₂ =>
    obtain ⟨e₁, he₁⟩ := h₁
    obtain ⟨e₂, he₂⟩ := h₂
    refine ⟨e₁ + e₂, ?_⟩
    have hs : h j ^ (e₁ + e₂) * (t₁ * t₂) = (h j ^ e₁ * t₁) * (h j ^ e₂ * t₂) := by ring
    rw [hs, pow_add]
    exact Submodule.mul_mem_mul he₁ he₂
end GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleSecs
