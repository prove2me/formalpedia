-- Prove2me | solution 1 for UpperTheory.Reformulated.B.FinitelyGeneratedModPow.fg_mod_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:29.959794+00:00
-- url     : https://prove2.me/submissions/fa674e7b-72ec-4324-be42-c61f0d94c72b

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FinitelyGeneratedModPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.FinitelyGeneratedModPow
namespace UpperTheory.Reformulated.B.FinitelyGeneratedModPow
theorem _root_.solution {O A : Type} [CommRing O] [CommRing A] [Algebra O A] [IsNoetherianRing A]
    (m : Ideal A) (hres : ∀ x : A, ∃ a : O, x - algebraMap O A a ∈ m) (n : ℕ) :
    ∃ N : Submodule O A, N.FG ∧ ∀ x : A, ∃ y ∈ N, x - y ∈ m ^ n := by
  induction n with
  | zero => exact ⟨⊥, Submodule.fg_bot, fun x => ⟨0, Submodule.zero_mem _, by simp⟩⟩
  | succ n ih =>
    obtain ⟨N, hN, hx⟩ := ih
    obtain ⟨s, hs⟩ : (m ^ n).FG := IsNoetherian.noetherian (m ^ n)
    have key : ∀ z ∈ Ideal.span (s : Set A),
        ∃ w ∈ Submodule.span O (s : Set A), z - w ∈ m ^ (n + 1) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz => exact ⟨z, Submodule.subset_span hz, by simp⟩
      | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
      | add z₁ z₂ _ _ h₁ h₂ =>
        obtain ⟨w₁, hw₁, e₁⟩ := h₁
        obtain ⟨w₂, hw₂, e₂⟩ := h₂
        refine ⟨w₁ + w₂, Submodule.add_mem _ hw₁ hw₂, ?_⟩
        have : z₁ + z₂ - (w₁ + w₂) = (z₁ - w₁) + (z₂ - w₂) := by ring
        rw [this]
        exact Ideal.add_mem _ e₁ e₂
      | smul a z hz h =>
        obtain ⟨w, hw, e⟩ := h
        obtain ⟨c, hc⟩ := hres a
        have hz' : z ∈ m ^ n := by rw [← hs]; exact hz
        refine ⟨c • w, Submodule.smul_mem _ c hw, ?_⟩
        have : a • z - c • w = z * (a - algebraMap O A c) + algebraMap O A c * (z - w) := by
          rw [smul_eq_mul, Algebra.smul_def]; ring
        rw [this]
        refine Ideal.add_mem _ ?_ (Ideal.mul_mem_left _ _ e)
        rw [pow_succ]
        exact Ideal.mul_mem_mul hz' hc
    refine ⟨N ⊔ Submodule.span O (s : Set A), hN.sup ⟨s, rfl⟩, fun x => ?_⟩
    obtain ⟨y, hy, hxy⟩ := hx x
    rw [← hs] at hxy
    obtain ⟨w, hw, e⟩ := key _ hxy
    refine ⟨y + w, Submodule.add_mem_sup hy hw, ?_⟩
    rwa [← sub_sub]
end UpperTheory.Reformulated.B.FinitelyGeneratedModPow
