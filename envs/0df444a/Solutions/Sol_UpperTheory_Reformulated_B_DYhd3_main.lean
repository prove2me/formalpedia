-- Prove2me | solution 1 for UpperTheory.Reformulated.B.DYhd3.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:51:18.408748+00:00
-- url     : https://prove2.me/submissions/4c5ebd39-f3b6-4489-8b76-6944c81c5d34

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsBisTer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.DYhd3
theorem _root_.solution :
    ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V] (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ),
      (∀ (u u' : V), (starRingEnd ℂ : ℂ → ℂ) (((B : V → V →ₗ[ℂ] ℂ) u : V → ℂ) u') = ((B : V → V →ₗ[ℂ] ℂ) u' : V → ℂ) u) →
        (∀ (u : V), (0 : ℝ) ≤ (((B : V → V →ₗ[ℂ] ℂ) u : V → ℂ) u).re) →
          ∀ (x y : V),
            ‖((B : V → V →ₗ[ℂ] ℂ) x : V → ℂ) y‖ ^ (2 : ℕ) ≤
              (((B : V → V →ₗ[ℂ] ℂ) x : V → ℂ) x).re * (((B : V → V →ₗ[ℂ] ℂ) y : V → ℂ) y).re := by
  intro V _ _ B hsymm hpos x y
  let c : PreInnerProductSpace.Core ℂ V :=
    { inner := fun u v => B u v
      conj_inner_symm := fun u v => hsymm v u
      re_inner_nonneg := fun u => hpos u
      add_left := fun u v w => by simp
      smul_left := fun u v r => by simp }
  have h : ‖B x y‖ * ‖B y x‖ ≤ (B x x).re * (B y y).re :=
    InnerProductSpace.Core.inner_mul_inner_self_le (c := c) x y
  have h2 : ‖B y x‖ = ‖B x y‖ := by
    rw [← hsymm x y]; exact RCLike.norm_conj _
  rw [h2] at h
  rw [sq]
  exact h
end UpperTheory.Reformulated.B.DYhd3
