-- Prove2me | solution 1 for UpperTheory.Reformulated.B.SesquilinearFlipConj.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:46:47.278063+00:00
-- url     : https://prove2.me/submissions/60d36c62-869d-42d5-9136-dbc2953f56fe

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SesquilinearFlipConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace UpperTheory.Reformulated.B.SesquilinearFlipConj.Helpers
private theorem flipConj_apply {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (v w : V) :
    flipConj B v w = starRingEnd ℂ (B w v) := rfl
end UpperTheory.Reformulated.B.SesquilinearFlipConj.Helpers
end

set_option autoImplicit false

open UpperTheory.Reformulated.B.SesquilinearFlipConj.Helpers
namespace UpperTheory.Reformulated.B.SesquilinearFlipConj
theorem _root_.solution :
    ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] {ρ : Representation ℂ G V},
      UpperTheory.Reformulated.B.SesquilinearFlipConj.HasSesq ρ →
        ∃ (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
          B ≠ (0 : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) ∧
            (∀ (v w : V),
                ((B : V → V →ₗ⋆[ℂ] ℂ) w : V → ℂ) v = (starRingEnd ℂ : ℂ → ℂ) (((B : V → V →ₗ⋆[ℂ] ℂ) v : V → ℂ) w)) ∧
              ∀ (g : G) (v w : V),
                ((B : V → V →ₗ⋆[ℂ] ℂ) (((ρ : G → V →ₗ[ℂ] V) g : V → V) v) : V → ℂ) (((ρ : G → V →ₗ[ℂ] V) g : V → V) w) =
                  ((B : V → V →ₗ⋆[ℂ] ℂ) v : V → ℂ) w := by
  intro G V _ _ _ ρ hS
  obtain ⟨B, hB0, hBinv⟩ := hS
  classical
  by_cases hH : B + flipConj B = 0
  · have hrel : ∀ v w, B v w + starRingEnd ℂ (B w v) = 0 := by
      intro v w
      have := congrArg (fun F : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ => F v w) hH
      simpa [flipConj_apply] using this
    refine ⟨Complex.I • B, ?_, ?_, ?_⟩
    · intro h
      apply hB0
      have : (-Complex.I) • (Complex.I • B) = B := by
        rw [smul_smul]; simp
      rw [← this, h, smul_zero]
    · intro v w
      have h1 := hrel v w
      have h2 : starRingEnd ℂ (B v w) = - B w v := by
        have := congrArg (starRingEnd ℂ) h1
        simp at this
        linear_combination this
      simp only [LinearMap.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, h2]
      ring
    · intro g v w
      simp only [LinearMap.smul_apply, smul_eq_mul, hBinv]
  · refine ⟨B + flipConj B, hH, ?_, ?_⟩
    · intro v w
      simp only [LinearMap.add_apply, flipConj_apply, map_add, Complex.conj_conj]
      ring
    · intro g v w
      simp only [LinearMap.add_apply, flipConj_apply, hBinv]
end UpperTheory.Reformulated.B.SesquilinearFlipConj
