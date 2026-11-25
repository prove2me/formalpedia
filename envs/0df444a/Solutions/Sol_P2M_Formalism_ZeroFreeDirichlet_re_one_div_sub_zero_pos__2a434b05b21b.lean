-- Prove2me | solution 1 for P2M_Formalism_ZeroFreeDirichlet_re_one_div_sub_zero_pos__2a434b05b21b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:48:55.685827+00:00
-- url     : https://prove2.me/submissions/57dd68cd-fa3d-4d66-b693-63e064f869e2

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_RealSmallTOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ρ : ℂ)
    (hρ : DirichletCharacter.LFunction χ ρ = 0) (σ : ℝ) (hσ : 1 < σ) :
    0 < (1 / ((σ : ℂ) - ρ)).re := by
  have hre : ρ.re < 1 := by
    by_contra h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) (not_lt.mp h) hρ
  have hz : ((σ : ℂ) - ρ).re = σ - ρ.re := by simp
  have hpos : 0 < ((σ : ℂ) - ρ).re := by rw [hz]; linarith
  have hne : ((σ : ℂ) - ρ) ≠ 0 := by
    intro h; rw [h] at hpos; simp at hpos
  rw [one_div, Complex.inv_re]
  exact div_pos hpos (Complex.normSq_pos.mpr hne)
end Formalism.ZeroFreeDirichlet
