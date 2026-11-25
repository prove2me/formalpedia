-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_not_unit_of_pow_succ_d05b5f3dd358
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:24:47.842558+00:00
-- url     : https://prove2.me/submissions/b33fe298-fb8b-4335-a283-f6465c356c51

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PPrimitiveUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution {R : Type*} [CommRing R] [IsDomain R] {ϖ : R} (hϖ : Irreducible ϖ)
    (u₁ u₂ : Rˣ) (i d : ℕ) {x y : R} (hy : IsUnit y)
    (h : (u₂ : R) * ϖ ^ (i + d + 1) * x = u₁ * ϖ ^ i * y) : False := by
  have hpow : ϖ ^ i ≠ 0 := pow_ne_zero _ hϖ.ne_zero
  have h' : (u₂ : R) * ϖ ^ (d + 1) * x = u₁ * y := by
    apply mul_left_cancel₀ hpow
    calc ϖ ^ i * ((u₂ : R) * ϖ ^ (d + 1) * x) = (u₂ * ϖ ^ (i + d + 1)) * x := by ring
      _ = (u₁ * ϖ ^ i) * y := h
      _ = ϖ ^ i * (u₁ * y) := by ring
  have hu : IsUnit ((u₁ : R) * y) := u₁.isUnit.mul hy
  rw [← h'] at hu
  exact hϖ.not_isUnit (isUnit_of_dvd_unit (Dvd.intro ((u₂ : R) * ϖ ^ d * x) (by ring)) hu)
end GroundTheory.Heights₂.Heights.Vertical
