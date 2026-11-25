-- Prove2me | solution 1 for PI.UnitKronW.unip_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:33:40.32387+00:00
-- url     : https://prove2.me/submissions/ed6259d7-443d-4118-a762-5ace0f2f6f64

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitKronecker_PosDefFormNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitKronecker_EqZeroOfMulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitKronW
open Matrix Polynomial ComplexOrder
namespace PI.UnitKronW
theorem _root_.solution {k : ℕ} {H W : Matrix (Fin k) (Fin k) ℂ} (hH : H.PosDef) (hW : Wᴴ * H * W = H)
    (v : Fin k → ℂ) (hv : (W - 1) *ᵥ ((W - 1) *ᵥ v) = 0) : (W - 1) *ᵥ v = 0 := by
  have pres : ∀ x y : Fin k → ℂ, star (W *ᵥ x) ⬝ᵥ (H *ᵥ (W *ᵥ y)) = star x ⬝ᵥ (H *ᵥ y) := by
    intro x y
    rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      ← Matrix.mul_assoc, hW]
  obtain ⟨u, hu⟩ : ∃ u, u = (W - 1) *ᵥ v := ⟨_, rfl⟩
  rw [← hu] at hv ⊢
  have hWu : W *ᵥ u = u := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
    exact hv
  have hu2 : u = W *ᵥ v - v := by rw [hu, Matrix.sub_mulVec, Matrix.one_mulVec]
  have h1 : star u ⬝ᵥ (H *ᵥ (W *ᵥ v)) = star u ⬝ᵥ (H *ᵥ v) := by
    have := pres u v
    rw [hWu] at this
    exact this
  have key : star u ⬝ᵥ (H *ᵥ u) = 0 := by
    nth_rw 2 [hu2]
    rw [Matrix.mulVec_sub]
    first
      | rw [dotProduct_sub, h1, sub_self]
      | rw [Matrix.dotProduct_sub, h1, sub_self]
  by_contra hne
  have hpos : 0 < star u ⬝ᵥ (H *ᵥ u) := by
    first
      | exact hH.2 u hne
      | exact hH.dotProduct_mulVec_pos hne
  rw [key] at hpos
  exact lt_irrefl _ hpos
end PI.UnitKronW
