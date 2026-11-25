-- Prove2me | solution 1 for PI.UD.framesDense_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:58:25.42896+00:00
-- url     : https://prove2.me/submissions/1210b41d-c4e9-4bf5-86b7-8c6016d92d18

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryDensity_EvalBindTorusSubst
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryDensity_VanishInvertible
import Theorems.Thm_PI_UD_famUnitDense
import Theorems.Thm_PI_UD_eval_bind_leftSubst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexOrder
open PI PI.UD
namespace PI.UD
theorem _root_.solution (hs : SVDStep) (hg : GramStep) : PI.FramesDense := by
  intro ι _ n G hG P hP
  choose C hC hCd using fun τ => hg n (G τ) (hG τ)
  have hCi : ∀ τ, C τ * (C τ)⁻¹ = 1 := fun τ =>
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hCd τ))
  have hiC : ∀ τ, (C τ)⁻¹ * C τ = 1 := fun τ =>
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hCd τ))
  have h0 : bind₁ (leftSubst (fun τ => (C τ)⁻¹)) P = 0 := by
    apply famUnitDense hs
    intro u hu
    rw [eval_bind_leftSubst]
    refine hP (fun τ => (C τ)⁻¹ * u τ) ?_
    intro τ
    rw [← hC τ]
    calc ((C τ)⁻¹ * u τ)ᴴ * ((C τ)ᴴ * C τ) * ((C τ)⁻¹ * u τ)
        = (u τ)ᴴ * ((C τ * (C τ)⁻¹)ᴴ * (C τ * (C τ)⁻¹ * u τ)) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hCi τ, conjTranspose_one, Matrix.one_mul, Matrix.one_mul, hu τ]
  apply MvPolynomial.funext
  intro x
  rw [map_zero]
  have h4 := eval_bind_leftSubst (fun τ => (C τ)⁻¹) P
    (fun τ => C τ * Matrix.of fun i j => x (τ, i, j))
  rw [h0, map_zero] at h4
  simp only [← Matrix.mul_assoc, hiC, Matrix.one_mul, Matrix.of_apply] at h4
  exact h4.symm
end PI.UD
