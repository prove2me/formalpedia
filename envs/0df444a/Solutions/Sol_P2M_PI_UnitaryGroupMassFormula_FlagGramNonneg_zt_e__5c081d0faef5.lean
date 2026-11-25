-- Prove2me | solution 1 for P2M_PI_UnitaryGroupMassFormula_FlagGramNonneg_zt_e__5c081d0faef5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:46:35.022905+00:00
-- url     : https://prove2.me/submissions/7cddf72d-e186-4634-829c-773a78cb33bb

import Definitions.Def_Formalism_PeriodIntegrals_FlagGramNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FlagGramNonnegativity_SumMulCommMulVec
import Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_sum_mul_vecMul
import Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_left_sub_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PI.FlagGramNonneg
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FlagGramNonneg
variable {E : Type} [Field E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
variable (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (e e' : Fin r → V) (z z' : V)
namespace PI.UnitaryGroupMassFormula.FlagGramNonneg
theorem _root_.solution (hA : IsUnit (amat hT e e').det) (c : Fin r) : hT (zt hT e e' z) (e' c) = 0 := by
  unfold zt
  rw [left_sub_sum]
  simp only [star_star]
  have h : ∑ a, (vvec hT z e' ᵥ* (amat hT e e')⁻¹) a * hT (e a) (e' c) =
      ((vvec hT z e' ᵥ* (amat hT e e')⁻¹) ᵥ* amat hT e e') c :=
    sum_mul_vecMul (amat hT e e') _ c
  rw [h, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hA, Matrix.vecMul_one]
  simp [vvec]
end PI.UnitaryGroupMassFormula.FlagGramNonneg
