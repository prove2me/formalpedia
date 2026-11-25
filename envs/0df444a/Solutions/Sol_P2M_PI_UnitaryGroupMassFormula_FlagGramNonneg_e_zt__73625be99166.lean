-- Prove2me | solution 1 for P2M_PI_UnitaryGroupMassFormula_FlagGramNonneg_e_zt__73625be99166
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:45:30.269255+00:00
-- url     : https://prove2.me/submissions/4828f8ae-2917-4bbf-bd19-bb7060c61134

import Definitions.Def_Formalism_PeriodIntegrals_FlagGramNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FlagGramNonnegativity_SumMulCommMulVec
import Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_sum_mul_comm_mulVec
import Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_right_sub_sum

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
theorem _root_.solution (hA : IsUnit (amat hT e e').det) (c : Fin r) : hT (e c) (zt' hT e e' z') = 0 := by
  unfold zt'
  rw [right_sub_sum]
  have h : ∑ b, ((amat hT e e')⁻¹ *ᵥ uvec hT e z') b * hT (e c) (e' b) =
      (amat hT e e' *ᵥ ((amat hT e e')⁻¹ *ᵥ uvec hT e z')) c :=
    sum_mul_comm_mulVec (amat hT e e') _ c
  rw [h, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hA, Matrix.one_mulVec]
  simp [uvec]
end PI.UnitaryGroupMassFormula.FlagGramNonneg
