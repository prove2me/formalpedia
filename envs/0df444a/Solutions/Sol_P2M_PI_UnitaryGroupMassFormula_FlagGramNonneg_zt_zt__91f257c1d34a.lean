-- Prove2me | solution 1 for P2M_PI_UnitaryGroupMassFormula_FlagGramNonneg_zt_zt__91f257c1d34a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:54:58.194736+00:00
-- url     : https://prove2.me/submissions/95692b05-55f3-4fb8-adee-ee37d8aabbb7

import Definitions.Def_Formalism_PeriodIntegrals_FlagGramNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FlagGramNonnegativity_SumMulCommMulVec
import Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_left_sub_sum
import Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_right_sub_sum
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_FlagGramNonneg_zt_e__5c081d0faef5

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
theorem _root_.solution (hA : IsUnit (amat hT e e').det) :
    hT (zt hT e e' z) (zt' hT e e' z') = sval hT e e' z z' := by
  rw [zt', right_sub_sum]
  simp only [zt_e' hT e e' z hA, mul_zero, Finset.sum_const_zero, sub_zero]
  rw [zt, left_sub_sum]
  simp only [star_star]
  unfold sval
  rw [Matrix.dotProduct_mulVec]
  simp [dotProduct, uvec]
end PI.UnitaryGroupMassFormula.FlagGramNonneg
