-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DSIC.quasi_determinant_conj_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:18:39.763628+00:00
-- url     : https://prove2.me/submissions/46155ad8-3356-47af-83a8-95f25968d82a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_CentralScalar
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_QuasiDeterminantConjInv
import Theorems.Thm_PI_UnitaryGroupMassFormula_DSIC_qdet_eq_qF
import Theorems.Thm_PI_UnitaryGroupMassFormula_DSIC_qF_row
import Theorems.Thm_PI_UnitaryGroupMassFormula_DSIC_qF_col

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.DSIC
open Finset
open scoped Matrix
namespace PI.UnitaryGroupMassFormula.DSIC
theorem _root_.solution : QdetConjInv := by
  intro A _ _ n E hE g hg u
  have hdet : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).mp hg
  have hT : (Formalism.REAL.Tm fun a b => ∑ c, ∑ d, (g c a * g⁻¹ b d) • E c d) =
      fun x a b => ∑ c, gᵀ a c • ∑ d, (g⁻¹)ᵀ d b • Formalism.REAL.Tm E x c d := by
    funext x a b
    simp only [Formalism.REAL.Tm, Matrix.transpose_apply, smul_add, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
    congr 1
    simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← Finset.sum_smul]
    have h1 : ∑ c, g c a * g⁻¹ b c = (g⁻¹ * g) b a := by
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun c _ => mul_comm _ _
    rw [h1, Matrix.nonsing_inv_mul _ hdet, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab, Ne.symm hab]
  rw [qdet_eq_qF, hT, qF_row, qF_col E hE, smul_smul, Matrix.det_transpose, Matrix.det_transpose,
    ← Matrix.det_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.det_one, one_smul]
end PI.UnitaryGroupMassFormula.DSIC
