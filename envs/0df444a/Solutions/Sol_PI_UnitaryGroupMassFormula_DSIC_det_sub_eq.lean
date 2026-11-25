-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DSIC.det_sub_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:39:40.821829+00:00
-- url     : https://prove2.me/submissions/8aa17514-0aa2-468b-b230-212cb10bec48

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_CentralScalar
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_QuasiDeterminantConjInv

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
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → Fin n) :
    ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, A (σ k) (c k) = (A.submatrix id c).det := by
  rw [Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  rfl
end PI.UnitaryGroupMassFormula.DSIC
