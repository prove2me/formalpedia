-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DSIC.det_sub_noninj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:39:58.698255+00:00
-- url     : https://prove2.me/submissions/4ed8b57e-1d7c-4a75-a235-4bdde83f7b3d

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
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → Fin n) (hc : ¬ Function.Injective c) :
    (A.submatrix id c).det = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hc
  exact Matrix.det_zero_of_column_eq hne (fun k => by simp [hij])
end PI.UnitaryGroupMassFormula.DSIC
