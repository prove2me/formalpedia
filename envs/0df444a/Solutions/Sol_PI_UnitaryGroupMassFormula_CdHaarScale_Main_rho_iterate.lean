-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CdHaarScale.Main.rho_iterate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:37:55.077386+00:00
-- url     : https://prove2.me/submissions/31642a0a-a3c4-4c4f-a7bc-42f8f49858c4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CdHaarScale
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarScaling_MapEqSelfOfIterate
import Theorems.Thm_PI_UnitaryGroupMassFormula_CdHaarScale_Main_umat_rho

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MeasureTheory.Measure Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CdHaarScale PI.UnitaryGroupMassFormula.CdHaarScale.Main
namespace PI.UnitaryGroupMassFormula.CdHaarScale.Main
theorem _root_.solution {n : ℕ} {ε : Fin n → Bool} (π : Fin n ≃ Fin n) (hπ : ∀ i, ε (π i) = ε i)
    (m : ℕ) (a : Formalism.REAL.UJ ε) (i j : Fin n) :
    PI.CdHaarScale.umat ((rho π hπ)^[m] a) i j =
      PI.CdHaarScale.umat a ((π.symm)^[m] i) ((π.symm)^[m] j) := by
  induction m generalizing i j with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', umat_rho, Matrix.reindex_apply, Matrix.submatrix_apply, ih,
      Function.iterate_succ_apply, Function.iterate_succ_apply]
end PI.UnitaryGroupMassFormula.CdHaarScale.Main
