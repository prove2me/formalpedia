-- Prove2me | solution 1 for PIQnLT.hpk_mul_Lz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:15:48.032344+00:00
-- url     : https://prove2.me/submissions/4e12118a-49b4-45cf-8776-a30310276d3b

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_ExpLz
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_LzConjTranspose
import Theorems.Thm_PIQnLT_lev_in
import Theorems.Thm_PIQnLT_cases_lev
import Theorems.Thm_PIQnLT_Lz_lev
import Theorems.Thm_PIQnLT_Lz_out_left
import Theorems.Thm_PIQnLT_Lz_out_right
import Theorems.Thm_PIQnLT_hpk_lev
import Theorems.Thm_PIQnLT_hpk_out_in
import Theorems.Thm_PIQnLT_sum_lev


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PIQnLT
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k i r' : ℕ}
namespace PIQnLT
theorem _root_.solution (W : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    Hpk k (i + r') * Lz k i r' W = Lz k i r' (Hpk k r' * W) := by
  ext p q
  rw [Matrix.mul_apply, sum_lev (fun s => Hpk k (i + r') p s * Lz k i r' W s q)
    (fun s hs => by simp only [Lz_out_left W s q hs, mul_zero])]
  rcases cases_lev p with ⟨p', rfl⟩ | hp
  · rcases cases_lev q with ⟨q', rfl⟩ | hq
    · simp only [hpk_lev, Lz_lev, Matrix.mul_apply]
    · simp only [Lz_out_right _ _ _ hq, mul_zero, Finset.sum_const_zero]
  · simp only [hpk_out_in p _ hp (lev_in _), zero_mul, Finset.sum_const_zero, Lz_out_left _ _ _ hp]
end PIQnLT
