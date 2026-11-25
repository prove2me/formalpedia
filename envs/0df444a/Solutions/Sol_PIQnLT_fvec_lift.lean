-- Prove2me | solution 1 for PIQnLT.fvec_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:32:40.718043+00:00
-- url     : https://prove2.me/submissions/46f7df68-2715-4c51-a088-17114eb06f8d

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_LzConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_SecondCapelliMinorLevel
import Theorems.Thm_PIQnLT_bvec_lev
import Theorems.Thm_PIQnLT_lev_val


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
theorem _root_.solution (z : Fin (2 * r' + k + 1) → ℂ) :
    fvec k (i + r') (liftVec k i r' z) ⟨i, by omega⟩ = liftVec k i r' (fvec k r' z 0) := by
  simp only [fvec]
  split_ifs with h1 h2 h2
  · rw [← bvec_lev]
    congr 1
    apply Fin.ext
    simp [eI, lev_val]
  · exfalso
    simp only [Fin.val_zero, Fin.val_mk] at h1 h2
    omega
  · exfalso
    simp only [Fin.val_zero, Fin.val_mk] at h1 h2
    omega
  · rfl
end PIQnLT
