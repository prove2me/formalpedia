-- Prove2me | solution 1 for PIQnLT.single_lev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:56:34.498965+00:00
-- url     : https://prove2.me/submissions/89b1beec-7d41-4734-890c-61e78e42da6c

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_ExpLz
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_LzConjTranspose

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
theorem _root_.solution (a b : Fin (2 * r' + k + 1)) :
    Matrix.single (levPos k i r' a) (levPos k i r' b) (1 : ℂ) = Lz k i r' (Matrix.single a b 1) := by
  ext p q
  have ha := a.isLt
  have hb := b.isLt
  simp only [Lz, Matrix.single_apply, levPos, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)
end PIQnLT
