-- Prove2me | solution 1 for PIQnLT.hpart1_lev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:56:35.725276+00:00
-- url     : https://prove2.me/submissions/5f850e56-8f34-482a-8083-568d643f051a

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_ExpLz
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_LzConjTranspose
import Theorems.Thm_PIQnLT_Lz_sub
import Theorems.Thm_PIQnLT_Lz_smul
import Theorems.Thm_PIQnLT_hpk_mul_Lz
import Theorems.Thm_PIQnLT_Lz_mul_hpk
import Theorems.Thm_PIQnLT_Lz_conjTranspose
import Theorems.Thm_PIQnLT_single_lev
import Theorems.Thm_PIQnLT_hpk_inv

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
    hpart1 (Hpk k (i + r')) (Matrix.single (levPos k i r' a) (levPos k i r' b) 1) =
      Lz k i r' (hpart1 (Hpk k r') (Matrix.single a b 1)) := by
  unfold hpart1
  rw [hpk_inv, hpk_inv, single_lev, Lz_conjTranspose, hpk_mul_Lz, Lz_mul_hpk, Lz_smul, Lz_sub]
end PIQnLT
