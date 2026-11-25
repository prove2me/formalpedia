-- Prove2me | solution 1 for P2M_PI_MirrorSection__herm_eI_18f96727ec1f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:01:25.078063+00:00
-- url     : https://prove2.me/submissions/baca5abc-8226-4b74-9e8a-361ebe520d38

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_HpkRowEsI
import Theorems.Thm_P2M_PI_MirrorSection__hpk_row_eI_d7a4b6370995

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
open PI PI.MirrorSection₂
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}
namespace PI.MirrorSection₂
theorem _root_.solution (y : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    herm (Hpk k r) y (bvec (eI k r b)) = y (esI k r b) := by
  unfold herm
  simp [bvec, dotProduct, Pi.single_apply, Matrix.mulVec, hpk_row_eI]
end PI.MirrorSection₂
