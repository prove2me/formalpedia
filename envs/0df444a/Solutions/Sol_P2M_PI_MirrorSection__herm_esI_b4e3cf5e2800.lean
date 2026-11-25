-- Prove2me | solution 1 for P2M_PI_MirrorSection__herm_esI_b4e3cf5e2800
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:19:22.581542+00:00
-- url     : https://prove2.me/submissions/eb49b52b-b8b1-4db2-b1b7-d3199a25d9dc

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_HpkRowEsI
import Theorems.Thm_P2M_PI_MirrorSection__hpk_row_esI_303aaeab59d3

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
    herm (Hpk k r) y (bvec (esI k r b)) = y (eI k r b) := by
  unfold herm
  simp [bvec, dotProduct, Pi.single_apply, Matrix.mulVec, hpk_row_esI]
end PI.MirrorSection₂
