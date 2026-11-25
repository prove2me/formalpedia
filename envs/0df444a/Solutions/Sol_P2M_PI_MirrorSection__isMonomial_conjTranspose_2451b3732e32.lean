-- Prove2me | solution 1 for P2M_PI_MirrorSection__isMonomial_conjTranspose_2451b3732e32
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:55:50.742106+00:00
-- url     : https://prove2.me/submissions/cbe95763-d851-474c-a4dd-4d5a70f88c23

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_IsMonomialConjTranspose
import Theorems.Thm_P2M_PI_MirrorSection__monomialMatrix_conjTranspose_6ef84c3c3930

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
open Formalism.FourierDecayAlt.C2
variable {m : ℕ}
namespace PI.MirrorSection₂
theorem _root_.solution {P : Matrix (Fin m) (Fin m) ℂ} (hP : IsMonomial P) : IsMonomial Pᴴ := by
  obtain ⟨w, d, hd, rfl⟩ := hP
  exact ⟨w.symm, fun a => star (d (w.symm a)), fun a => by simpa using hd (w.symm a),
    monomialMatrix_conjTranspose w d⟩
end PI.MirrorSection₂
