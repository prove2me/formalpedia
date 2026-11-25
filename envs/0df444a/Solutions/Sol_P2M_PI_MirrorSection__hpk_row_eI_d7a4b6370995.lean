-- Prove2me | solution 1 for P2M_PI_MirrorSection__hpk_row_eI_d7a4b6370995
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:44:47.902601+00:00
-- url     : https://prove2.me/submissions/78fa2704-a035-42a6-9242-38e7e2767944

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_HpkRowEsI

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
theorem _root_.solution (b : Fin r) (l : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r b) l = if l = esI k r b then 1 else 0 := by
  simp only [Hpk, esI, eI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega
end PI.MirrorSection₂
