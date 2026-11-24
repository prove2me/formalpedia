-- Prove2me | solution 1 for P2M_PI_MirrorSection__det_ut_7f3e5f0304a5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:04:43.319245+00:00
-- url     : https://prove2.me/submissions/be8d7729-1c53-436b-b23b-288398950bc7

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_IsMonomialConjTranspose

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
theorem _root_.solution {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ UTset m) : u.det = 1 := by
  rw [det_of_upperTriangular (fun i j h => hu.1 i j h)]
  simp [hu.2]
end PI.MirrorSection₂
