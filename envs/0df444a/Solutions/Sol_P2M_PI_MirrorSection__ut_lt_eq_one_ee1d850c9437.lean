-- Prove2me | solution 1 for P2M_PI_MirrorSection__ut_lt_eq_one_ee1d850c9437
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:44:44.540158+00:00
-- url     : https://prove2.me/submissions/62a36728-a482-4d8f-b30a-a5ded811afbe

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
theorem _root_.solution {x : Matrix (Fin m) (Fin m) ℂ} (hu : x ∈ UTset m) (hl : x ∈ LTset m) : x = 1 := by
  ext i j
  rcases lt_trichotomy i j with h | h | h
  · rw [hl.1 i j h, Matrix.one_apply_ne (ne_of_lt h)]
  · subst h; rw [hu.2, Matrix.one_apply_eq]
  · rw [hu.1 i j h, Matrix.one_apply_ne (ne_of_gt h)]
end PI.MirrorSection₂
