-- Prove2me | solution 1 for P2M_PI_MirrorSection__lt_conjTranspose_880787298ed1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:04:45.478858+00:00
-- url     : https://prove2.me/submissions/1e053a46-04f0-49c9-b186-03ee18ffdc40

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
theorem _root_.solution {l : Matrix (Fin m) (Fin m) ℂ} (hl : l ∈ LTset m) : lᴴ ∈ UTset m := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [conjTranspose_apply, hl.1 j i hij, star_zero]
  · rw [conjTranspose_apply, hl.2, star_one]
end PI.MirrorSection₂
