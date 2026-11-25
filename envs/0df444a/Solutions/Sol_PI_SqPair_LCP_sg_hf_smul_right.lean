-- Prove2me | solution 1 for PI.SqPair.LCP.sg_hf_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:22:49.65759+00:00
-- url     : https://prove2.me/submissions/951ed2de-491b-4f19-bebb-d2bcdcec9416

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PiNonunit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_StepGlue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SqPair PI.SqPair.LCP
variable {R : Type} [CommRing R] [StarRing R] {ι : Type} [Fintype ι]
namespace PI.SqPair.LCP
theorem _root_.solution (A : Matrix ι ι R) (c : R) (x y : ι → R) :
    hf A x (c • y) = c * hf A x y := by
  simp only [hf, mulVec_smul, dotProduct_smul, smul_eq_mul]
end PI.SqPair.LCP
