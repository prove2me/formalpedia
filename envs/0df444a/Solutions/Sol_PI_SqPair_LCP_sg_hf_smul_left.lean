-- Prove2me | solution 1 for PI.SqPair.LCP.sg_hf_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:23:07.561305+00:00
-- url     : https://prove2.me/submissions/0ad7ebab-65e7-439f-aa98-420c8233d961

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
    hf A (c • x) y = star c * hf A x y := by
  simp only [hf, dotProduct, mulVec, Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring
end PI.SqPair.LCP
