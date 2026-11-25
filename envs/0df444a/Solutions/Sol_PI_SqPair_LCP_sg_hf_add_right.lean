-- Prove2me | solution 1 for PI.SqPair.LCP.sg_hf_add_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:23:03.085855+00:00
-- url     : https://prove2.me/submissions/fb140ca9-8d24-462c-9f1e-d1653fadc1f0

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
theorem _root_.solution (A : Matrix ι ι R) (x y y' : ι → R) :
    hf A x (y + y') = hf A x y + hf A x y' := by
  simp only [hf, mulVec_add, dotProduct_add]
end PI.SqPair.LCP
