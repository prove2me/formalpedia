-- Prove2me | solution 1 for PI.UConjT.star_eq_self_of_im_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:32:34.243801+00:00
-- url     : https://prove2.me/submissions/f261cd75-1cea-421c-9898-a1c0ad45b4c0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryConjugation_TransferStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryConjugation_SubmatrixMemUnitaryGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UConjT
open Matrix
namespace PI.UConjT
theorem _root_.solution {z : ℂ} (h : z.im = 0) : star z = z :=
  Complex.conj_eq_iff_im.mpr h
end PI.UConjT
