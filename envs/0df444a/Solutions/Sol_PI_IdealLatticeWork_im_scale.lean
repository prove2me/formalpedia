-- Prove2me | solution 1 for PI.IdealLatticeWork.im_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:42:38.204129+00:00
-- url     : https://prove2.me/submissions/b2896db1-829e-4c46-993b-b2424866556c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IdealLattice
import Definitions.Def_Formalism_PeriodIntegrals_AreaLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdealLatticeBasis_IdealBasisAlt
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_AreaLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdealLatticeBasis_Assemble

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open PI PI.IdealLatticeWork
namespace PI.IdealLatticeWork
theorem _root_.solution (δ x y : ℂ) :
    ((starRingEnd ℂ) (δ * x) * (δ * y)).im = ‖δ‖ ^ 2 * ((starRingEnd ℂ) x * y).im := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [map_mul, Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring
end PI.IdealLatticeWork
