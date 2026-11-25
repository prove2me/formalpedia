-- Prove2me | solution 1 for PI.LatIdxDetW.lidx_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:50:42.174904+00:00
-- url     : https://prove2.me/submissions/c5b51873-7b2b-48f6-abab-1ad6a28b0c69

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LatIdxDet
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndexDeterminant_NegLogValuation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.DivisionValues
open scoped nonZeroDivisors
noncomputable section
open PI PI.LatIdxDetW
variable {R W W' : Type*} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']
namespace PI.LatIdxDetW
theorem _root_.solution (p : Ideal R) [p.IsPrime] (A B : Submodule R W) :
    lidx p A B = - lidx p B A := by
  unfold lidx
  rw [inf_comm B A]
  ring
end PI.LatIdxDetW
