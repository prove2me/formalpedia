-- Prove2me | solution 1 for PI.IdealLatticeWork.okBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:43:03.305715+00:00
-- url     : https://prove2.me/submissions/9432136b-346c-446f-a513-2ab8e9d1de57

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
theorem _root_.solution : OKBasis := by
  intro K _ _ h
  exact ⟨Module.finBasisOfFinrankEq ℤ (𝓞 K) (by rw [NumberField.RingOfIntegers.rank, h])⟩
end PI.IdealLatticeWork
