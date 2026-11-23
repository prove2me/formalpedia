-- Prove2me | solution 1 for PI.LocDualGen.FpU.repr_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:31.770227+00:00
-- url     : https://prove2.me/submissions/260f330a-9e9e-4d25-9acc-d9212d1a64ea

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDualUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_IsClosedO

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel IsLocalRing
open PI PI.LocDualGen PI.LocDualGen.FpU
variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (l : ℕ) [Fact l.Prime] [Algebra ℚ_[l] K]
namespace PI.LocDualGen.FpU
theorem _root_.solution {ι R M : Type*} [Fintype ι] [CommRing R] [AddCommGroup M] [Module R M]
    (b : Module.Basis ι R M) (c : ι → R) (i : ι) : b.repr (∑ j, c j • b j) i = c i := by
  exact congrFun (b.repr_sum_self c) i
end PI.LocDualGen.FpU
