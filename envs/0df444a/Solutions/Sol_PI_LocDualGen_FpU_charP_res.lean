-- Prove2me | solution 1 for PI.LocDualGen.FpU.charP_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:56:33.390095+00:00
-- url     : https://prove2.me/submissions/3044716d-2814-481c-ab9c-ba3544469862

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
theorem _root_.solution (huni : Irreducible ((l : ℕ) : 𝒪[K])) : CharP 𝓀[K] l := by
  rw [CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime), ← map_natCast (residue 𝒪[K]) l,
    IsLocalRing.residue_eq_zero_iff]
  exact (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 huni.not_isUnit)
end PI.LocDualGen.FpU
