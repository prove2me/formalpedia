-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ASSmall.exists_as_of_val_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:39:57.438329+00:00
-- url     : https://prove2.me/submissions/70f847e7-1f2a-42cf-b6a7-35ef89cd0581

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ArtSch
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SmallArtinSchreier_CoordPowEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SmallArtinSchreier_ExistsAsOfValLtOne
import Theorems.Thm_PI_UnitaryGroupMassFormula_ASSmall_coeff_zero_nilpotent
import Theorems.Thm_PI_UnitaryGroupMassFormula_ASSmall_solPerf_spec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ASSmall
open scoped NNReal
variable {K : Type*} [Field K] {v : Valuation K ℝ≥0} {O : Type*} [CommRing O] [Algebra O K]
  (hv : v.Integers O) {p : ℕ} [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
include hv
namespace PI.UnitaryGroupMassFormula.ASSmall
theorem _root_.solution (hp : 0 < v (p : K)) (e : PreTilt O p)
    (he : PreTilt.val K v O hv p e < 1) : ∃ w : PreTilt O p, w ^ p - w = e := by
  obtain ⟨N, hN⟩ := coeff_zero_nilpotent hv hp e he
  exact ⟨solPerf (R := ModP O p) (p := p) e hN, solPerf_spec (R := ModP O p) (p := p) e hN⟩
end PI.UnitaryGroupMassFormula.ASSmall
