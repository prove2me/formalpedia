-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ASSmall.tiltSmall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:46:08.020231+00:00
-- url     : https://prove2.me/submissions/af78ed5c-cb67-401f-8790-e733db6c5744

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ArtSch
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SmallArtinSchreier_CoordPowEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SmallArtinSchreier_ExistsAsOfValLtOne
import Theorems.Thm_PI_UnitaryGroupMassFormula_ASSmall_exists_as_of_val_lt_one

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
namespace PI.UnitaryGroupMassFormula.ASSmall
theorem _root_.solution : PI.ArtSch.TiltSmall := by
  intro l _ e he
  have hp : 0 < (PadicComplex.valued l).v ((l : ℕ) : PadicComplex l) := by
    rw [PadicComplex.valuation_p l]
    have : (0 : ℝ≥0) < (l : ℝ≥0) := by exact_mod_cast (Fact.out : l.Prime).pos
    positivity
  exact exists_as_of_val_lt_one (PadicComplexInt.integers l) hp e he
end PI.UnitaryGroupMassFormula.ASSmall
