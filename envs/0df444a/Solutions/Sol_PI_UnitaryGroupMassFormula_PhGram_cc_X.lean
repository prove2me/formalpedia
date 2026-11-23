-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhGram.cc_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:18.117744+00:00
-- url     : https://prove2.me/submissions/00a4c00a-d6e5-4469-88cd-d7864c5731d3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_IntegralSubst
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditiveCubes_ConstantCoeffLogEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_HasSubstGood

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhGram
open PI.FglGram
variable {p : ℕ} [Fact p.Prime]
namespace PI.UnitaryGroupMassFormula.PhGram
theorem _root_.solution {σ : Type*} (i : σ) : MvPowerSeries.constantCoeff (Xv (p := p) i) = 0 := by
  first
  | exact MvPowerSeries.constantCoeff_X i
  | simp
end PI.UnitaryGroupMassFormula.PhGram
