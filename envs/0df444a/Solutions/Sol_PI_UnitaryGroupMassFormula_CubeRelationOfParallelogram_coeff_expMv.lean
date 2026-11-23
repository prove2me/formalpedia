-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.coeff_expMv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:32.122635+00:00
-- url     : https://prove2.me/submissions/8362cd74-a3b1-4ae1-a081-a60b87309fc9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_CoeffPowMulPowEqZero

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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
open PI.FglGram MvPowerSeries
variable {p : ℕ} [Fact p.Prime] {σ : Type*}
namespace PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
theorem _root_.solution (F : MvPowerSeries σ ℂ_[p]) (α : σ →₀ ℕ) :
    coeff α (expMv F) =
      ∑ n ∈ Finset.range (α.degree + 1), coeff α (F ^ n) / (n.factorial : ℂ_[p]) := rfl
end PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
