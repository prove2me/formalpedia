-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.ChooseW.rank_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:41:13.479839+00:00
-- url     : https://prove2.me/submissions/43c5e1b1-fefa-411f-8451-ca0c56f6a5d3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatticeIsometry
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_Choose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open PI.UnitaryGroupMassFormula.LCG.ChooseW
variable {K : Type*} [Field K] {n : ℕ}
namespace PI.UnitaryGroupMassFormula.LCG.ChooseW
theorem _root_.solution (δ : Matrix (Fin n) (Fin n) K) (hδ : δ ≠ 0) : 1 ≤ δ.rank := by
  by_contra h
  have h0 : δ.rank = 0 := by omega
  have hbot : LinearMap.range δ.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h0
  have hz : Matrix.toLin' δ = 0 := by
    rw [Matrix.toLin'_apply']
    exact LinearMap.range_eq_bot.mp hbot
  exact hδ (Matrix.toLin'.injective (by rw [hz, map_zero]))
end PI.UnitaryGroupMassFormula.LCG.ChooseW
