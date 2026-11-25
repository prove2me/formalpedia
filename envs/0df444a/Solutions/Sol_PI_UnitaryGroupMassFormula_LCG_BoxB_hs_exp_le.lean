-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.BoxB.hs_exp_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:50:29.109302+00:00
-- url     : https://prove2.me/submissions/49ea1139-2e3c-48d1-abb2-9f572b2cb2f6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_BoxBoundAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SymmetricDistance_SymDistOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeMultiplicity_EncardLeOfFinset
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_BoxBound
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_BoxB_frob_sq
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_BoxB_frob_eq
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_BoxB_norm_exp_le
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open PI.UnitaryGroupMassFormula.LCG.BoxB
variable {n : ℕ}
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedRing
  Matrix.frobeniusNormedAlgebra Matrix.frobeniusNormedSpace
namespace PI.UnitaryGroupMassFormula.LCG.BoxB
theorem _root_.solution (X : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.hs (NormedSpace.exp X) ≤ (Real.sqrt n * Real.exp (Real.sqrt (Formalism.REAL.hs X))) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [Formalism.REAL.hs]
  · rw [← frob_sq, ← frob_eq]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_exp_le hn X) 2
end PI.UnitaryGroupMassFormula.LCG.BoxB
