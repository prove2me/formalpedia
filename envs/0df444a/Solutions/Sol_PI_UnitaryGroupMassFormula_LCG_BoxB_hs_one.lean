-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.BoxB.hs_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:40:53.656414+00:00
-- url     : https://prove2.me/submissions/f232bcd9-87c1-4266-9f5c-38e1f24eb55e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_BoxBoundAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SymmetricDistance_SymDistOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeMultiplicity_EncardLeOfFinset
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_BoxBound
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
theorem _root_.solution : Formalism.REAL.hs (1 : Matrix (Fin n) (Fin n) ℂ) = n := by
  unfold Formalism.REAL.hs
  have h1 : ∀ i : Fin n, ∑ j, ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 = 1 := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Matrix.one_apply_ne (Ne.symm hj)]
    · intro h
      exact absurd (Finset.mem_univ i) h
  simp [h1]
end PI.UnitaryGroupMassFormula.LCG.BoxB
