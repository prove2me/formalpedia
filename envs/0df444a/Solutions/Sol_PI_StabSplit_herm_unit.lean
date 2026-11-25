-- Prove2me | solution 1 for PI.StabSplit.herm_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:37:55.149444+00:00
-- url     : https://prove2.me/submissions/4605c94f-e3c3-40cd-a598-0fe86b18fae0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_SubFlag
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_PrjMulVecOfL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_UnitR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_MulVecColOfMul
import Theorems.Thm_PI_StabSplit_GV_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.StabSplit
namespace PI.StabSplit
theorem _root_.solution (k r : ℕ) {g : B.Mat k r} (hg : g ∈ B.GV k r) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (g *ᵥ x) (g *ᵥ y) = herm (Hpk k r) x y := by
  unfold herm
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  rw [GV_eq k r hg]
end PI.StabSplit
