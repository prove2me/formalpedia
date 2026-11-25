-- Prove2me | solution 1 for PI.StabSplit.mem_U_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:38:24.181401+00:00
-- url     : https://prove2.me/submissions/c67ff3e9-e916-4722-9e24-34e59236b52b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_SubFlag
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_PrjMulVecOfL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_UnitR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_MulVecColOfMul

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
theorem _root_.solution (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (v) :
    v ∈ Uperp k r z z' γ ↔ ((Ym k r z z' γ)ᴴ * Hpk k r) *ᵥ v = 0 := by
  have : (Matrix.of fun i j => star (gramVec k r z z' γ i j)) = (Ym k r z z' γ)ᴴ := by
    ext i j; simp [Ym, conjTranspose_apply]
  rw [Uperp, LinearMap.mem_ker, Matrix.mulVecLin_apply, this]
end PI.StabSplit
