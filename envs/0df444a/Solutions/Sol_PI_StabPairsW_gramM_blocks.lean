-- Prove2me | solution 1 for PI.StabPairsW.gramM_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:52:13.214747+00:00
-- url     : https://prove2.me/submissions/9ac33aeb-7ccf-4ee9-9a0d-17b2f5885c2a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConverseStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Theorems.Thm_PI_StabPairsW_herm_swap
import Theorems.Thm_PI_StabPairsW_herm_GV
import Theorems.Thm_PI_StabPairsW_herm_fvec_fvec
import Theorems.Thm_PI_StabPairsW_Adiag_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.StabPairsW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}
namespace PI.StabPairsW
theorem _root_.solution (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z') (γ : B.Mat k r)
    (hγ : γ ∈ B.GV k r) :
    gramM k r z z' γ = Matrix.fromBlocks (Adiag k r z) (Zhat k r z z' γ) (Zhat k r z z' γ)ᴴ (Adiag k r z') := by
  ext (a | a) (b | b)
  · simp only [gramM, gramVec, Matrix.fromBlocks_apply₁₁]
    rw [herm_fvec_fvec z hz, Adiag_apply]
  · simp only [gramM, gramVec, Matrix.fromBlocks_apply₁₂]
    rfl
  · simp only [gramM, gramVec, Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply]
    rw [herm_swap]
    rfl
  · simp only [gramM, gramVec, Matrix.fromBlocks_apply₂₂]
    rw [herm_GV hγ, herm_fvec_fvec z' hz', Adiag_apply]
end PI.StabPairsW
