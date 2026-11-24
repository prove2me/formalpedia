-- Prove2me | solution 1 for PI.FrameInd.CountsW.re_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:19:16.661336+00:00
-- url     : https://prove2.me/submissions/35b08e8a-a83c-4edd-8aa9-37b8b17df6f5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_NonposCount
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_Counts
import Theorems.Thm_PI_FrameInd_CountsW_diag_eq
import Theorems.Thm_PI_FrameInd_herm_mulVec_mulVec


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
open PI PI.FrameInd PI.FrameInd.CountsW
open PI.FrameInd
namespace PI.FrameInd.CountsW
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (w : n → ℂ) :
    (herm A ((hA.eigenvectorUnitary : Matrix n n ℂ) *ᵥ w) ((hA.eigenvectorUnitary : Matrix n n ℂ) *ᵥ w)).re =
      ∑ i, hA.eigenvalues i * Complex.normSq (w i) := by
  rw [herm_mulVec_mulVec, diag_eq, herm, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [mulVec_diagonal, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring
end PI.FrameInd.CountsW
