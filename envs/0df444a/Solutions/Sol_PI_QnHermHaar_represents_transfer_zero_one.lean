-- Prove2me | solution 1 for PI.QnHermHaar.represents_transfer_zero_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:31:55.173425+00:00
-- url     : https://prove2.me/submissions/4031077b-5894-4300-95e6-64e7206efbe4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_RepOnOfEq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_RepresentsTransferOneOne
import Theorems.Thm_PI_QnHermHaar_repQminor
import Theorems.Thm_PI_QnHermHaar_Gen_repOn_mul
import Theorems.Thm_PI_QnHermHaar_Gen_repOn_neg
import Theorems.Thm_PI_QnHermHaar_Gen_repOn_smul
import Theorems.Thm_PI_QnHermHaar_Gen_repOn_sum
import Theorems.Thm_PI_QnHermHaar_repOn_of_eq
import Theorems.Thm_PI_QnHermHaar_repYb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory
open scoped ContDiff
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Gen
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {i : Fin (r + 1)} {μ : Measure (Mt k r)}
namespace PI.QnHermHaar
theorem _root_.solution (H : Hyp k r z z' i μ) (Y : ℂ) :
    RepOn (hI H) (tA (EA H) (YA H) (YbA H) (xv k r z' i) (xbv k r z' i) (uC k r i Y) 0 1)
      (tL k r z z' i Y 0 1) := by
  have h := repOn_neg (hI H) (repOn_sum (hI H) (Finset.univ : Finset (Fin (mdim k r i))) fun a _ => repOn_sum (hI H) (Finset.univ : Finset (Fin (mdim k r i))) fun b _ =>
    repOn_smul (hI H) ((-1 : ℂ) ^ ((a : ℕ) + (b : ℕ)) * xv k r z' i b)
      (repOn_mul (hI H) (repYb H a) (repQminor H (skip1 a) (skip1 b) (uC k r i Y - 1))))
  refine repOn_of_eq h fun f => ?_
  funext g
  simp only [tL, chatL, MOp, Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  ring
end PI.QnHermHaar
