-- Prove2me | solution 1 for PI.QnHermHaar.sumSingle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:09:51.918147+00:00
-- url     : https://prove2.me/submissions/dfe82ac7-1e09-4b3f-a3dd-78ee0f66f9ac

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_SumFourCommVersion
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_GeneralSecondMinorExpansion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.FourierDecayAlt.Q
namespace PI.QnHermHaar
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (W : Fin m → A) (c : Fin m → ℂ) (i i' : Fin m) :
    W i * algebraMap ℂ A (c i') - W i' * algebraMap ℂ A (c i) =
      ∑ l, ((Pi.single l (1 : ℂ) : Fin m → ℂ) i * c i' - (Pi.single l (1 : ℂ) : Fin m → ℂ) i' * c i) • W l := by
  simp [Pi.single_apply, sub_smul, Finset.sum_sub_distrib, ite_smul]
  simp only [Algebra.smul_def, Algebra.commutes]
end PI.QnHermHaar
