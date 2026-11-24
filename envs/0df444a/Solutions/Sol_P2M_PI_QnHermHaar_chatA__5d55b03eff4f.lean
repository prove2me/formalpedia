-- Prove2me | solution 1 for P2M_PI_QnHermHaar_chatA__5d55b03eff4f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:11:05.949048+00:00
-- url     : https://prove2.me/submissions/6983f838-7604-4867-be3b-1549b7c7326f

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
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (w : ℂ) (a : Fin m → ℂ)
    (l : Fin m) : chatA E w a (Pi.single l 1) =
      ∑ j : Fin m, ((-1 : ℂ) ^ ((l : ℕ) + (j : ℕ)) * a j) • qminor E (skip1 l) (skip1 j) w := by
  simp only [chatA]
  rw [Finset.sum_eq_single l (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
  simp
end PI.QnHermHaar
