-- Prove2me | solution 1 for PI.QnHermHaar.chatAa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:11:07.110573+00:00
-- url     : https://prove2.me/submissions/4c6e5154-5550-4420-aae6-a4500c6f5b6c

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
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (w : ℂ) (β : Fin m → ℂ)
    (p : Fin m) : chatA E w (Pi.single p 1) β =
      ∑ i : Fin m, ((-1 : ℂ) ^ ((i : ℕ) + (p : ℕ)) * β i) • qminor E (skip1 i) (skip1 p) w := by
  simp only [chatA]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single p (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
  simp
end PI.QnHermHaar
