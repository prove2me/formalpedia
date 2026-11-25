-- Prove2me | solution 1 for PI.StabPairs.Conv.ut_sub_one_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:42:04.368428+00:00
-- url     : https://prove2.me/submissions/51019d9b-0280-4555-be40-996e3fef648a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConverseStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConvAlg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_UtSubOneLast
import Theorems.Thm_PI_StabPairs_Conv_ut_last

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
open PI PI.StabPairs PI.StabPairs.Conv
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 PI.StabPairsW
namespace PI.StabPairs.Conv
theorem _root_.solution {r : ℕ} {u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hu : u ∈ UTset (r + 1))
    (x : Fin (r + 1) → ℂ) : ((u - 1) *ᵥ x) (Fin.last r) = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Matrix.sub_apply, ut_last hu, Matrix.one_apply]
  by_cases h : j = Fin.last r
  · subst h; simp
  · simp [h, Ne.symm h]
end PI.StabPairs.Conv
