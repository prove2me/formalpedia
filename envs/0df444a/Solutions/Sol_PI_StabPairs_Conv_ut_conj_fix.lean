-- Prove2me | solution 1 for PI.StabPairs.Conv.ut_conj_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:30:59.717361+00:00
-- url     : https://prove2.me/submissions/66b52ea4-5fc2-4934-9197-c65c4b94d0f0

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
    (v : Fin (r + 1) → ℂ) (hv : ∀ a : Fin (r + 1), a.val < r → v a = 0) : uᴴ *ᵥ v = v := by
  ext a
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [ut_last hu]
    by_cases ha : a = Fin.last r
    · subst ha; simp
    · simp only [ha, if_false, star_zero, zero_mul]
      exact (hv a (lt_of_le_of_ne (Nat.lt_succ_iff.mp a.isLt) (fun e => ha (Fin.ext e)))).symm
  · intro b _ hb
    rw [hv b (lt_of_le_of_ne (Nat.lt_succ_iff.mp b.isLt) (fun e => hb (Fin.ext e))), mul_zero]
  · simp
end PI.StabPairs.Conv
