-- Prove2me | solution 1 for PIQnLT.mulVec_liftVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:55:43.640552+00:00
-- url     : https://prove2.me/submissions/8676afed-8460-4c9c-9b9c-aaf59bfecc2e

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_LzConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_SecondCapelliMinorLevel
import Theorems.Thm_P2M_PIQnLT__Lev_lev_250764e1f733
import Theorems.Thm_P2M_PIQnLT__Lev_out_d130fdfe3a24
import Theorems.Thm_PIQnLT_liftVec_lev
import Theorems.Thm_PIQnLT_liftVec_out
import Theorems.Thm_PIQnLT_sum_lev


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
open PIQnLT
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k i r' : ℕ}
namespace PIQnLT
theorem _root_.solution (M : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (v : Fin (2 * r' + k + 1) → ℂ) :
    ιLev k i r' M *ᵥ liftVec k i r' v = liftVec k i r' (M *ᵥ v) := by
  funext p
  by_cases hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i
  · obtain ⟨a, rfl⟩ : ∃ a, levPos k i r' a = p :=
      ⟨⟨p.val - i, by omega⟩, Fin.ext (by show p.val - i + i = p.val; omega)⟩
    rw [liftVec_lev]
    simp only [Matrix.mulVec, dotProduct]
    rw [sum_lev]
    · simp only [ιLev_lev, liftVec_lev]
    · intro q hq
      rw [liftVec_out _ _ hq, mul_zero]
  · rw [liftVec_out _ _ hp]
    simp only [Matrix.mulVec, dotProduct, ιLev_out M p _ hp, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    exact liftVec_out _ _ hp
end PIQnLT
