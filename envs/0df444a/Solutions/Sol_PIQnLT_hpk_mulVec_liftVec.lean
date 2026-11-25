-- Prove2me | solution 1 for PIQnLT.hpk_mulVec_liftVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:18:38.192374+00:00
-- url     : https://prove2.me/submissions/8b6f7aee-6466-4cef-aa96-b740aa2d3c47

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_LzConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_SecondCapelliMinorLevel
import Theorems.Thm_PIQnLT_hpk_lev
import Theorems.Thm_PIQnLT_hpk_out_in
import Theorems.Thm_PIQnLT_lev_val
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
theorem _root_.solution (v : Fin (2 * r' + k + 1) → ℂ) :
    Hpk k (i + r') *ᵥ liftVec k i r' v = liftVec k i r' (Hpk k r' *ᵥ v) := by
  funext p
  by_cases hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i
  · obtain ⟨a, rfl⟩ : ∃ a, levPos k i r' a = p :=
      ⟨⟨p.val - i, by omega⟩, Fin.ext (by show p.val - i + i = p.val; omega)⟩
    rw [liftVec_lev]
    simp only [Matrix.mulVec, dotProduct]
    rw [sum_lev]
    · simp only [hpk_lev, liftVec_lev]
    · intro q hq
      rw [liftVec_out _ _ hq, mul_zero]
  · rw [liftVec_out _ _ hp]
    simp only [Matrix.mulVec, dotProduct]
    rw [sum_lev]
    · refine Finset.sum_eq_zero fun j _ => ?_
      have hj := j.isLt
      have hjin : i ≤ (levPos k i r' j).val ∧ (levPos k i r' j).val < 2 * r' + k + 1 + i := by rw [lev_val]; omega
      rw [hpk_out_in p (levPos k i r' j) hp hjin, zero_mul]
    · intro q hq
      rw [liftVec_out _ _ hq, mul_zero]
end PIQnLT
