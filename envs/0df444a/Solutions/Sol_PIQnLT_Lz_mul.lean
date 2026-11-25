-- Prove2me | solution 1 for PIQnLT.Lz_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:19:18.926554+00:00
-- url     : https://prove2.me/submissions/88e8dd26-8049-43b2-bd8b-5de53fceb4e1

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_LzOutRight
import Theorems.Thm_PIQnLT_sum_lev
import Theorems.Thm_PIQnLT_Lz_lev
import Theorems.Thm_PIQnLT_Lz_out_left
import Theorems.Thm_PIQnLT_Lz_out_right

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
open Formalism.REAL Formalism.QuantumDeterminants
variable {k i r' : ℕ}
variable (hL : LevHom)
include hL
namespace PIQnLT
theorem _root_.solution (X Y : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    Lz k i r' (X * Y) = Lz k i r' X * Lz k i r' Y := by
  ext p q
  by_cases hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i
  · by_cases hq : i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i
    · obtain ⟨a, rfl⟩ : ∃ a, levPos k i r' a = p :=
        ⟨⟨p.val - i, by omega⟩, Fin.ext (by show p.val - i + i = p.val; omega)⟩
      obtain ⟨b, rfl⟩ : ∃ b, levPos k i r' b = q :=
        ⟨⟨q.val - i, by omega⟩, Fin.ext (by show q.val - i + i = q.val; omega)⟩
      rw [Lz_lev, Matrix.mul_apply, Matrix.mul_apply, sum_lev]
      · simp only [Lz_lev]
      · intro m hm
        rw [Lz_out_right _ _ _ hm, zero_mul]
    · rw [Lz_out_right _ _ _ hq, Matrix.mul_apply]
      exact (Finset.sum_eq_zero fun m _ => by rw [Lz_out_right _ _ _ hq, mul_zero]).symm
  · rw [Lz_out_left _ _ _ hp, Matrix.mul_apply]
    exact (Finset.sum_eq_zero fun m _ => by rw [Lz_out_left _ _ _ hp, zero_mul]).symm
end PIQnLT
