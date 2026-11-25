-- Prove2me | solution 1 for PI.StabBigW.dd_tau
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:26:21.211006+00:00
-- url     : https://prove2.me/submissions/d6de5da9-b041-4f8a-8e76-b3cd85973cf5

import Definitions.Def_Formalism_PeriodIntegrals_StabBig
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LargeStabilizerInverse_GLeftInv
import Theorems.Thm_PI_StabBigW_tau_val

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
open PI PI.StabBigW
open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
variable {k r : ℕ}
namespace PI.StabBigW
theorem _root_.solution {c : Fin r → ℂ} (hc : ∀ a, c a ≠ 0) (j : Fin (2 * r + k + 1))
    (hj : j.val < r ∨ r + k < j.val) :
    dd k r (fun a => star (c a)) (tau k r j) * dd k r c j = 1 := by
  have hjl := j.isLt
  have ht := tau_val (k := k) (r := r) j
  rw [if_pos hj] at ht
  rcases hj with h | h
  · have h1 : ¬ (tau k r j).val < r := by omega
    have h2 : r + k < (tau k r j).val := by omega
    have e : (⟨2 * r + k - (tau k r j).val, by omega⟩ : Fin r) = ⟨j.val, h⟩ :=
      Fin.ext (by show 2 * r + k - (tau k r j).val = j.val; omega)
    simp only [dd, dif_neg h1, dif_pos h2, dif_pos h, e, star_star]
    exact inv_mul_cancel₀ (hc _)
  · have h1 : (tau k r j).val < r := by omega
    have h0 : ¬ j.val < r := by omega
    have e : (⟨(tau k r j).val, h1⟩ : Fin r) = ⟨2 * r + k - j.val, by omega⟩ :=
      Fin.ext (by show (tau k r j).val = 2 * r + k - j.val; omega)
    simp only [dd, dif_pos h1, dif_neg h0, dif_pos h, e]
    exact mul_inv_cancel₀ (star_ne_zero.mpr (hc _))
end PI.StabBigW
