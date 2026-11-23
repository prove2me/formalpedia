-- Prove2me | solution 1 for PI.StabBigW.g_col_out
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:58:09.15149+00:00
-- url     : https://prove2.me/submissions/3939ec4d-2952-47cb-9466-6c114d1258df

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
theorem _root_.solution (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (i j : Fin (2 * r + k + 1)) (hj : j.val < r ∨ r + k < j.val) :
    bigCell k r c μ i j = if i = tau k r j then dd k r c j else 0 := by
  have hjl := j.isLt
  have ht := tau_val (k := k) (r := r) j
  rw [if_pos hj] at ht
  rcases hj with h | h
  · have e : esI k r ⟨j.val, h⟩ = tau k r j := Fin.ext (by rw [ht]; rfl)
    simp only [bigCell, dd, dif_pos h, e]
  · have h0 : ¬ j.val < r := by omega
    have h2 : ¬ j.val ≤ r + k := by omega
    simp only [bigCell, dd, dif_neg h0, dif_neg h2, dif_pos h]
    by_cases hi : i = tau k r j
    · have hv : i.val = 2 * r + k - j.val := by rw [hi, ht]
      rw [if_pos hv, if_pos hi]
    · have hv : ¬ i.val = 2 * r + k - j.val := fun h' => hi (Fin.ext (by rw [h', ht]))
      rw [if_neg hv, if_neg hi]
end PI.StabBigW
