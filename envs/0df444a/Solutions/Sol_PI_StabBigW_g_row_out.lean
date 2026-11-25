-- Prove2me | solution 1 for PI.StabBigW.g_row_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:26:26.66303+00:00
-- url     : https://prove2.me/submissions/2a8b1852-3ada-482a-82f6-8019cf313079

import Definitions.Def_Formalism_PeriodIntegrals_StabBig
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LargeStabilizerInverse_GLeftInv
import Theorems.Thm_PI_StabBigW_tau_val
import Theorems.Thm_PI_StabBigW_g_col_out
import Theorems.Thm_PI_StabBigW_g_mid_col
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
noncomputable section
namespace PI.StabBigW
open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
variable {k r : ℕ}
private theorem tau_tau_lemma (i : Fin (2 * r + k + 1)) : tau k r (tau k r i) = i := by
  have h1 := tau_val (k := k) (r := r) i
  have h2 := tau_val (k := k) (r := r) (tau k r i)
  have hi := i.isLt
  ext
  by_cases hc : i.val < r ∨ r + k < i.val
  · rw [if_pos hc] at h1
    have hc2 : (tau k r i).val < r ∨ r + k < (tau k r i).val := by omega
    rw [if_pos hc2] at h2
    omega
  · rw [if_neg hc] at h1
    have hc2 : ¬ ((tau k r i).val < r ∨ r + k < (tau k r i).val) := by omega
    rw [if_neg hc2] at h2
    omega
end PI.StabBigW
end
end

set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.StabBigW
open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
variable {k r : ℕ}
namespace PI.StabBigW
theorem _root_.solution (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (i m : Fin (2 * r + k + 1)) (hi : i.val < r ∨ r + k < i.val) :
    bigCell k r c μ i m = if m = tau k r i then dd k r c (tau k r i) else 0 := by
  have hil := i.isLt
  have hml := m.isLt
  have hti := tau_val (k := k) (r := r) i
  rw [if_pos hi] at hti
  by_cases hm : m.val < r ∨ r + k < m.val
  · rw [g_col_out c μ i m hm]
    by_cases h : m = tau k r i
    · have h' : i = tau k r m := by rw [h, tau_tau_lemma]
      rw [if_pos h', if_pos h, h]
    · have h' : ¬ i = tau k r m := fun h'' => h (by rw [h'', tau_tau_lemma])
      rw [if_neg h', if_neg h]
  · have hne : ¬ m = tau k r i := fun h => by have := congrArg Fin.val h; omega
    rw [if_neg hne]
    exact g_mid_col c μ i m (by omega) (by omega) hi
end PI.StabBigW
