-- Prove2me | solution 1 for PI.StabBigW.adj_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:26:58.06959+00:00
-- url     : https://prove2.me/submissions/b30e1f30-35ef-468d-a7b7-ad81cc47ee90

import Definitions.Def_Formalism_PeriodIntegrals_StabBig
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LargeStabilizerInverse_GLeftInv
import Theorems.Thm_PI_StabBigW_tau_val
import Theorems.Thm_PI_StabBigW_hpk_col
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
private theorem sgn_tau' (i : Fin (2 * r + k + 1)) : sgn k r (tau k r i) = sgn k r i := by
  have h1 := tau_val (k := k) (r := r) i
  have hi := i.isLt
  unfold sgn
  by_cases hc : i.val < r ∨ r + k < i.val
  · rw [if_pos hc] at h1
    rw [if_neg (by omega : ¬ (tau k r i).val = r + k), if_neg (by omega : ¬ i.val = r + k)]
  · rw [if_neg hc] at h1
    rw [h1]
private theorem Hpk_apply_eq_ite_tau (p m : Fin (2 * r + k + 1)) :
    Hpk k r p m = if m = tau k r p then sgn k r p else 0 := by
  rw [hpk_col]
  by_cases h : m = tau k r p
  · have h2 : p = tau k r m := by rw [h, tau_tau_lemma]
    rw [if_pos h2, if_pos h, h, sgn_tau']
  · have h2 : ¬ p = tau k r m := fun h' => h (by rw [h', tau_tau_lemma])
    rw [if_neg h2, if_neg h]
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
theorem _root_.solution (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (p q : Fin (2 * r + k + 1)) :
    (Hpk k r * aᴴ * Hpk k r) p q = sgn k r p * sgn k r q * star (a (tau k r q) (tau k r p)) := by
  have e1 : ∀ m, Hpk k r m q = if m = tau k r q then sgn k r q else 0 := fun m => hpk_col m q
  have e2 : ∀ m, Hpk k r p m = if m = tau k r p then sgn k r p else 0 := fun m => Hpk_apply_eq_ite_tau p m
  rw [Matrix.mul_apply]
  simp only [e1, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [Matrix.mul_apply]
  simp only [e2, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    Matrix.conjTranspose_apply]
  ring
end PI.StabBigW
