-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_re_trace_sigTop_tail_2171dde6e7ba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:50:34.172112+00:00
-- url     : https://prove2.me/submissions/2371658a-9fbb-4fca-849e-91295fa57101

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_FlagPsLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_FlagPsDeriv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_sum_fin_split_castLE_158e19b9f679
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open Polynomial Matrix
noncomputable section
variable {N : ℕ} (p i : ℕ) (hi : i ≤ N)
namespace GroundTheory.Heights₂.Heights.FourB
theorem _root_.solution (L : Matrix (Fin N) (Fin N) ℂ) :
    (sigTop p i hi * tailForm p i hi L).trace.re = tailSum p i L := by
  rw [tailSum, sum_fin_split_castLE hi (fun b => ∑ c : Fin N,
    if b.val < i ∧ i ≤ c.val then sigSign p b * sigSign p c * ‖L c b‖ ^ 2 else 0)]
  have h2 : (∑ b : Fin N, if i ≤ b.val then (∑ c : Fin N,
      if b.val < i ∧ i ≤ c.val then sigSign p b * sigSign p c * ‖L c b‖ ^ 2 else 0) else 0) =
      0 := by
    refine Finset.sum_eq_zero fun b _ => ?_
    split_ifs with hb
    · exact Finset.sum_eq_zero fun c _ => if_neg (by omega)
    · rfl
  rw [h2, add_zero, Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.diag_apply, sigTop, tailForm, Matrix.diagonal_mul, Matrix.of_apply,
    Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have ha : (Fin.castLE hi a).val < i := by simp
  by_cases hc : i ≤ c.val
  · rw [if_pos hc, if_pos ⟨ha, hc⟩]
    have : star (L c (Fin.castLE hi a)) * ((sigSign p c : ℝ) : ℂ) * L c (Fin.castLE hi a) =
        ((sigSign p c * ‖L c (Fin.castLE hi a)‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm (star _), mul_assoc, Complex.star_def, Complex.conj_mul']
      push_cast
      ring
    rw [this, ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  · rw [if_neg hc, if_neg (fun h => hc h.2)]
    simp
end GroundTheory.Heights₂.Heights.FourB
