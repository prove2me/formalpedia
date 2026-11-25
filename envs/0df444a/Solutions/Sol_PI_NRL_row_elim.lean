-- Prove2me | solution 1 for PI.NRL.row_elim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:05:41.673746+00:00
-- url     : https://prove2.me/submissions/2292053c-4820-4606-b4b9-f0efb21bbc67

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormRepresentationLift_ExistsMulEqOneAddSmulOfRowsGe
import Theorems.Thm_PI_NRL_exists_mul_eq_one_add_smul_of_rows_ge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.NRL
open Matrix
variable {R : Type*} [CommRing R] {r : ℕ}
namespace PI.NRL
theorem _root_.solution (g : R) (P : Matrix (Fin (r + 1)) (Fin (r + 1)) R → Prop)
    (h1 : P 1) (hmul : ∀ M N, P M → P N → P (M * N))
    (hrow : ∀ a : Fin (r + 1), a.val < r → ∀ t : Fin (r + 1) → R, ∃ w : Fin (r + 1) → R,
      (∀ c, c ≤ a → w c = 0) ∧ (∀ c, a < c → ∃ q, w c = t c + g * q) ∧ P (1 + rowMat a w))
    (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (hξ : UniUp ξ) :
    ∃ M, P M ∧ ∃ Q, M * ξ = 1 + g • Q := by
  refine exists_mul_eq_one_add_smul_of_rows_ge g P h1 hmul hrow r le_rfl ξ hξ fun d c hd => ?_
  have hdl : d = Fin.last r := Fin.ext (by have := d.isLt; simp only [Fin.val_last]; omega)
  subst hdl
  split_ifs with hc
  · subst hc
    exact hξ.2 _
  · exact hξ.1 _ _ (lt_of_le_of_ne (Fin.le_last c) (fun h' => hc h'.symm))
end PI.NRL
