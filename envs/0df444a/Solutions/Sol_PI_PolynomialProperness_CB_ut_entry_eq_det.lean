-- Prove2me | solution 1 for PI.PolynomialProperness.CB.ut_entry_eq_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:21:58.823389+00:00
-- url     : https://prove2.me/submissions/2d2dfbd1-e9f4-494e-b169-8a94b7f44a2a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_NsqMulVecLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_SecondOrderNormBound
import Theorems.Thm_PI_PolynomialProperness_CB_sum_castLE
import Theorems.Thm_PI_PolynomialProperness_CB_rws_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.CB
namespace PI.PolynomialProperness.CB
theorem _root_.solution {m : ℕ} {L U : Matrix (Fin m) (Fin m) ℂ} (hL : L ∈ LTset m)
    (hU : U ∈ UTset m) (i j : Fin m) : U i j = ((L * U).submatrix (rws i) (cls i j)).det := by
  have hfac : (L * U).submatrix (rws i) (cls i j) =
      L.submatrix (rws i) (rws i) * U.submatrix (rws i) (cls i j) := by
    ext a b
    simp only [submatrix_apply, mul_apply]
    refine sum_castLE (Nat.succ_le_of_lt i.isLt) _ fun l hl => ?_
    have h0 : L (rws i a) l = 0 := hL.1 _ _ (by rw [Fin.lt_def, rws_val]; omega)
    rw [h0, zero_mul]
  have hlo : (L.submatrix (rws i) (rws i)).IsLowerTriangular := by
    intro a b hab
    have hab' : a < b := hab
    exact hL.1 _ _ hab'
  have hup : (U.submatrix (rws i) (cls i j)).IsUpperTriangular := by
    intro a b hab
    have hab' : b < a := hab
    have hb : b.val < i.val := by
      have := a.isLt; rw [Fin.lt_def] at hab'; omega
    show U (rws i a) (cls i j b) = 0
    simp only [cls, if_pos hb]
    exact hU.1 _ _ hab'
  rw [hfac, det_mul, det_of_isLowerTriangular _ hlo]
  have hl1 : ∀ t : Fin (i.val + 1), L.submatrix (rws i) (rws i) t t = 1 := fun t => hL.2 _
  have hcs : ∀ t : Fin i.val, U.submatrix (rws i) (cls i j) t.castSucc t.castSucc = 1 := by
    intro t
    have h2 : cls i j t.castSucc = rws i t.castSucc := by
      have ht : (t.castSucc : Fin (i.val + 1)).val < i.val := t.isLt
      simp only [cls, if_pos ht]; rfl
    show U (rws i t.castSucc) (cls i j t.castSucc) = 1
    rw [h2]; exact hU.2 _
  have hlast1 : rws i (Fin.last i.val) = i := Fin.ext rfl
  have hlast2 : cls i j (Fin.last i.val) = j := by
    simp only [cls, Fin.val_last, lt_irrefl, if_false]
  rw [Finset.prod_eq_one (fun t _ => hl1 t), one_mul, det_of_isUpperTriangular hup,
    Fin.prod_univ_castSucc, Finset.prod_eq_one (fun t _ => hcs t), one_mul]
  show U i j = U (rws i (Fin.last i.val)) (cls i j (Fin.last i.val))
  rw [hlast1, hlast2]
end PI.PolynomialProperness.CB
