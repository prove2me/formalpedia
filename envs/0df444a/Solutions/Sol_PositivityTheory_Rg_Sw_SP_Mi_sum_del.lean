-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.Mi.sum_del
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:05:06.851799+00:00
-- url     : https://prove2.me/submissions/09add062-c025-44ad-b4c5-50ba2b623806

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorCoreA
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_Mi_deriv_det


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP PositivityTheory.Rg.Sw.SP.Mi
variable {R : Type} [CommRing R]
namespace PositivityTheory.Rg.Sw.SP.Mi
theorem _root_.solution (ρ : ℕ) :
    ∑ j : Fin (ρ + 1), (-1 : Pm R (ρ + 1)) ^ (j : ℕ) * del 0 j ((Xm R (ρ + 1)).submatrix j.succAbove Fin.succ).det =
      -((ρ : Pm R (ρ + 1)) * (Xm R (ρ + 1)).det) := by
  have h1 : ∀ j : Fin (ρ + 1), del 0 j ((Xm R (ρ + 1)).submatrix j.succAbove Fin.succ).det =
      ∑ c : Fin ρ, X (j, c.succ) * (updateCol ((Xm R (ρ + 1)).submatrix j.succAbove Fin.succ) c
        (fun a => X (j.succAbove a, 0))).det := by
    intro j
    rw [deriv_det]
    refine Finset.sum_congr rfl fun c _ => ?_
    have : (fun a => del 0 j (((Xm R (ρ + 1)).submatrix j.succAbove Fin.succ) a c)) =
        (X (j, c.succ) : Pm R (ρ + 1)) • (fun a => (X (j.succAbove a, 0) : Pm R (ρ + 1))) := by
      funext a
      simp [Xm, del, mkDerivation_X, mul_comm]
    rw [this, det_updateCol_smul]
  have h2 : ∀ c : Fin ρ, ∑ j : Fin (ρ + 1), (-1 : Pm R (ρ + 1)) ^ (j : ℕ) * (X (j, c.succ) *
      (updateCol ((Xm R (ρ + 1)).submatrix j.succAbove Fin.succ) c (fun a => X (j.succAbove a, 0))).det) =
      -(Xm R (ρ + 1)).det := by
    intro c
    have hB := det_succ_column_zero ((Xm R (ρ + 1)).submatrix id (Equiv.swap 0 c.succ))
    rw [det_permute', Equiv.Perm.sign_swap (Fin.succ_ne_zero c).symm] at hB
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul] at hB
    rw [hB]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc]
    congr 2
    ext p q
    by_cases h : q = c
    · subst h; simp [Xm, updateCol_apply, Equiv.swap_apply_right]
    · have h3 : q.succ ≠ 0 := Fin.succ_ne_zero q
      have h4 : q.succ ≠ c.succ := fun e => h (Fin.succ_injective _ e)
      simp [Xm, updateCol_apply, h, Equiv.swap_apply_of_ne_of_ne h3 h4]
  simp_rw [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [h2]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
end PositivityTheory.Rg.Sw.SP.Mi
