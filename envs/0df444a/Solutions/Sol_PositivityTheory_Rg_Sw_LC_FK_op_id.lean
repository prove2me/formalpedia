-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.FK.op_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:54:35.965725+00:00
-- url     : https://prove2.me/submissions/7e81574c-a135-4dff-b155-691cc861c621

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivComm
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_FK_pderiv_comm
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_FK_cr_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_FK_qp_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.FK
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.FK
theorem _root_.solution (c : ℝ) (ε : Fin m → Bool) (i j : Fin n) (P : PX m n) :
    (∑ a ∈ Finset.univ.filter (fun a => ε a = true), cr c (a, i, false) (pderiv (a, j, true) P)) -
      ∑ a ∈ Finset.univ.filter (fun a => ε a = false), cr c (a, j, true) (pderiv (a, i, false) P) =
    ((c : ℂ) ^ 2) • mulQ ε i j P - lapS ε c i j P - (c : ℂ) • eulH c i j P + (c : ℂ) • eulA c i j P -
      (if i = j then (c : ℂ) * ∑ a, sgn ε a else 0) • P := by
  classical
  have hd : (if i = j then (c : ℂ) * ∑ a, sgn ε a else 0) • P =
      ∑ a, (if i = j then (c : ℂ) * sgn ε a else 0) • P := by
    by_cases hij : i = j <;> simp [hij, Finset.mul_sum, Finset.sum_smul]
  rw [hd, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  unfold mulQ lapS eulH eulA
  rw [qp_sum, Finset.sum_mul, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  cases hε : ε a
  · simp only [hε, Bool.false_eq_true, if_false, if_true, zero_sub, cr_apply, sw, Bool.not_true]
    rw [pderiv_comm (a, j, true) (a, i, false)]
    by_cases hij : i = j
    · subst hij
      simp [sgn, hε, pderiv_mul, pderiv_X, Pi.single_apply, smul_eq_C_mul, pderiv_C_mul, map_ofNat]
      ring
    · have hne : (a, j, false) ≠ (a, i, false) := by simp [Ne.symm hij]
      simp [sgn, hε, pderiv_mul, pderiv_X, Pi.single_apply, smul_eq_C_mul, pderiv_C_mul, hij, hne, map_ofNat]
      ring
  · simp only [hε, if_true, Bool.true_eq_false, if_false, sub_zero, cr_apply, sw, Bool.not_false]
    by_cases hij : i = j
    · subst hij
      simp [sgn, hε, pderiv_mul, pderiv_X, Pi.single_apply, smul_eq_C_mul, pderiv_C_mul, map_ofNat]
      ring
    · have hne : (a, j, false) ≠ (a, i, false) := by simp [Ne.symm hij]
      simp [sgn, hε, pderiv_mul, pderiv_X, Pi.single_apply, smul_eq_C_mul, pderiv_C_mul, hij, hne, map_ofNat]
      ring
end PositivityTheory.Rg.Sw.LC.FK
