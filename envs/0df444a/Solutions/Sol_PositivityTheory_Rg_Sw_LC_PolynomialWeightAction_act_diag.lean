-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.PolynomialWeightAction.act_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:09:54.811868+00:00
-- url     : https://prove2.me/submissions/d0f15389-c58c-4036-825e-928015fc91ea

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_TransvectionInv
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialWeightAction_sum_ite_l
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialWeightAction_sum_ite_r
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialWeightAction_coeff_Dsrc

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.PolynomialWeightAction
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.PolynomialWeightAction
theorem _root_.solution (D : Fin n → ℂ) (hD : ∀ l, D l ≠ 0) (p : MvPolynomial (FinalTheorems m n) ℂ)
    (hp : ∀ l, Dsrc (m := m) l l p = 0) : act (Matrix.diagonal D) p = p := by
  have hinv : (Matrix.diagonal D)⁻¹ = Matrix.diagonal (fun l => (D l)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal]
    simp [mul_inv_cancel₀ (hD _)]
  let cv : FinalTheorems m n → ℂ := Sum.elim (fun x => D x.1) (fun y => (D y.1)⁻¹)
  have hgen : ∀ v, act (m := m) (Matrix.diagonal D) (X v) = C (cv v) * X v := by
    rintro (⟨l, a⟩ | ⟨l, b⟩)
    · simp only [act, aeval_X, Sum.elim_inl, Matrix.diagonal_apply]
      rw [sum_ite_l (fun _ => D l) (fun x => X (Sum.inl (x, a))) l]
      rfl
    · simp only [act, aeval_X, Sum.elim_inr, hinv, Matrix.diagonal_apply]
      rw [sum_ite_r (fun x => (D x)⁻¹) (fun x => X (Sum.inr (x, b))) l]
      rfl
  have hmono : ∀ (d : FinalTheorems m n →₀ ℕ) (r : ℂ), act (m := m) (Matrix.diagonal D) (monomial d r) =
      C (d.prod fun v k => cv v ^ k) * monomial d r := by
    intro d r
    rw [monomial_eq, map_mul, map_finsuppProd]
    simp only [map_pow, hgen, mul_pow, Finsupp.prod_mul, map_finsuppProd, map_pow]
    have hCr : act (m := m) (Matrix.diagonal D) (C r) = C r := by
      simp [act, MvPolynomial.algebraMap_eq]
    rw [hCr]
    ring
  have hw : ∀ d ∈ p.support, ∀ l, wgt l d = 0 := by
    intro d hd l
    have h := congrArg (coeff d) (hp l)
    rw [coeff_Dsrc, coeff_zero] at h
    have hc : coeff d p ≠ 0 := mem_support_iff.mp hd
    exact_mod_cast (mul_eq_zero.mp h).resolve_right hc
  have hprod : ∀ d ∈ p.support, (d.prod fun v k => cv v ^ k) = 1 := by
    intro d hd
    rw [Finsupp.prod_fintype _ _ (fun v => pow_zero _), Fintype.prod_sum_type]
    simp only [cv, Sum.elim_inl, Sum.elim_inr]
    rw [Fintype.prod_prod_type, Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun l _ => ?_
    dsimp only
    have h := hw d hd l
    simp only [wgt, sub_eq_zero] at h
    rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, inv_pow, ← div_eq_mul_inv,
      div_eq_one_iff_eq (pow_ne_zero _ (hD l))]
    congr 1
    exact_mod_cast h
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  conv_rhs => rw [p.as_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [hmono, hprod d hd, map_one, one_mul]
end PositivityTheory.Rg.Sw.LC.PolynomialWeightAction
