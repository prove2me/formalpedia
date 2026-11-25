-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.wick_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:45:47.781897+00:00
-- url     : https://prove2.me/submissions/f590c8c0-fd35-4510-ac29-b5eace13f77c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_EvXPderivPhiP
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GWickC
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_amat_det_ne
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_dEv_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_dEv_wirt
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_evX_continuous
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_evX_pderiv_phiP
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_exp_phiP
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_hasFDerivAt_evX
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_norm_exp_tr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G
open PositivityTheory.Rg.Sw
namespace PositivityTheory.Rg.Sw.WR.G
theorem _root_.solution (hI : IntegP) : Wick := by
  intro m n ε c t hc b hb M a i
  have hdet := amat_det_ne ε hc t hb a
  have : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  set E : (Fin m → Fin n → ℂ) → ℂ := fun x => Complex.exp (evX (phiP ε c t b) x) with hEdef
  have hsec : ∀ P, secN ε c t P b = ∫ x, evX P x * E x := by
    intro P; unfold secN; congr 1; funext x; rw [mul_assoc, exp_phiP]
  have hint : ∀ P, Integrable (fun x => evX P x * E x) := by
    intro P
    refine (hI m n c hc P).mono ?_ ?_
    · exact ((evX_continuous P).mul (evX_continuous (phiP ε c t b)).cexp).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x => ?_
      have hx : E x = gs c x * Complex.exp (Complex.I * t * (b * gramX ε x).trace) := (exp_phiP ε c t b x).symm
      rw [hx, ← mul_assoc, norm_mul _ (Complex.exp _), norm_exp_tr ε t b hb x, mul_one]
  have hE : ∀ x, HasFDerivAt E (E x • dEv (phiP ε c t b) x) x := fun x => (hasFDerivAt_evX (phiP ε c t b) x).cexp
  have hfd : ∀ x v, fderiv ℝ E x v = E x * evX (∑ k, C (crd k v) * pderiv k (phiP ε c t b)) x := by
    intro x v; rw [(hE x).fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul, dEv_apply]
  have hPd : ∀ (P : PX m n) x v, fderiv ℝ (evX P) x v = evX (∑ k, C (crd k v) * pderiv k P) x := by
    intro P x v; rw [(hasFDerivAt_evX P x).fderiv, dEv_apply]
  have hintD : ∀ (P : PX m n) v, Integrable (fun x => evX P x * fderiv ℝ E x v) := by
    intro P v
    refine (hint (P * ∑ k, C (crd k v) * pderiv k (phiP ε c t b))).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [hfd]; simp only [evX, map_mul]; ring
  have hintM : ∀ (P : PX m n) v, Integrable (fun x => fderiv ℝ (evX P) x v * E x) := by
    intro P v; simp_rw [hPd]; exact hint _
  have ibp : ∀ (P : PX m n) (v : Fin m → Fin n → ℂ),
      ∫ x, evX P x * fderiv ℝ E x v = -∫ x, fderiv ℝ (evX P) x v * E x := by
    intro P v
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hintM P v) (hintD P v) (hint P)
      (fun x _ => (hasFDerivAt_evX P x).differentiableAt) (fun x _ => (hE x).differentiableAt)
  have ibpW : ∀ j : Fin n, ∫ x, evX M x * (E x * evX (pderiv (a, j, false) (phiP ε c t b)) x) =
      -∫ x, evX (pderiv (a, j, false) M) x * E x := by
    intro j
    have hWE : ∀ x, fderiv ℝ E x (fun a' i' => if a' = a ∧ i' = j then (1 : ℂ) else 0) -
        Complex.I * fderiv ℝ E x (fun a' i' => if a' = a ∧ i' = j then Complex.I else 0) =
        2 * (E x * evX (pderiv (a, j, false) (phiP ε c t b)) x) := by
      intro x
      rw [(hE x).fderiv, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
      have := dEv_wirt (phiP ε c t b) x a j
      linear_combination (E x) * this
    have hpt : ∀ x, evX M x * (E x * evX (pderiv (a, j, false) (phiP ε c t b)) x) =
        (evX M x * fderiv ℝ E x (fun a' i' => if a' = a ∧ i' = j then (1 : ℂ) else 0) -
          Complex.I * (evX M x * fderiv ℝ E x (fun a' i' => if a' = a ∧ i' = j then Complex.I else 0))) / 2 := by
      intro x
      rw [eq_div_iff (two_ne_zero)]
      linear_combination (-(evX M x)) * hWE x
    have hptM : ∀ x, evX (pderiv (a, j, false) M) x * E x =
        (fderiv ℝ (evX M) x (fun a' i' => if a' = a ∧ i' = j then (1 : ℂ) else 0) * E x -
          Complex.I * (fderiv ℝ (evX M) x (fun a' i' => if a' = a ∧ i' = j then Complex.I else 0) * E x)) / 2 := by
      intro x
      rw [eq_div_iff (two_ne_zero), (hasFDerivAt_evX M x).fderiv]
      have := dEv_wirt M x a j
      linear_combination (-(E x)) * this
    simp_rw [hpt, hptM]
    rw [integral_div, integral_div, integral_sub (hintD M _) ((hintD M _).const_mul _),
      integral_sub (hintM M _) ((hintM M _).const_mul _), integral_const_mul, integral_const_mul, ibp, ibp]
    ring
  have hAA : Amat ε c t b a * (Amat ε c t b a)⁻¹ = 1 := Matrix.mul_nonsing_inv (Amat ε c t b a) (isUnit_iff_ne_zero.mpr hdet)
  have key : ∀ x, evX (X (a, i, true) * M) x * E x =
      -∑ j, (Amat ε c t b a)⁻¹ j i * (evX M x * (E x * evX (pderiv (a, j, false) (phiP ε c t b)) x)) := by
    intro x
    simp only [evX_pderiv_phiP]
    have h1 : ∀ k, ∑ j, Amat ε c t b a k j * (Amat ε c t b a)⁻¹ j i = if k = i then 1 else 0 := by
      intro k; rw [← Matrix.mul_apply, hAA, Matrix.one_apply]
    have h2 : ∑ j, (Amat ε c t b a)⁻¹ j i * (evX M x * (E x * -∑ k, Amat ε c t b a k j * star (x a k))) =
        -(evX M x * E x * ∑ k, star (x a k) * ∑ j, Amat ε c t b a k j * (Amat ε c t b a)⁻¹ j i) := by
      simp only [Finset.mul_sum, mul_neg, Finset.sum_neg_distrib, neg_inj]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h2]
    simp only [h1, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, neg_neg]
    simp only [evX, map_mul, eval_X, if_true]
    ring
  rw [hsec]
  simp_rw [key]
  rw [integral_neg, integral_finset_sum]
  · simp only [integral_const_mul, ibpW, hsec]
    simp only [Finset.sum_neg_distrib, mul_neg, neg_neg]
  · intro j _
    refine Integrable.const_mul ?_ _
    refine (hint (M * pderiv (a, j, false) (phiP ε c t b))).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [evX, map_mul]; ring
end PositivityTheory.Rg.Sw.WR.G
