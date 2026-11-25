-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.hasFDerivAt_evX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:30:42.755601+00:00
-- url     : https://prove2.me/submissions/2aff4937-e9d7-45db-84e3-b3e3c1e00864

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GWickA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_evX_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_evX_pderiv_mul_X

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
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.G
theorem _root_.solution (P : PX m n) (x : Fin m → Fin n → ℂ) : HasFDerivAt (evX P) (dEv P x) x := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h : evX (C a : PX m n) = fun _ => a := by funext y; simp [evX]
    rw [h]; refine (hasFDerivAt_const a x).congr_fderiv ?_
    simp [dEv, evX]
  | add p q hp hq =>
    have h : evX (p + q) = fun y => evX p y + evX q y := by funext y; simp [evX]
    rw [h]; refine (hp.add hq).congr_fderiv ?_
    unfold dEv; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun k _ => ?_
    rw [← add_smul]; congr 1; simp [evX]
  | mul_X p k hp =>
    have h : evX (p * X k) = fun y => evX p y * crd k y := by funext y; simp [evX_eq]
    rw [h]; refine (hp.mul (crd k).hasFDerivAt).congr_fderiv ?_
    ext v
    simp only [dEv, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      ContinuousLinearMap.coe_sum', Finset.sum_apply, smul_eq_mul, evX_pderiv_mul_X, add_mul,
      Finset.sum_add_distrib]
    have e1 : ∑ b, evX (pderiv b p) x * crd k x * crd b v = crd k x * ∑ b, evX (pderiv b p) x * crd b v := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => ?_; ring
    have e2 : ∑ b, (evX p x * if k = b then 1 else 0) * crd b v = evX p x * crd k v := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp
    rw [e1, e2]; ring
end PositivityTheory.Rg.Sw.WR.G
