-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.NullS.hasFDerivAt_evX
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:45:46.423707+00:00
-- url     : https://prove2.me/submissions/eec1daa6-bd4d-4688-bc31-310993025cdf

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_HasFDerivAtEvX
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_NullS_evX_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.NullS
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.NullS
theorem _root_.solution (P : PX m n) (x : Fin m → Fin n → ℂ) : HasFDerivAt (fun y => evX P y) (dP P x) x := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have : dP (C a : PX m n) x = 0 := by simp [dP, evX_eq]
    have e : (fun y => evX (C a : PX m n) y) = fun _ => a := by funext y; simp [evX_eq]
    rw [this, e]; exact hasFDerivAt_const a x
  | add p q hp hq =>
    have : dP (p + q) x = dP p x + dP q x := by simp [dP, evX_eq, Finset.sum_add_distrib, add_smul]
    have e : (fun y => evX (p + q) y) = fun y => evX p y + evX q y := by funext y; simp [evX_eq]
    rw [this, e]; exact hp.add hq
  | mul_X p k hp =>
    have h1 : HasFDerivAt (fun y => evX p y * crd k y) (evX p x • crd k + crd k x • dP p x) x :=
      hp.mul (crd k).hasFDerivAt
    have e1 : (fun y => evX (p * X k) y) = fun y => evX p y * crd k y := by
      funext y; simp [evX_eq]
    have e2 : dP (p * X k) x = evX p x • crd k + crd k x • dP p x := by
      ext v
      have hb : ∀ b, evX (pderiv b (p * X k)) x * crd b v =
          crd k x * (evX (pderiv b p) x * crd b v) + (if k = b then evX p x * crd k v else 0) := by
        intro b
        rw [Derivation.leibniz, pderiv_X]
        by_cases h : k = b
        · subst h; simp [evX_eq]; ring
        · simp [evX_eq, Pi.single_apply, Ne.symm h, h]; ring
      simp only [dP, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum',
        Finset.sum_apply, smul_eq_mul]
      rw [Finset.sum_congr rfl fun b _ => hb b, Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos (Finset.mem_univ _),
        ← Finset.mul_sum]
      ring
    rw [e1, e2]; exact h1
end PositivityTheory.Rg.Sw.LC.NullS
