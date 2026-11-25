-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.dEv_wirt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:20:56.28135+00:00
-- url     : https://prove2.me/submissions/0aeb11f6-e875-4da2-8eef-e71bf5227785

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GWickB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_EvXPderivPhiP
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_crd_wirt

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
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.G
theorem _root_.solution (P : PX m n) (x : Fin m → Fin n → ℂ) (a : Fin m) (j : Fin n) :
    dEv P x (fun a' i' => if a' = a ∧ i' = j then (1 : ℂ) else 0) -
      Complex.I * dEv P x (fun a' i' => if a' = a ∧ i' = j then Complex.I else 0) =
      2 * evX (pderiv (a, j, false) P) x := by
  simp only [dEv, ContinuousLinearMap.coe_sum', ContinuousLinearMap.coe_smul', Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single (a, j, false)]
  · have := crd_wirt a j (a, j, false); simp only [if_true] at this
    rw [← this]; ring
  · intro k _ hk
    have := crd_wirt a j k; rw [if_neg hk] at this
    calc _ = evX (pderiv k P) x * (crd k (fun a' i' => if a' = a ∧ i' = j then (1 : ℂ) else 0) -
          Complex.I * crd k (fun a' i' => if a' = a ∧ i' = j then Complex.I else 0)) := by ring
      _ = 0 := by rw [this, mul_zero]
  · simp
end PositivityTheory.Rg.Sw.WR.G
