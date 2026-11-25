-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.evX_pderiv_phiP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:51:41.345272+00:00
-- url     : https://prove2.me/submissions/0ee9679a-b3a9-46d9-accc-957014938674

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GWickB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_EvXPderivPhiP

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
theorem _root_.solution (ε : Fin m → Bool) (c t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (x : Fin m → Fin n → ℂ)
    (a : Fin m) (j : Fin n) :
    evX (pderiv (a, j, false) (phiP ε c t b)) x = -∑ k, (Amat ε c t b a) k j * star (x a k) := by
  simp only [phiP, map_neg, map_sum, pderiv_mul, pderiv_C, pderiv_X, Pi.single_apply]
  simp only [evX, map_neg, map_sum, map_mul, Prod.ext_iff]
  simp only [mul_zero, mul_one, zero_mul, Pi.single_apply, Prod.mk.injEq, and_true, Bool.false_eq_true, and_false,
    if_false, map_zero, add_zero, zero_add]
  rw [neg_inj, Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hj; simp [hj]
    · simp
  · intro a' _ ha; simp [ha]
  · simp
end PositivityTheory.Rg.Sw.WR.G
