-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.bound_aux
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:41:04.716304+00:00
-- url     : https://prove2.me/submissions/e5b17e69-41b4-45e9-99d7-1e6603376829

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_NullTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.FFTSteps
theorem _root_.solution {a r S : ℝ} (ha : 0 < a) (hr : 0 ≤ r) (hS : r ^ 2 ≤ S) :
    r * Real.exp (-(a * S)) ≤ 1 + 1 / a := by
  have hS0 : 0 ≤ S := le_trans (sq_nonneg r) hS
  have h1 : 1 + a * S ≤ Real.exp (a * S) := by
    have := Real.add_one_le_exp (a * S)
    linarith
  have hinv : 0 ≤ 1 / a := by positivity
  have haS : 0 ≤ a * S := mul_nonneg ha.le hS0
  have hprod : (1 + 1 / a) * (1 + a * S) = 1 + a * S + 1 / a + S := by
    field_simp
    ring
  have h2 : r ≤ (1 + 1 / a) * (1 + a * S) := by
    rw [hprod]
    nlinarith [sq_nonneg (r - 1)]
  have h3 : r ≤ (1 + 1 / a) * Real.exp (a * S) := by
    have : 0 ≤ 1 + 1 / a := by positivity
    nlinarith
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  exact h3
end PositivityTheory.Rg.Sw.FFTSteps
