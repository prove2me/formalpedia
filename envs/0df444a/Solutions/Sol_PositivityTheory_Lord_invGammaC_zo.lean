-- Prove2me | solution 1 for PositivityTheory.Lord.invGammaC_zo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:18:35.719812+00:00
-- url     : https://prove2.me/submissions/062e596a-c3c8-4a01-b019-31d1e601a9e6

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ZetaEulerProducts_MeromorphicAtProd
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ZetaEulerProducts_InvGammaRZo
import Theorems.Thm_PositivityTheory_Lord_invGamma_zo
import Theorems.Thm_PositivityTheory_Lord_PO_mul
import Theorems.Thm_PositivityTheory_Lord_ZO_inv
import Theorems.Thm_PositivityTheory_Lord_ZO_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Complex
open scoped Real
open PositivityTheory PositivityTheory.Lord
namespace PositivityTheory.Lord
theorem _root_.solution (j : ℤ) (hj : j ≤ 0) : ZO (fun s => (Gammaℂ s)⁻¹) (j : ℂ) 1 := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, j = -(n : ℤ) := ⟨j.natAbs, by omega⟩
  obtain ⟨u, hu, hu0, hue⟩ := invGamma_zo n
  have hjn : (j : ℂ) = -(n : ℂ) := by rw [hn]; push_cast; ring
  have h2pi : (2 * (π : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero)
  refine ⟨fun s => (2 * (2 * (π : ℂ)) ^ (-s))⁻¹ * u s, ?_, ?_, ?_⟩
  · have hd : Differentiable ℂ fun s : ℂ => 2 * (2 * (π : ℂ)) ^ (-s) :=
      fun s => (differentiableAt_id.neg.const_cpow (Or.inl h2pi)).const_mul 2
    refine ((hd.analyticAt _).inv ?_).mul (by rw [hjn]; exact hu)
    exact mul_ne_zero two_ne_zero (by rw [Ne, cpow_eq_zero_iff]; tauto)
  · simp only
    rw [hjn]
    refine mul_ne_zero (inv_ne_zero (mul_ne_zero two_ne_zero ?_)) hu0
    rw [Ne, cpow_eq_zero_iff]; tauto
  · rw [hjn]
    filter_upwards [hue] with s h1
    rw [Gammaℂ_def, mul_inv, h1]
    ring
end PositivityTheory.Lord
