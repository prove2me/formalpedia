-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.mom_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:41:23.612478+00:00
-- url     : https://prove2.me/submissions/7074b4ca-1274-4e87-8a0d-f1198e1ce9e1

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
theorem _root_.solution (c : ℝ) (a : ℂ) (R P : PX m n) : mom c ((a • R) * P) = a * mom c (R * P) := by
  unfold mom
  have h : ∀ x, evX ((a • R) * P) x * gs c x = a * (evX (R * P) x * gs c x) := by
    intro x
    simp only [evX, smul_eq_C_mul, map_mul, eval_C]
    ring
  simp_rw [h]
  exact integral_const_mul a _
end PositivityTheory.Rg.Sw.FFTSteps
