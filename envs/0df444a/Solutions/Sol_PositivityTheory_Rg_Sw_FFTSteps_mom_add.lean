-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.mom_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:44:22.201973+00:00
-- url     : https://prove2.me/submissions/13533e61-2e6d-4710-a1eb-3ed8271a723e

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_NullTop
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_integrable_evX_gs

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
theorem _root_.solution {c : ℝ} (hc : 0 < c) (R1 R2 P : PX m n) :
    mom c ((R1 + R2) * P) = mom c (R1 * P) + mom c (R2 * P) := by
  unfold mom
  have h : ∀ x, evX ((R1 + R2) * P) x * gs c x = evX (R1 * P) x * gs c x + evX (R2 * P) x * gs c x := by
    intro x
    simp only [evX, add_mul, map_add]
  simp_rw [h]
  exact integral_add (integrable_evX_gs _ hc) (integrable_evX_gs _ hc)
end PositivityTheory.Rg.Sw.FFTSteps
