-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.PowSpanB.pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:03:23.606806+00:00
-- url     : https://prove2.me/submissions/fbaebb90-7819-4adf-9db8-9fe538fa1d9d

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_PowSpan
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PowSpanB_lf_eq

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps
open PositivityTheory.Rg.Sw.FFTSteps.PowSpanB
variable {m n : ℕ} (ε : Fin m → Bool)
namespace PositivityTheory.Rg.Sw.FFTSteps.PowSpanB
theorem _root_.solution {w : PX m n} (hw : w ∈ W ε) (k : ℕ) : w ^ k ∈ S ε := by
  obtain ⟨h, hh, rfl⟩ := hw
  exact Submodule.subset_span ⟨h, k, hh, by rw [lf_eq]⟩
end PositivityTheory.Rg.Sw.FFTSteps.PowSpanB
