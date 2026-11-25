-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.PowSpanB.natCast_smul_add_mem_W
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:39:06.134866+00:00
-- url     : https://prove2.me/submissions/ada5e197-a3d0-494a-8794-5380f5d0f678

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_PowSpan
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PowSpanB_lf_add
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PowSpanB_lf_smul

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
theorem _root_.solution {w v : PX m n} (hw : w ∈ W ε) (hv : v ∈ W ε) (t : ℕ) : (t : ℂ) • v + w ∈ W ε := by
  obtain ⟨h1, hh1, rfl⟩ := hw
  obtain ⟨h2, hh2, rfl⟩ := hv
  refine ⟨(t : ℂ) • h2 + h1, ?_, by rw [lf_add, lf_smul]⟩
  show Matrix.conjTranspose ((t : ℂ) • h2 + h1) = _
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hh2.eq, hh1.eq]
  simp
end PositivityTheory.Rg.Sw.FFTSteps.PowSpanB
