-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.AsmA.act_one_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:39:52.840982+00:00
-- url     : https://prove2.me/submissions/58fc40be-6f3e-46f0-bac2-9b17c0edebee

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyTA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.AsmA
variable {ι A B : Type} [Fintype ι]
namespace PositivityTheory.Rg.Sw.FFTSteps.AsmA
theorem _root_.solution (z : (ι × A) ⊕ (ι × B) → ℂ) [DecidableEq ι] : act (1 : Matrix ι ι ℂ) 1 z = z := by
  funext v
  rcases v with ⟨i, a⟩ | ⟨i, b⟩ <;> simp [act, Matrix.one_apply]
end PositivityTheory.Rg.Sw.FFTSteps.AsmA
