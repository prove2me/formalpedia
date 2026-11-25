-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.actZ_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:40:58.203342+00:00
-- url     : https://prove2.me/submissions/fe2311b9-01cb-4d33-920b-ad90f5260b2a

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_ExistsUnitaryDiagonalUnitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Complex Filter Topology
open scoped ComplexConjugate ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps
variable {ι A B : Type} [Fintype ι] [DecidableEq ι]
namespace PositivityTheory.Rg.Sw.FFTSteps
theorem _root_.solution (a b : ι → ℂ) (z : (ι × A) ⊕ (ι × B) → ℂ) :
    actZ (diagonal a) (diagonal b) z = Sum.elim (fun x => a x.1 * z (Sum.inl x)) (fun y => b y.1 * z (Sum.inr y)) := by
  funext v
  rcases v with x | y
  · simp [actZ, diagonal_apply]
  · simp [actZ, diagonal_apply]
end PositivityTheory.Rg.Sw.FFTSteps
