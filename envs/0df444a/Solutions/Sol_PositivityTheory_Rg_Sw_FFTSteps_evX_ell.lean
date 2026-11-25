-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.evX_ell
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:39:50.175882+00:00
-- url     : https://prove2.me/submissions/f9929cfb-dc41-4797-97b9-533cf81e2b85

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
theorem _root_.solution (ε : Fin m → Bool) (b : Matrix (Fin n) (Fin n) ℂ) (x : Fin m → Fin n → ℂ) :
    evX (∑ i, ∑ j, C (b i j) * (Qp ε j i : PX m n)) x = (b * gramX ε x).trace := by
  simp only [evX, map_sum, map_mul, MvPolynomial.eval_C, Matrix.trace, Matrix.diag, Matrix.mul_apply, gramX]
end PositivityTheory.Rg.Sw.FFTSteps
