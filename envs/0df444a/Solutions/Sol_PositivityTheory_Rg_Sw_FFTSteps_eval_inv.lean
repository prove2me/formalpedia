-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.eval_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:29:31.251399+00:00
-- url     : https://prove2.me/submissions/b3311423-a208-4136-bfcf-6548bdc8e45c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_ExistsUnitaryDiagonalUnitary
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_eval_sub

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
theorem _root_.solution (p : PV ι A B) (hp : IsInv p) (u : Matrix ι ι ℂ) (hu : u ∈ Matrix.unitaryGroup ι ℂ)
    (z : (ι × A) ⊕ (ι × B) → ℂ) : eval (actZ u (u.map star) z) p = eval z p := by
  rw [← eval_sub, hp u hu]
end PositivityTheory.Rg.Sw.FFTSteps
