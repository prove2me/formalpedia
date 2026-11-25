-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.AsmT.continuous_Mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:12:08.555807+00:00
-- url     : https://prove2.me/submissions/f7932bae-282f-4c67-ae1c-f260f8f25e45

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyT
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_Assembly
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_AsmT_continuous_blk


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
open scoped ComplexOrder Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.AsmT
open AsmA
attribute [local irreducible] Tf
variable {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
namespace PositivityTheory.Rg.Sw.FFTSteps.AsmT
theorem _root_.solution : Continuous (Mk (ι := ι) (A := A) (B := B)) :=
  continuous_blk.matrix_transpose.matrix_mul (continuous_blk.matrix_map continuous_star)
end PositivityTheory.Rg.Sw.FFTSteps.AsmT
