-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.AsmT.continuous_blk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:40:44.021223+00:00
-- url     : https://prove2.me/submissions/c24fff79-bd2b-42d9-9f93-018c5eb4b0fc

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyTB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyT
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_AsmT_continuous_toMK

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.AsmT
open AsmA
variable {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
namespace PositivityTheory.Rg.Sw.FFTSteps.AsmT
theorem _root_.solution : Continuous fun k : Formalism.REAL.KG (fun _ : Fin (NN ι A B) => true) =>
    blk (ι := ι) (A := A) (B := B) (Formalism.REAL.toMK k) :=
  continuous_pi fun i => continuous_pi fun i' => (continuous_toMK _).matrix_elem _ _
end PositivityTheory.Rg.Sw.FFTSteps.AsmT
