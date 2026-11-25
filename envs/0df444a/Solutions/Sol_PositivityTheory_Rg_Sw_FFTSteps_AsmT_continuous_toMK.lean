-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.AsmT.continuous_toMK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:22:40.954187+00:00
-- url     : https://prove2.me/submissions/3c484837-32fe-403b-83f6-e20f61149b15

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyTB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyT

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
theorem _root_.solution (N : ℕ) :
    Continuous fun k : Formalism.REAL.KG (fun _ : Fin N => true) => Formalism.REAL.toMK k :=
  Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
end PositivityTheory.Rg.Sw.FFTSteps.AsmT
