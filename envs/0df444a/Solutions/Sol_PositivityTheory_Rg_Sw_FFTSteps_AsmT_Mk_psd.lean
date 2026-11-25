-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.AsmT.Mk_psd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:25:42.68792+00:00
-- url     : https://prove2.me/submissions/cbf1af4f-6659-4c50-9a02-83e3300e0bbb

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyT
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_Assembly

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
theorem _root_.solution (k : Formalism.REAL.KG (fun _ : Fin (NN ι A B) => true)) : (Mk (ι := ι) (A := A) (B := B) k).PosSemidef := by
  have e : Mk (ι := ι) (A := A) (B := B) k =
      ((blk (ι := ι) (A := A) (B := B) (Formalism.REAL.toMK k)).map star)ᴴ * (blk (Formalism.REAL.toMK k)).map star := by
    ext i j
    simp [Mk, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [e]
  exact Matrix.posSemidef_conjTranspose_mul_self _
end PositivityTheory.Rg.Sw.FFTSteps.AsmT
