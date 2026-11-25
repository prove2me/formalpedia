-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.AsmT.Mk_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:36:50.288622+00:00
-- url     : https://prove2.me/submissions/cdbc2aef-991d-4a51-bc7c-8d5e3eeacd14

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyT
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_Assembly
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_AsmT_emb_injective


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
theorem _root_.solution : Mk (ι := ι) (A := A) (B := B) 1 = 1 := by
  have hb : blk (ι := ι) (A := A) (B := B) (Formalism.REAL.toMK (1 : Formalism.REAL.KG (fun _ : Fin (NN ι A B) => true))) = 1 := by
    have h1 : Formalism.REAL.toM (1 : Formalism.REAL.UJ (fun _ : Fin (NN ι A B) => true)) = 1 := Units.val_one
    ext i j
    simp only [blk, Formalism.REAL.toMK, OneMemClass.coe_one, h1, Matrix.one_apply, emb_injective.eq_iff]
  simp [Mk, hb]
end PositivityTheory.Rg.Sw.FFTSteps.AsmT
