-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.PosProof.eval_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:30:41.746795+00:00
-- url     : https://prove2.me/submissions/260d5642-b25c-4a96-9dbe-1bf462a80522

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_IntegralHkDiag
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_ContinuousPhi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Module
open scoped ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.PosProof
variable {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
namespace PositivityTheory.Rg.Sw.FFTSteps.PosProof
theorem _root_.solution (g : Matrix ι ι ℂ) (f : PV ι A B) (z : Sg ι A B → ℂ) :
    eval z (sub 1 g f) = eval (Phi g z) f := by
  have h : (eval z).comp (sub (A := A) (B := B) 1 g).toRingHom = eval (Phi g z) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [sub]
    · intro s
      rcases s with ⟨i, a⟩ | ⟨i, b⟩
      · simp [sub, Phi, Matrix.one_apply]
      · simp [sub, Phi]
  exact RingHom.congr_fun h f
end PositivityTheory.Rg.Sw.FFTSteps.PosProof
