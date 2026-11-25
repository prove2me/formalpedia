-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.PosProof.unitary_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:40:01.066099+00:00
-- url     : https://prove2.me/submissions/fd7f25b4-ab67-40b0-bca3-af3b93ca392d

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
theorem _root_.solution (U : Matrix ι ι ℂ) (hU : star U * U = 1) (v : ι → ℂ) :
    ∑ i, ‖∑ j, U i j * v j‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  apply Complex.ofReal_injective
  have key : star (U.mulVec v) ⬝ᵥ U.mulVec v = star v ⬝ᵥ v := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose, hU,
      Matrix.one_mulVec]
  have e1' : ∀ w : ι → ℂ, star w ⬝ᵥ w = ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
    intro w
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  rw [← e1', ← e1', ← key]
  rfl
end PositivityTheory.Rg.Sw.FFTSteps.PosProof
