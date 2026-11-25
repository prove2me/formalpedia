-- Prove2me | solution 1 for PI.PolynomialProperness.GN.hs_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:18:03.90896+00:00
-- url     : https://prove2.me/submissions/4f325853-faa4-4394-a67e-bb453ab37a33

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.GN
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt
namespace PI.PolynomialProperness.GN
theorem _root_.solution {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) : hs Mᴴ = hs M := by
  unfold hs
  simp only [conjTranspose_apply, RCLike.star_def, Complex.normSq_conj]
  exact Finset.sum_comm
end PI.PolynomialProperness.GN
