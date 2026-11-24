-- Prove2me | solution 1 for PI.PolynomialProperness.GN.herm_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:42:31.799622+00:00
-- url     : https://prove2.me/submissions/a4183616-4951-4242-a98a-21cdb722d7c4

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
theorem _root_.solution {k r : ℕ} {g : B.Mat k r} (hg : g ∈ B.GV k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (g *ᵥ v) (g *ᵥ w) = herm (Hpk k r) v w := by
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  unfold herm
  rw [star_mulVec, ← dotProduct_mulVec]
  simp only [mulVec_mulVec]
  rw [← Matrix.mul_assoc, h]
end PI.PolynomialProperness.GN
