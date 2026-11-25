-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DLm.Gram.gf_zhat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:39:20.964052+00:00
-- url     : https://prove2.me/submissions/8fe39933-5e55-453d-b2e3-5e0bcda7ee23

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFramesCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFdGramCut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.DLm PI.UnitaryGroupMassFormula.DLm.Gram
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace PI.UnitaryGroupMassFormula.DLm.Gram
theorem _root_.solution (z z' : Fin (2 * r + k + 1) → ℂ) {g₁ g₂ : B.Mat k r} (hZ : Zhat k r z z' g₁ = Zhat k r z z' g₂) :
    Gf k r z z' g₁ = Gf k r z z' g₂ := by
  simp only [Gf, Dmin, hZ]
end PI.UnitaryGroupMassFormula.DLm.Gram
