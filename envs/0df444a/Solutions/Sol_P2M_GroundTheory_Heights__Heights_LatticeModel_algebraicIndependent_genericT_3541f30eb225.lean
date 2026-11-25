-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_algebraicIndependent_genericT_3541f30eb225
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:02:19.270143+00:00
-- url     : https://prove2.me/submissions/a4cab731-2a44-4bd4-9dd8-6db6add3a8d0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.LatticeModel
variable {K : Type} [Field K] [NumberField K] {N r : ℕ} {L : Submodule (𝓞 K) (Fin (r + 1) → K)}
  {φ : Fin (N + 1) → Fin (r + 1) → K}
namespace GroundTheory.Heights₂.Heights.LatticeModel
theorem _root_.solution : AlgebraicIndependent ℚ (genericT K r) := by
  have h := (MvPolynomial.algebraicIndependent_X (Fin r) K).map'
    (f := IsScalarTower.toAlgHom K (MvPolynomial (Fin r) K) (LatticeField K r)) (IsFractionRing.injective _ _)
  exact h.restrictScalars (algebraMap ℚ K).injective
end GroundTheory.Heights₂.Heights.LatticeModel
