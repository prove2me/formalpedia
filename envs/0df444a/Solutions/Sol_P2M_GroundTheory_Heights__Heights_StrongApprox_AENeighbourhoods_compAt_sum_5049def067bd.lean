-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_compAt_sum_5049def067bd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:52.981872+00:00
-- url     : https://prove2.me/submissions/118f1df1-7aef-4322-86ef-4e23951e2657

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PAENeighbourhoods

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA
open GroundTheory.Heights₂.Heights.StrongApprox.AENeighbourhoods
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
namespace GroundTheory.Heights₂.Heights.StrongApprox.AENeighbourhoods
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F))
    (X : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → FiniteAdeleRing (𝓞 F) F) :
    compAt E v (∑ l, X l ⊗ₜ[F] intBasis E l) = ∑ l, X l v ⊗ₜ[F] intBasis E l := by
  rw [map_sum]; rfl
end GroundTheory.Heights₂.Heights.StrongApprox.AENeighbourhoods
