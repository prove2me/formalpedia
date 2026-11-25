-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_form_map_compAt_748dc0e274ac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:35.956972+00:00
-- url     : https://prove2.me/submissions/a07a5cf1-2861-4c03-ad27-6150cead61fa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PPlaceMaps
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_inclA_map_compAt_20da9d9df5df
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_sigA_map_compAt_053947ca7890

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
open Matrix NumberField IsDedekindDomain TensorProduct ReciprocityTheory.ChartRestriction.G.SA
open GroundTheory.Heights₂.Heights.StrongApprox.PlaceMaps
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]
namespace GroundTheory.Heights₂.Heights.StrongApprox.PlaceMaps
theorem _root_.solution (c : E ≃ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)) {N : ℕ}
    (J : Matrix (Fin N) (Fin N) E) (X : Matrix (Fin N) (Fin N) (AE F E)) :
    (Xᵀ * J.map (inclA F E) * X.map (sigA c)).map (compAt E w) =
      (X.map (compAt E w))ᵀ * J.map (inclV E w) * (X.map (compAt E w)).map (sigV c w).toRingHom := by
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, inclA_map_compAt, sigA_map_compAt]
end GroundTheory.Heights₂.Heights.StrongApprox.PlaceMaps
