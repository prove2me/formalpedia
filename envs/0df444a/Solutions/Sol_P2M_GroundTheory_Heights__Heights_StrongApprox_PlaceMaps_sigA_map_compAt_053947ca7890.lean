-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_sigA_map_compAt_053947ca7890
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:20:18.116462+00:00
-- url     : https://prove2.me/submissions/07412495-4dd4-4deb-a28c-3a57b1b459f3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PPlaceMaps
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_compAt_sigA_47589663127e
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct ReciprocityTheory.ChartRestriction.G.SA
open GroundTheory.Heights₂.Heights.StrongApprox.PlaceMaps
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]
namespace GroundTheory.Heights₂.Heights.StrongApprox.PlaceMaps
theorem _root_.solution (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) {N : ℕ}
    (X : Matrix (Fin N) (Fin N) (AE F E)) :
    (X.map (sigA c)).map (compAt E v) = (X.map (compAt E v)).map (sigV c v).toRingHom := by
  ext i j
  simp [compAt_sigA]
end GroundTheory.Heights₂.Heights.StrongApprox.PlaceMaps
