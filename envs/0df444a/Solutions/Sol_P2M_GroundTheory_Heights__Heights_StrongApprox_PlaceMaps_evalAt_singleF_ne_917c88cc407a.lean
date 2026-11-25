-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_evalAt_singleF_ne_917c88cc407a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:19:17.75997+00:00
-- url     : https://prove2.me/submissions/06fbf817-b611-4026-a8b0-4fb4c5280b51

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PPlaceMaps
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
open Classical
namespace GroundTheory.Heights₂.Heights.StrongApprox.PlaceMaps
theorem _root_.solution {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (x : v.adicCompletion F) :
    evalAt F w (singleF F v x) = 0 := by
  show Pi.single v x w = 0
  simp [h]
end GroundTheory.Heights₂.Heights.StrongApprox.PlaceMaps
