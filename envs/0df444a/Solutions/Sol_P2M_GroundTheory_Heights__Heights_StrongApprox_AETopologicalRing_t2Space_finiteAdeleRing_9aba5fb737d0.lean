-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_AETopologicalRing_t2Space_finiteAdeleRing_9aba5fb737d0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:19:36.707234+00:00
-- url     : https://prove2.me/submissions/27154f57-a790-466e-9759-cc9bffd23657

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PAETopologicalRing

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
open scoped RestrictedProduct
namespace GroundTheory.Heights₂.Heights.StrongApprox
namespace AETopologicalRing
theorem _root_.solution (F : Type) [Field F] [NumberField F] :
    T2Space (FiniteAdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space (Πʳ v : HeightOneSpectrum (𝓞 F),
    [v.adicCompletion F, v.adicCompletionIntegers F]))
end AETopologicalRing
end GroundTheory.Heights₂.Heights.StrongApprox
