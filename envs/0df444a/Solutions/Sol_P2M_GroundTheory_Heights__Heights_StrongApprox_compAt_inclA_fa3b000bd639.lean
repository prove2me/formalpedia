-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_compAt_inclA_fa3b000bd639
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:20:36.848892+00:00
-- url     : https://prove2.me/submissions/ac1e49b4-5b00-49d4-af8a-dbc6bb41da50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PTruncation
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
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA
open Classical
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]
namespace GroundTheory.Heights₂.Heights.StrongApprox
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (y : E) :
    compAt E v (inclA F E y) = inclV E v y := by
  simp [compAt, inclA, inclV]
end GroundTheory.Heights₂.Heights.StrongApprox
