-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_evalAt_singleF_ne_097e515f57f0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:20:33.369165+00:00
-- url     : https://prove2.me/submissions/6f16f391-e486-4d00-b63b-3a67db8955fe

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
theorem _root_.solution {u v : HeightOneSpectrum (𝓞 F)} (h : u ≠ v) (x : v.adicCompletion F) :
    evalAt F u (singleF F v x) = 0 := by
  change Pi.single v x u = 0
  simp [h]
end GroundTheory.Heights₂.Heights.StrongApprox
