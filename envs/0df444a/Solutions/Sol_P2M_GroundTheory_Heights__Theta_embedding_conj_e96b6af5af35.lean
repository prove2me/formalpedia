-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_embedding_conj_e96b6af5af35
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:32:38.756407+00:00
-- url     : https://prove2.me/submissions/737cc997-40a6-4684-8e1d-b1d83224edeb

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_QuadraticConj
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_CMDatum
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_conj_eq_complexConj_3315d27272de

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open NumberField GroundTheory.Automorphic
variable (F E : Type*) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
  [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {F E}
variable (F E)
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution (φ : E →+* ℂ) (x : E) : φ (conj F E x) = starRingEnd ℂ (φ x) := by
  haveI := isCMField F E
  rw [conj_eq_complexConj, IsCMField.complexEmbedding_complexConj]
end GroundTheory.Heights₂.Theta
