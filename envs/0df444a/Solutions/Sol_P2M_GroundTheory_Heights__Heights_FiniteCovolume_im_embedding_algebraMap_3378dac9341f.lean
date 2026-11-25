-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_im_embedding_algebraMap_3378dac9341f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:05:49.603179+00:00
-- url     : https://prove2.me/submissions/5c54b60f-a69b-45ae-8919-e1f5950662ba

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StImaginaryLatticeCocompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PImaginaryLatticeCocompact
import Theorems.Thm_GroundTheory_Automorphic_conj_algebraMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution (σ : E →+* ℂ) (c : F) : (σ (algebraMap F E c)).im = 0 := by
  have h := embedding_conj (F := F) σ (algebraMap F E c)
  rw [conj_algebraMap] at h
  exact Complex.conj_eq_iff_im.mp h.symm
end GroundTheory.Heights₂.Heights.FiniteCovolume
