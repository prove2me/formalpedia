-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_segreMap_X_c51f5f5b34ef
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:29.605991+00:00
-- url     : https://prove2.me/submissions/7a7dcc5d-fabe-4d69-afb2-c342c8106af8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsMultiDegreePositive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSegre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} (F : Type) [Field F]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution (f : ∀ k, ι k) :
    segreMap F (X ⟨(), f⟩ : MRing (fun _ : Unit => ∀ k, ι k) F) = ∏ k, X ⟨k, f k⟩ :=
  aeval_X _ _
end GroundTheory.Heights₂.Heights.HilbertSamuel
