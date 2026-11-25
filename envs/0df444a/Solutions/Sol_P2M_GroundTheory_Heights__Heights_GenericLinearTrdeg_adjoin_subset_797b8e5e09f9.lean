-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_adjoin_subset_797b8e5e09f9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:25:16.2605+00:00
-- url     : https://prove2.me/submissions/71568812-f9e6-489d-ae89-88db3701be77

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PGenericLinearTrdeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.GenericLinearTrdeg
namespace GroundTheory.Heights₂.Heights.GenericLinearTrdeg
theorem _root_.solution {A R : Type*} [CommRing A] [CommRing R] [Algebra R A] (T : Subring A)
    (s : Set A) (h1 : ∀ c : R, algebraMap R A c ∈ T) (h2 : s ⊆ T) :
    (Algebra.adjoin R s : Set A) ⊆ T := by
  intro y hy
  induction hy using Algebra.adjoin_induction with
  | mem a ha => exact h2 ha
  | algebraMap c => exact h1 c
  | add a b _ _ ha hb => exact T.add_mem ha hb
  | mul a b _ _ ha hb => exact T.mul_mem ha hb
end GroundTheory.Heights₂.Heights.GenericLinearTrdeg
