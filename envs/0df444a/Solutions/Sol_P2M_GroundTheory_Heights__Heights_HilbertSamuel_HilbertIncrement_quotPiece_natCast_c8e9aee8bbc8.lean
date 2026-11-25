-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_HilbertIncrement_quotPiece_natCast_c8e9aee8bbc8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:14:34.523042+00:00
-- url     : https://prove2.me/submissions/920d9905-eb67-44dc-b5ad-b6d7b97546e9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ColonSpanSingletonEqOfNotMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertIncrement
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_HilbertIncrement_ringPiece_natCast_788d1e277de0

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
universe u
open GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertIncrement
variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertIncrement
theorem _root_.solution (J : Ideal (MRing ι F)) (a : K → ℕ) :
    quotPiece J (fun k => (a k : ℤ)) = gradedPiece J a := by
  rw [quotPiece, gradedPiece, ringPiece_natCast]
end GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertIncrement
