-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_relDim_eq_zero_of_ringKrullDim_47c8ef99c9a9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:12:11.832054+00:00
-- url     : https://prove2.me/submissions/59cd413b-f50b-483d-ac4d-fd142ba4a727

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertDimZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
universe u
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution {F : Type*} [Field F] {K : Type} [Fintype K]
    {ι : K → Type} (q : Ideal (MRing ι F))
    (hd : ringKrullDim (MRing ι F ⧸ q) = ((Fintype.card K : ℕ) : WithBot ℕ∞)) :
    GroundTheory.Heights₂.Heights.FieldNumbers.relDim q = ((0 : ℕ) : WithBot (WithTop ℤ)) := by
  unfold GroundTheory.Heights₂.Heights.FieldNumbers.relDim
  rw [hd]
  simp
  change WithTop.map (fun e : ℕ => (e : ℤ) - (Fintype.card K : ℤ))
    ((Fintype.card K : ℕ) : WithTop ℕ) = 0
  exact congrArg WithTop.some (sub_self _)
end GroundTheory.Heights₂.Heights.HilbertSamuel
