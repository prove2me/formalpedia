-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_map_splitEquiv_a10732f4e974
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:53:04.098014+00:00
-- url     : https://prove2.me/submissions/84b7d2ba-0ba2-4a8c-aee4-b9ef43cd42cf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsAddBlock
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbAddBlock
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_splitEquiv_rename_incl_5e9743a2ab6d
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.HilbAddBlock
variable {K : Type} [DecidableEq K] {ι : K → Type} {N : ℕ}
variable {F : Type u} [Field F]
omit [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.HilbAddBlock
theorem _root_.solution (I : Ideal (MRing ι F)) :
    (addBlockPrime N I).map (splitEquiv F ι N) = I.map C := by
  have h : (splitEquiv F ι N).toRingEquiv.toRingHom.comp (rename (addBlockIncl ι N)).toRingHom =
      (C : MRing ι F →+* MvPolynomial (Fin (N + 1)) (MRing ι F)) :=
    RingHom.ext fun p => by simpa using splitEquiv_rename_incl (N := N) p
  change Ideal.map (splitEquiv F ι N).toRingEquiv.toRingHom
    (Ideal.map (rename (addBlockIncl ι N)).toRingHom I) = _
  rw [Ideal.map_map, h]
end GroundTheory.Heights₂.Heights.FieldNumbers.HilbAddBlock
