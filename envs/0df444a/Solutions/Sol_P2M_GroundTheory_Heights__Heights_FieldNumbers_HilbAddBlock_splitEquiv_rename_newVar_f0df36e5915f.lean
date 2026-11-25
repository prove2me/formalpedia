-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_splitEquiv_rename_newVar_f0df36e5915f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:53:06.270978+00:00
-- url     : https://prove2.me/submissions/aed4dd6e-f881-4ceb-8f58-0db2e1cad1be

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsAddBlock
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbAddBlock
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
theorem _root_.solution (q : MvPolynomial (Fin (N + 1)) F) :
    splitEquiv F ι N (rename (newVar ι N) q) = map C q := by
  have h : (splitEquiv F ι N).toRingHom.comp (rename (newVar ι N)).toRingHom =
      (map C : MvPolynomial (Fin (N + 1)) F →+* MvPolynomial (Fin (N + 1)) (MRing ι F)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [splitEquiv, MvPolynomial.algebraMap_eq]
    · intro j
      simp [splitEquiv, varSplit, newVar, sumAlgEquiv_X_inl]
  exact DFunLike.congr_fun h q
end GroundTheory.Heights₂.Heights.FieldNumbers.HilbAddBlock
