-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_splitEquiv_rename_incl_5e9743a2ab6d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:00:47.842311+00:00
-- url     : https://prove2.me/submissions/550b0067-8b86-49f1-b9a2-458f93ae9f35

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
theorem _root_.solution (p : MRing ι F) :
    splitEquiv F ι N (rename (addBlockIncl ι N) p) = C p := by
  have h : (splitEquiv F ι N).toAlgHom.comp (rename (addBlockIncl ι N)) =
      IsScalarTower.toAlgHom F (MRing ι F) (MvPolynomial (Fin (N + 1)) (MRing ι F)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨k, i⟩
    simp [splitEquiv, varSplit, addBlockIncl, sumAlgEquiv_X_inr, MvPolynomial.algebraMap_eq]
  simpa [MvPolynomial.algebraMap_eq] using DFunLike.congr_fun h p
end GroundTheory.Heights₂.Heights.FieldNumbers.HilbAddBlock
