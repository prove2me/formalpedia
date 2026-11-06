-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceRecursion_fieldRange_sup_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:36:22.690735+00:00
-- url     : https://prove2.me/submissions/18e6db84-680a-4afd-ad18-b78a8acb7180

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalCoordinateCells
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceCoordinates
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceRecursion_adjoin_coordinate_eq_top
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_Nonnegative_add


set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ) :
    (sourceRecursionEmbedding m).fieldRange ⊔ F256⟮sourceDistinguishedCoordinate (m + 1)⟯ =
      (⊤ : IntermediateField F256 (SourceField (m + 1))) := by
  let T := (sourceRecursionEmbedding m).fieldRange ⊔ F256⟮sourceDistinguishedCoordinate (m + 1)⟯
  apply top_unique
  intro z hzTop
  clear hzTop
  change z ∈ T
  have hz : z ∈ (SourceField m)⟮sourceDistinguishedCoordinate (m + 1)⟯ := by
    rw [sourceRecursion_adjoin_coordinate_eq_top]
    trivial
  induction hz using IntermediateField.adjoin_induction with
  | mem v hv =>
      exact (show F256⟮sourceDistinguishedCoordinate (m + 1)⟯ ≤ T from le_sup_right)
        (IntermediateField.subset_adjoin F256 _ hv)
  | algebraMap v =>
      exact (show (sourceRecursionEmbedding m).fieldRange ≤ T from le_sup_left) ⟨v, rfl⟩
  | add v w _ _ hv hw => exact T.add_mem hv hw
  | mul v w _ _ hv hw => exact T.mul_mem hv hw
  | inv v _ hv => exact T.inv_mem hv
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
