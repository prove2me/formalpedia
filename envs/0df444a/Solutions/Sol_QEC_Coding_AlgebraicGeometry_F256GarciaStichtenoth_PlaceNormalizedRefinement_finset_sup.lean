-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.PlaceNormalizedRefinement.finset_sup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:38:53.247001+00:00
-- url     : https://prove2.me/submissions/e171f748-5216-4d47-8407-3cb56f339e45

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_AmbientPlaceModels
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RefinementBaseTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_PlaceRefinement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_PlaceNormalizedRefinement_compositum
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_NormalizedEdge_compositum
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_NormalizedRefinement_compositum


set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
open scoped QEC.Coding.AlgebraicGeometry.AmbientPlaceModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {F E : Type*} [_root_.Field F] [_root_.Field E]
    [Algebra F256 F] [Algebra F256 E] [Algebra F E] [IsScalarTower F256 F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (Q : GlobalPlace F256 E)
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
namespace PlaceNormalizedRefinement
theorem _root_.solution
    [Finite Q.residueField] {ι : Type*} (s : Finset ι)
    (L : ι → IntermediateField F E)
    (h : ∀ i ∈ s, PlaceNormalizedRefinement F Q ⊥ (L i)) :
    PlaceNormalizedRefinement F Q ⊥ (s.sup L) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sup_empty]
  | @insert i s hi ih =>
      rw [Finset.sup_insert]
      have hi := h i (Finset.mem_insert_self i s)
      have hs := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      exact hi.trans (PlaceNormalizedRefinement.compositum Q hi hs).1
end PlaceNormalizedRefinement
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
