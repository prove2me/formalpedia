-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.selectedPlaces_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:33:28.708418+00:00
-- url     : https://prove2.me/submissions/13f50227-7a62-41f5-98d0-8b1b0a26d397

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SelectedPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlaceDegree
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Logic.Equiv.Fintype
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Enumeration

set_option autoImplicit false
open Filter
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (i : ℕ) :
    (selectedPlaces i).card = selectedLength i := by
  classical
  rw [selectedPlaces, Finset.card_image_of_injective _
    (selectedPlace_injective i), Finset.card_univ, Fintype.card_fin]
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
