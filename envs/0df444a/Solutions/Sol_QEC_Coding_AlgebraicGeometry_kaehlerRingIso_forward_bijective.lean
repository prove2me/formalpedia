-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.kaehlerRingIso_forward_bijective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:00:59.18774+00:00
-- url     : https://prove2.me/submissions/796ab553-4e31-4994-bedc-6252b9b62c42

import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_KaehlerRingIso
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_kaehlerRingIso_left_inverse
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_kaehlerRingIso_right_inverse

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory
noncomputable section
universe u
variable {k B B' : CommRingCat.{u}} (phi : k ⟶ B) (psi : k ⟶ B')
  (e : B ≅ B') (h : phi ≫ e.hom = psi)
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution : Function.Bijective
    (kaehlerRingIso_forward phi psi e h) :=
  ⟨(kaehlerRingIso_left_inverse phi psi e h).injective,
    (kaehlerRingIso_right_inverse phi psi e h).surjective⟩
end QEC.Coding.AlgebraicGeometry
