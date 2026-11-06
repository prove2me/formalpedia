-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.kaehlerRingIso_left_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:59:54.47676+00:00
-- url     : https://prove2.me/submissions/4d5750b0-de8c-449b-b368-f2feb206ba1b

import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_KaehlerRingIso
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_kaehlerRingIso_hom_inv_ring

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory
noncomputable section
universe u
variable {k B B' : CommRingCat.{u}} (phi : k ⟶ B) (psi : k ⟶ B')
  (e : B ≅ B') (h : phi ≫ e.hom = psi)
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution : Function.LeftInverse
    (kaehlerRingIso_backward phi psi e h) (kaehlerRingIso_forward phi psi e h) := by
  let alpha := kaehlerRingIso_forward phi psi e h ≫
    (ModuleCat.restrictScalars e.hom.hom).map (kaehlerRingIso_backward phi psi e h) ≫
    (ModuleCat.restrictScalarsComp'App e.hom.hom e.inv.hom (RingHom.id B)
      (kaehlerRingIso_hom_inv_ring e) (CommRingCat.KaehlerDifferential phi)).inv ≫
    (ModuleCat.restrictScalarsId B).hom.app (CommRingCat.KaehlerDifferential phi)
  have heq : alpha = 𝟙 (CommRingCat.KaehlerDifferential phi) := by
    apply CommRingCat.KaehlerDifferential.ext
    intro b
    change kaehlerRingIso_backward phi psi e h
      (kaehlerRingIso_forward phi psi e h (CommRingCat.KaehlerDifferential.d b)) =
        CommRingCat.KaehlerDifferential.d b
    simp only [kaehlerRingIso_forward, kaehlerRingIso_backward,
      CommRingCat.KaehlerDifferential.map_d]
    have hb : e.inv (e.hom b) = b := congrArg (fun t : B ⟶ B => t b) e.hom_inv_id
    exact congrArg (CommRingCat.KaehlerDifferential.d (f := phi)) hb
  intro x
  exact congrArg (fun t => t x) heq
end QEC.Coding.AlgebraicGeometry
