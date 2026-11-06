-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.kaehlerRingIso_right_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:59:25.20486+00:00
-- url     : https://prove2.me/submissions/f05ec7c2-5c9a-4b85-abfe-84d6f29cd0ca

import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_KaehlerRingIso
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_kaehlerRingIso_inv_hom_ring

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory
noncomputable section
universe u
variable {k B B' : CommRingCat.{u}} (phi : k ⟶ B) (psi : k ⟶ B')
  (e : B ≅ B') (h : phi ≫ e.hom = psi)
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution : Function.RightInverse
    (kaehlerRingIso_backward phi psi e h) (kaehlerRingIso_forward phi psi e h) := by
  let alpha := kaehlerRingIso_backward phi psi e h ≫
    (ModuleCat.restrictScalars e.inv.hom).map (kaehlerRingIso_forward phi psi e h) ≫
    (ModuleCat.restrictScalarsComp'App e.inv.hom e.hom.hom (RingHom.id B')
      (kaehlerRingIso_inv_hom_ring e) (CommRingCat.KaehlerDifferential psi)).inv ≫
    (ModuleCat.restrictScalarsId B').hom.app (CommRingCat.KaehlerDifferential psi)
  have heq : alpha = 𝟙 (CommRingCat.KaehlerDifferential psi) := by
    apply CommRingCat.KaehlerDifferential.ext
    intro b
    change kaehlerRingIso_forward phi psi e h
      (kaehlerRingIso_backward phi psi e h (CommRingCat.KaehlerDifferential.d b)) =
        CommRingCat.KaehlerDifferential.d b
    simp only [kaehlerRingIso_forward, kaehlerRingIso_backward,
      CommRingCat.KaehlerDifferential.map_d]
    have hb : e.hom (e.inv b) = b := congrArg (fun t : B' ⟶ B' => t b) e.inv_hom_id
    exact congrArg (CommRingCat.KaehlerDifferential.d (f := psi)) hb
  intro x
  exact congrArg (fun t => t x) heq
end QEC.Coding.AlgebraicGeometry
