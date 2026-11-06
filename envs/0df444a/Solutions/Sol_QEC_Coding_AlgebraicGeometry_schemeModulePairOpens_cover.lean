-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.schemeModulePairOpens_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:58:31.995309+00:00
-- url     : https://prove2.me/submissions/8695aa4d-7a2a-429c-9a6e-f43f73d964b1

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_ModulePairDescent

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {X : Scheme.{u}} (M : X.Modules) (U V : X.Opens)
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution (hcover : U ⊔ V = ⊤) :
    (⊤ : X.Opens) ≤ iSup (schemeModulePairOpens U V) := by
  rw [← hcover]
  exact sup_le (le_iSup (schemeModulePairOpens U V) false)
    (le_iSup (schemeModulePairOpens U V) true)
end QEC.Coding.AlgebraicGeometry
