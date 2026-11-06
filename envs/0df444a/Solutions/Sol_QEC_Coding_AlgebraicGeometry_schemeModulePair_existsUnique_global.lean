-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.schemeModulePair_existsUnique_global
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:59:24.478708+00:00
-- url     : https://prove2.me/submissions/afb92e71-ce4a-45e8-b76e-b7d60f79de22

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_ModulePairDescent
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeModulePairSections_compatible
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeModulePairOpens_cover

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {X : Scheme.{u}} (M : X.Modules) (U V : X.Opens)
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution (hcover : U ⊔ V = ⊤)
    (s : Γ(M, U)) (t : Γ(M, V))
    (h : M.presheaf.map (TopologicalSpace.Opens.infLELeft U V).op s =
      M.presheaf.map (TopologicalSpace.Opens.infLERight U V).op t) :
    ∃! z : Γ(M, ⊤), M.presheaf.map (homOfLE le_top).op z = s ∧
      M.presheaf.map (homOfLE le_top).op z = t := by
  obtain ⟨z, hz, huniq⟩ := (schemeModuleAbelianSheaf M).existsUnique_gluing'
    (schemeModulePairOpens U V) ⊤ (fun _ => homOfLE le_top)
    (schemeModulePairOpens_cover U V hcover) (schemeModulePairSections M U V s t)
    (schemeModulePairSections_compatible M U V s t h)
  refine ⟨z, ⟨hz false, hz true⟩, ?_⟩
  intro z' hz'
  apply huniq z'
  intro b
  cases b
  · exact hz'.1
  · exact hz'.2
end QEC.Coding.AlgebraicGeometry
