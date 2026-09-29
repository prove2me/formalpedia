-- Prove2me | solution 1 for ProjSpaceCech.GradedModule.Hom.secMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/1d06282e-7478-543d-9662-8bbb103b7229

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ProjSpaceCech_GradedModule_Hom_secMap_injective

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

universe u

noncomputable section

open Finset Function MvPolynomial

namespace ProjSpaceCech
p2m_export "ProjSpaceCech" "GradedModule GradedModule.Frac GradedModule.sec GradedModule.sec.mk GradedModule.sec_mk_eq GradedModule.Hom GradedModule.Hom.map_monMul GradedModule.Hom.secMap"
p2m_open "ProjSpaceCech"

section SecMapInj

variable {R : Type u} [CommRing R] {n : ℕ} {D₁ D₂ : GradedModule R n}

namespace GradedModule p2m_export "ProjSpaceCech.GradedModule" "Frac sec sec.mk sec_mk_eq Hom Hom.map_monMul Hom.secMap mk" namespace Hom p2m_export "ProjSpaceCech.GradedModule.Hom" "map_monMul secMap mem_grade mk toLinearMap" end GradedModule.Hom
p2m_open_scoped "ProjSpaceCech.GradedModule ProjSpaceCech.GradedModule.Hom" in
theorem GradedModule.Hom.secMap_mk (φ : GradedModule.Hom D₁ D₂) (I : Finset (Fin (n + 1)))
    (x : GradedModule.Frac D₁ I) :
    GradedModule.Hom.secMap φ I (GradedModule.sec.mk D₁ I x)
      = GradedModule.sec.mk D₂ I ⟨x.denExp, x.hden, φ.toLinearMap x.num, φ.mem_grade _ _ x.hnum⟩ := rfl

p2m_open_scoped "ProjSpaceCech.GradedModule ProjSpaceCech.GradedModule.Hom" in

theorem GradedModule.Hom.secMap_injective' (φ : GradedModule.Hom D₁ D₂)
    (hinj : Function.Injective φ.toLinearMap) (I : Finset (Fin (n + 1))) :
    Function.Injective (GradedModule.Hom.secMap φ I) := by
  intro p q h
  obtain ⟨x, rfl⟩ := Quotient.exists_rep p
  obtain ⟨y, rfl⟩ := Quotient.exists_rep q
  change GradedModule.sec.mk D₁ I x = GradedModule.sec.mk D₁ I y
  change GradedModule.Hom.secMap φ I (GradedModule.sec.mk D₁ I x)
    = GradedModule.Hom.secMap φ I (GradedModule.sec.mk D₁ I y) at h
  rw [GradedModule.Hom.secMap_mk, GradedModule.Hom.secMap_mk, GradedModule.sec_mk_eq] at h
  obtain ⟨c, hc, heq⟩ := h
  refine (GradedModule.sec_mk_eq D₁ I).mpr ⟨c, hc, hinj ?_⟩
  rw [GradedModule.Hom.map_monMul, GradedModule.Hom.map_monMul]
  exact heq

end SecMapInj

end ProjSpaceCech

theorem solution {R : Type u} [CommRing R] {n : ℕ} {D₁ D₂ : ProjSpaceCech.GradedModule R n} (φ : ProjSpaceCech.GradedModule.Hom D₁ D₂)
    (hinj : Function.Injective φ.toLinearMap) (I : Finset (Fin (n + 1))) :
    Function.Injective (ProjSpaceCech.GradedModule.Hom.secMap φ I) :=
  ProjSpaceCech.GradedModule.Hom.secMap_injective' φ hinj I

end

end S_ProjSpaceCech_GradedModule_Hom_secMap_injective
end P2MW
export P2MW.S_ProjSpaceCech_GradedModule_Hom_secMap_injective (solution)
