-- Prove2me | solution 1 for ProjSpaceCech.GradedModule.Hom.HMap_bijective_of_saturated
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/9be547c2-d686-5245-8b54-c27e537708f2

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import Theorems.Thm_ProjSpaceCech_GradedModule_Hom_cochainMap_bijective_of_saturated
import Theorems.Thm_ProjSpaceCech_GradedModule_HMap_bijective_of_cochainMap_bijective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ProjSpaceCech_GradedModule_Hom_HMap_bijective_of_saturated

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
p2m_export "ProjSpaceCech" "GradedModule GradedModule.Hom GradedModule.Hom.HMap GradedModule.Hom.cochainMap_bijective_of_saturated GradedModule.HMap_bijective_of_cochainMap_bijective"
p2m_open "ProjSpaceCech"

section HMapSat

variable {R : Type u} [CommRing R] {n : ℕ} {D₁ D₂ : GradedModule R n}

namespace GradedModule p2m_export "ProjSpaceCech.GradedModule" "Hom Hom.HMap xMul grade Hom.cochainMap_bijective_of_saturated HMap_bijective_of_cochainMap_bijective" namespace Hom p2m_export "ProjSpaceCech.GradedModule.Hom" "HMap toLinearMap cochainMap_bijective_of_saturated" end GradedModule.Hom
p2m_open_scoped "ProjSpaceCech.GradedModule ProjSpaceCech.GradedModule.Hom" in

theorem GradedModule.Hom.HMap_bijective_of_saturated' (φ : GradedModule.Hom D₁ D₂)
    (hinj : Function.Injective φ.toLinearMap)
    (hsat : ∀ (j : Fin (n + 1)) (e : ℤ), ∀ m ∈ D₂.grade e,
      ∃ k : ℕ, ∃ m' ∈ D₁.grade (e + k), φ.toLinearMap m' = (D₂.xMul j ^ k) m) (i : ℕ) :
    Function.Bijective (GradedModule.Hom.HMap φ i) :=
  GradedModule.HMap_bijective_of_cochainMap_bijective φ
    (GradedModule.Hom.cochainMap_bijective_of_saturated φ hinj hsat) i

end HMapSat

end ProjSpaceCech

theorem solution {R : Type u} [CommRing R] {n : ℕ} {D₁ D₂ : ProjSpaceCech.GradedModule R n} (φ : ProjSpaceCech.GradedModule.Hom D₁ D₂)
    (hinj : Function.Injective φ.toLinearMap)
    (hsat : ∀ (j : Fin (n + 1)) (e : ℤ), ∀ m ∈ D₂.grade e,
      ∃ k : ℕ, ∃ m' ∈ D₁.grade (e + k), φ.toLinearMap m' = (D₂.xMul j ^ k) m) (i : ℕ) :
    Function.Bijective (ProjSpaceCech.GradedModule.Hom.HMap φ i) :=
  ProjSpaceCech.GradedModule.Hom.HMap_bijective_of_saturated' φ hinj hsat i

end

end S_ProjSpaceCech_GradedModule_Hom_HMap_bijective_of_saturated
end P2MW
export P2MW.S_ProjSpaceCech_GradedModule_Hom_HMap_bijective_of_saturated (solution)
