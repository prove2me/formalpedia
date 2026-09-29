-- Prove2me | solution 1 for ProjSpaceCech.GradedModule.Hom.cochainMap_bijective_of_saturated
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/5645d50a-d28f-5822-a486-fef5cb035d22

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import Theorems.Thm_ProjSpaceCech_GradedModule_Hom_secMap_bijective_of_saturated
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ProjSpaceCech_GradedModule_Hom_cochainMap_bijective_of_saturated

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
p2m_export "ProjSpaceCech" "Idx Idx.img Idx.card_img GradedModule GradedModule.Hom GradedModule.Hom.secMap GradedModule.Hom.cochainMap GradedModule.Hom.secMap_bijective_of_saturated"
p2m_open "ProjSpaceCech"

section CochainSat

variable {R : Type u} [CommRing R] {n : ℕ} {D₁ D₂ : GradedModule R n}

namespace GradedModule p2m_export "ProjSpaceCech.GradedModule" "Hom Hom.secMap Hom.cochainMap xMul grade Hom.secMap_bijective_of_saturated" namespace Hom p2m_export "ProjSpaceCech.GradedModule.Hom" "secMap cochainMap toLinearMap secMap_bijective_of_saturated" end GradedModule.Hom
p2m_open_scoped "ProjSpaceCech.GradedModule ProjSpaceCech.GradedModule.Hom" in

theorem GradedModule.Hom.cochainMap_bijective_of_saturated' (φ : GradedModule.Hom D₁ D₂)
    (hinj : Function.Injective φ.toLinearMap)
    (hsat : ∀ (j : Fin (n + 1)) (e : ℤ), ∀ m ∈ D₂.grade e,
      ∃ k : ℕ, ∃ m' ∈ D₁.grade (e + k), φ.toLinearMap m' = (D₂.xMul j ^ k) m) (i : ℕ) :
    Function.Bijective (GradedModule.Hom.cochainMap φ i) := by
  have hb : ∀ s : Idx n i, Function.Bijective (GradedModule.Hom.secMap φ (Idx.img n s)) := fun s =>
    GradedModule.Hom.secMap_bijective_of_saturated φ hinj hsat _
      (by rw [← Finset.card_pos, Idx.card_img]; exact Nat.succ_pos i)
  constructor
  · intro f g h
    funext s
    exact (hb s).1 (congrFun h s)
  · intro g
    choose f hf using fun s => (hb s).2 (g s)
    exact ⟨f, funext hf⟩

end CochainSat

end ProjSpaceCech

theorem solution {R : Type u} [CommRing R] {n : ℕ} {D₁ D₂ : ProjSpaceCech.GradedModule R n} (φ : ProjSpaceCech.GradedModule.Hom D₁ D₂)
    (hinj : Function.Injective φ.toLinearMap)
    (hsat : ∀ (j : Fin (n + 1)) (e : ℤ), ∀ m ∈ D₂.grade e,
      ∃ k : ℕ, ∃ m' ∈ D₁.grade (e + k), φ.toLinearMap m' = (D₂.xMul j ^ k) m) (i : ℕ) :
    Function.Bijective (ProjSpaceCech.GradedModule.Hom.cochainMap φ i) :=
  ProjSpaceCech.GradedModule.Hom.cochainMap_bijective_of_saturated' φ hinj hsat i

end

end S_ProjSpaceCech_GradedModule_Hom_cochainMap_bijective_of_saturated
end P2MW
export P2MW.S_ProjSpaceCech_GradedModule_Hom_cochainMap_bijective_of_saturated (solution)
