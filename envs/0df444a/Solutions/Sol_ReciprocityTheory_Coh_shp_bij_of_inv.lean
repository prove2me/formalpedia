-- Prove2me | solution 1 for ReciprocityTheory.Coh.shp_bij_of_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:48.431748+00:00
-- url     : https://prove2.me/submissions/461104c3-efec-402e-9684-7b14a9e1abe1

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogIso
import Definitions.Def_ReciprocityTheory_GroupCohomology_PrismOpZeroEval
import Definitions.Def_ReciprocityTheory_GroupCohomology_Shapiro

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R] {A B : Cx R}
namespace ReciprocityTheory.Coh
theorem _root_.solution (φ : Hom A B) (ψ : Hom B A) (n : ℕ) (h1 : (ψ.comp φ).H n = (Hom.id A).H n)
    (h2 : (φ.comp ψ).H n = (Hom.id B).H n) : Bijective (φ.H n) := by
  have hcomp : ∀ {P Q S : Cx R} (α : Hom Q S) (β : Hom P Q) (x : P.H n),
      (α.comp β).H n x = α.H n (β.H n x) := by
    intro P Q S α β x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  have hid : ∀ {P : Cx R} (x : P.H n), (Hom.id P).H n x = x := by
    intro P x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  refine ⟨fun x y hxy => ?_, fun y => ⟨ψ.H n y, ?_⟩⟩
  · calc x = (Hom.id A).H n x := (hid x).symm
      _ = (ψ.comp φ).H n x := by rw [h1]
      _ = ψ.H n (φ.H n x) := hcomp ψ φ x
      _ = ψ.H n (φ.H n y) := by rw [hxy]
      _ = (ψ.comp φ).H n y := (hcomp ψ φ y).symm
      _ = (Hom.id A).H n y := by rw [h1]
      _ = y := hid y
  · rw [← hcomp φ ψ y, h2, hid]
end ReciprocityTheory.Coh
