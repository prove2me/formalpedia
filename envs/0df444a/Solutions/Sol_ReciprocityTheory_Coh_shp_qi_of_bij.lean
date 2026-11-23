-- Prove2me | solution 1 for ReciprocityTheory.Coh.shp_qi_of_bij
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:04.354228+00:00
-- url     : https://prove2.me/submissions/8fd31dbe-d13a-401a-bf2c-f822894f5713

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogIso
import Definitions.Def_ReciprocityTheory_GroupCohomology_PrismOpZeroEval
import Definitions.Def_ReciprocityTheory_GroupCohomology_Shapiro
import Theorems.Thm_ReciprocityTheory_Coh_shp_hom_ext
import Theorems.Thm_ReciprocityTheory_Coh_shp_bij_of_inv

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
theorem _root_.solution (φ : Hom A B) (h : ∀ n, Bijective (φ.f n)) : φ.QuasiIso := by
  let e : ∀ n, A.X n ≃ₗ[R] B.X n := fun n => LinearEquiv.ofBijective (φ.f n) (h n)
  have h1 : ∀ m (y : B.X m), φ.f m ((e m).symm y) = y := fun m y => (e m).apply_symm_apply y
  have h0 : ∀ m (x : A.X m), (e m).symm (φ.f m x) = x := fun m x => (e m).symm_apply_apply x
  let ψ : Hom B A := ⟨fun n => (e n).symm.toLinearMap, fun n x => by
    apply (h (n + 1)).1
    show φ.f (n + 1) ((e (n + 1)).symm (B.d n x)) = φ.f (n + 1) (A.d n ((e n).symm x))
    rw [φ.comm, h1, h1]⟩
  intro n
  apply shp_bij_of_inv φ ψ n
  · congr 1
    apply shp_hom_ext
    intro m
    ext x
    exact h0 m x
  · congr 1
    apply shp_hom_ext
    intro m
    ext y
    exact h1 m y
end ReciprocityTheory.Coh
