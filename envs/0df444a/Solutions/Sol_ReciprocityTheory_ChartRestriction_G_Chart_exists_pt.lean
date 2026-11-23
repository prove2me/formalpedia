-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.exists_pt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:19.068802+00:00
-- url     : https://prove2.me/submissions/34231a41-f86b-4cd6-919e-9b3951ee9132

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pt_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {R₀ : Type} [CommRing R₀]
variable (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G]
variable {G}
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution (C : Chart G) {P : Type} [CommRing P] [Algebra R₀ P] (x : sp P ⟶ G)
    (hx : ⊤ ≤ x.left ⁻¹ᵁ C.U) : ∃ h : Γ(G.left, C.U) →ₐ[R₀] P, x = pt C h := by
  have hx' : Spec.map (x.left.appLE C.U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of P)).hom) ≫ C.hU.fromSpec =
      x.left := chart_eq C x.left hx
  have hc : (x.left.appLE C.U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of P)).hom).hom.comp (alg0 C) =
      algebraMap R₀ P := by
    have e : Spec.map (CommRingCat.ofHom ((x.left.appLE C.U ⊤ hx ≫
        (Scheme.ΓSpecIso (CommRingCat.of P)).hom).hom.comp (alg0 C))) =
        Spec.map (CommRingCat.ofHom (algebraMap R₀ P)) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, ← fromSpec_over, ← Category.assoc, hx']
      exact Over.w x
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  refine ⟨{ (x.left.appLE C.U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of P)).hom).hom with
    commutes' := fun r => RingHom.congr_fun hc r }, ?_⟩
  apply Over.OverMorphism.ext
  rw [pt_left]
  exact hx'.symm
end ReciprocityTheory.ChartRestriction.G.Chart
