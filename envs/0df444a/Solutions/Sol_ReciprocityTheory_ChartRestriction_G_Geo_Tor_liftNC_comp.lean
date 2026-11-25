-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.liftNC_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:01:44.798428+00:00
-- url     : https://prove2.me/submissions/e01ae1ca-bcb8-4fd4-b4ca-091ec337b2de

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_liftNC_comp__de63461cc6c3
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
variable {S : Scheme.{0}} {E : SplitExt S} {G₁ G₂ : Over S} [GrpObj G₁] [GrpObj G₂]
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {A B C X ι' : Type} [CommRing A] [CommRing B] [CommRing C] [AddCommGroup X] (f : A →+* B)
    (ρ : B →+* C) (b : Module.Basis ι' ℤ X) (v : ι' → Bˣ) (v' : ι' → Cˣ) (hv : ∀ k, (v' k).val = ρ (v k).val) :
    AddMonoidAlgebra.liftNCRingHom (ρ.comp f) ((Units.coeHom C).comp (AddMonoidHom.toMultiplicativeLeft
        (b.constr ℤ (fun k => Additive.ofMul (v' k))).toAddMonoidHom)) (fun _ _ => Commute.all _ _) =
      ρ.comp (AddMonoidAlgebra.liftNCRingHom f ((Units.coeHom B).comp (AddMonoidHom.toMultiplicativeLeft
        (b.constr ℤ (fun k => Additive.ofMul (v k))).toAddMonoidHom)) (fun _ _ => Commute.all _ _)) := by
  have hlin : (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map ρ.toMonoidHom))).comp
      (b.constr ℤ (fun k => Additive.ofMul (v k))) = b.constr ℤ (fun k => Additive.ofMul (v' k)) := by
    refine b.ext fun k => ?_
    simp only [LinearMap.comp_apply, Module.Basis.constr_basis]
    apply congrArg Additive.ofMul
    exact Units.ext (by rw [hv k]; rfl)
  have key : ∀ y : X, ρ ((Additive.toMul (b.constr ℤ (fun k => Additive.ofMul (v k)) y) : Bˣ) : B) =
      ((Additive.toMul (b.constr ℤ (fun k => Additive.ofMul (v' k)) y) : Cˣ) : C) := by
    intro y
    have := congrArg (fun φ : X →ₗ[ℤ] Additive Cˣ => ((Additive.toMul (φ y) : Cˣ) : C)) hlin
    simpa using this
  rw [← liftNC_comp₀]
  congr 1
  ext x
  first
    | exact (key (Multiplicative.toAdd x)).symm
    | simpa using (key x).symm
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
