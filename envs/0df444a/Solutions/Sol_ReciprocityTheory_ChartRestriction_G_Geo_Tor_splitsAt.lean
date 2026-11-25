-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.splitsAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:33:00.437372+00:00
-- url     : https://prove2.me/submissions/20f821de-3209-4216-b428-ca0fd5214052

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGt_of_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sabPull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp


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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (hC : Out.CubePullSt) (hU : Out.UnramExtSt) (hB : Out.GtBaseChangeSt) (hS : Y.SplitFibres)
    (P : ValPt Y) : SplitsAt P := by
  have := P.complete
  let f₀ : Sp (ResidueField P.V) ⟶ Y.X := spMap (residue P.V) ≫ P.yt
  let x : Y.X := f₀ (closedPoint (ResidueField P.V))
  let φ₀ : Y.X.residueField x ⟶ CommRingCat.of (ResidueField P.V) :=
    Scheme.descResidueField (Scheme.stalkClosedPointTo f₀)
  have hf₀ : Spec.map φ₀ ≫ Y.X.fromSpecResidueField x = f₀ :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField _ _ f₀
  obtain ⟨k, _, _, hfin, hsep, S, hGt⟩ := hS x
  let Ω := AlgebraicClosure (ResidueField P.V)
  let _ : Algebra (Y.X.residueField x) (ResidueField P.V) := φ₀.hom.toAlgebra
  let σ : k →ₐ[Y.X.residueField x] Ω := IsAlgClosed.lift
  let bs := Module.finBasis (Y.X.residueField x) k
  let k' := IntermediateField.adjoin (ResidueField P.V) (Set.range fun i => σ (bs i))
  have sepσ : ∀ z : k, IsSeparable (ResidueField P.V) (σ z) := fun z =>
    ((Algebra.IsSeparable.isSeparable (Y.X.residueField x) z).map σ σ.injective).tower_top _
  have : FiniteDimensional (ResidueField P.V) k' :=
    IntermediateField.finiteDimensional_adjoin (by rintro _ ⟨i, rfl⟩; exact (sepσ _).isIntegral)
  have : Algebra.IsSeparable (ResidueField P.V) k' :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable _ _).2 (by rintro _ ⟨i, rfl⟩; exact sepσ _)
  have hmem : ∀ z : k, σ z ∈ k' := fun z => by
    rw [← bs.sum_repr z, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply (Y.X.residueField x) (ResidueField P.V) Ω]
    exact mul_mem (k'.algebraMap_mem _) (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  obtain ⟨W, _, _, _, hc, _, h₁, h₂, -, h₄, e, he⟩ := hU P.V k'
  let Wx : UnramExt P.V := { W := W, fin := h₁, inj := h₂, unram := h₄, complete := hc }
  let g : k →+* ResidueField W := e.symm.toRingHom.comp (σ.toRingHom.codRestrict k'.toSubring hmem)
  have hg : g.comp (algebraMap (Y.X.residueField x) k) =
      (e.symm.toRingHom.comp (algebraMap (ResidueField P.V) k')).comp φ₀.hom := by
    ext z
    exact congrArg e.symm (Subtype.ext (σ.commutes z))
  have hr : (residue W).comp (algebraMap P.V W) =
      (e.symm.toRingHom.comp (algebraMap (ResidueField P.V) k')).comp (residue P.V) := by
    ext v
    exact e.injective ((he v).trans (e.apply_symm_apply _).symm)
  have key : spMap g ≫ Spec.map (CommRingCat.ofHom (algebraMap (Y.X.residueField x) k)) ≫ Y.X.fromSpecResidueField x =
      spMap (residue W) ≫ P.ξ Wx := by
    have a₁ : spMap g ≫ Spec.map (CommRingCat.ofHom (algebraMap (Y.X.residueField x) k)) =
        spMap (e.symm.toRingHom.comp (algebraMap (ResidueField P.V) k')) ≫ Spec.map φ₀ :=
      (spMap_comp _ _).symm.trans ((congrArg spMap hg).trans (spMap_comp _ _))
    have a₂ : spMap (residue W) ≫ spMap (algebraMap P.V W) =
        spMap (e.symm.toRingHom.comp (algebraMap (ResidueField P.V) k')) ≫ spMap (residue P.V) :=
      (spMap_comp _ _).symm.trans ((congrArg spMap hr).trans (spMap_comp _ _))
    rw [← Category.assoc, a₁, Category.assoc, hf₀]
    show _ = spMap (residue W) ≫ spMap (algebraMap P.V W) ≫ P.yt
    rw [← Category.assoc (spMap (residue W)), a₂, Category.assoc]
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull hC (P.ξ Wx) Y.t
  obtain ⟨S', -, -, -, -, hGt'⟩ := hB _ _ (spMap g) S _ hGt
  refine ⟨Wx, _, m, S', ?_⟩
  have : IsMonHom (pullCompIso (spMap g) (Spec.map (CommRingCat.ofHom (algebraMap (Y.X.residueField x) k)) ≫
      Y.X.fromSpecResidueField x) Y.t.G).symm.hom := by
    show IsMonHom (pullCompIso _ _ _).inv
    infer_instance
  have h₀ := isGt_of_iso (pullCompIso (spMap g) _ Y.t.G).symm hGt'
  rw [key] at h₀
  exact isGt_of_iso (pullCompIso (spMap (residue W)) (P.ξ Wx) Y.t.G) h₀
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
