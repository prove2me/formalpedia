-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.SectionDivision.exists_section
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:20:18.946131+00:00
-- url     : https://prove2.me/submissions/0d62753b-3c39-4629-b492-72f6fdec7c0a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionDivision

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.SectionDivision
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
namespace ReciprocityTheory.ChartRestriction.G.H1.SectionDivision
theorem _root_.solution {k : Type} [Field k] [IsAlgClosed k] {P' : Scheme.{0}}
    (p : P' ⟶ Spec (CommRingCat.of k)) [IsFinite p] [Surjective p] :
    ∃ t : Spec (CommRingCat.of k) ⟶ P', t ≫ p = 𝟙 _ := by
  have : IsAffine P' := isAffine_of_isAffineHom p
  obtain ⟨w, -⟩ := Surjective.surj (f := p) (IsLocalRing.closedPoint k)
  have : Nonempty (⊤ : P'.Opens) := ⟨⟨w, trivial⟩⟩
  let θ := Scheme.ΓSpecIso (CommRingCat.of k)
  let ψ : k →+* Γ(P', ⊤) := (p.appTop).hom.comp θ.inv.hom
  let _ : Algebra k Γ(P', ⊤) := ψ.toAlgebra
  have hfin : ψ.Finite := (IsFinite.finite_app p ⊤ (isAffineOpen_top _)).comp
    (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso θ.inv).2)
  have : Module.Finite k Γ(P', ⊤) := hfin
  obtain ⟨M, hM⟩ := Ideal.exists_maximal Γ(P', ⊤)
  let _ : Field (Γ(P', ⊤) ⧸ M) := Ideal.Quotient.field M
  have : Module.Finite k (Γ(P', ⊤) ⧸ M) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ k M).toLinearMap (Ideal.Quotient.mkₐ_surjective k M)
  have : Algebra.IsIntegral k (Γ(P', ⊤) ⧸ M) := Algebra.IsIntegral.of_finite k _
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := Γ(P', ⊤) ⧸ M)
  let e : k ≃+* Γ(P', ⊤) ⧸ M := RingEquiv.ofBijective (algebraMap k (Γ(P', ⊤) ⧸ M)) hb
  let φ' : Γ(P', ⊤) →+* k := e.symm.toRingHom.comp (Ideal.Quotient.mk M)
  have hφ : ∀ c, φ' (ψ c) = c := fun c => by
    show e.symm (Ideal.Quotient.mk M (algebraMap k Γ(P', ⊤) c)) = c
    rw [← Ideal.Quotient.algebraMap_eq, ← RingHom.comp_apply, ← IsScalarTower.algebraMap_eq]
    exact e.symm_apply_apply c
  let φ : Γ(P', ⊤) ⟶ Γ(Spec (CommRingCat.of k), ⊤) := CommRingCat.ofHom φ' ≫ θ.inv
  have hret : p.appTop ≫ φ = 𝟙 _ := by
    ext c
    obtain ⟨d, rfl⟩ : ∃ d, θ.inv.hom d = c := (ConcreteCategory.bijective_of_isIso θ.inv).2 c
    show θ.inv.hom (φ' (ψ d)) = θ.inv.hom d
    rw [hφ]
  refine ⟨(Spec (CommRingCat.of k)).isoSpec.hom ≫ Spec.map φ ≫ P'.isoSpec.inv, ?_⟩
  have nat' : P'.isoSpec.inv ≫ p = Spec.map p.appTop ≫ (Spec (CommRingCat.of k)).isoSpec.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [Category.assoc, Category.assoc, nat', ← Category.assoc (Spec.map φ), ← Spec.map_comp, hret, Spec.map_id,
    Category.id_comp, Iso.hom_inv_id]
end ReciprocityTheory.ChartRestriction.G.H1.SectionDivision
