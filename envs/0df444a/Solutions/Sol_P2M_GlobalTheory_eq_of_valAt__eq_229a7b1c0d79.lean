-- Prove2me | solution 1 for P2M_GlobalTheory_eq_of_valAt__eq_229a7b1c0d79
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:54:54.784486+00:00
-- url     : https://prove2.me/submissions/6276c5b6-3cc7-479d-a6d7-dec36ada5d17

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EqZeroOfForallAlgHomComplex
import Theorems.Thm_GlobalTheory_eq_zero_of_forall_algHom_complex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) →
    (∀ (X : Over (Sp ℂ)) (U : X.left.Opens), IsAffineOpen U → ∀ e : Γ(X.left, U) →+* ℂ, (∀ a, e (constFn X.hom U a) = a) → ∃! x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U ∧ ∀ f, valAt' x.left U f = e f) →
    (∀ (X : Over (Sp ℂ)), IsReduced X.left → LocallyOfFiniteType X.hom → ∀ (U : X.left.Opens) (f f' : Γ(X.left, U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U → valAt' x.left U f = valAt' x.left U f') → f = f') := by
  intro hval haff X hred hft U f f' h
  refine TopCat.Sheaf.eq_of_locally_eq' X.left.sheaf
    (fun V : {V : X.left.Opens // IsAffineOpen V ∧ V ≤ U} => V.1) U (fun V => homOfLE V.2.2) ?_ f f' ?_
  · intro p hp
    obtain ⟨_, ⟨V, hV, rfl⟩, hpV, hVU⟩ :=
      X.left.isBasis_affineOpens.exists_subset_of_mem_open hp U.isOpen
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV, hVU⟩, hpV⟩
  · rintro ⟨V, hV, hVU⟩
    change resG X.left hVU f = resG X.left hVU f'
    let c : ℂ →+* Γ(X.left, V) :=
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appLE ⊤ V (fun _ _ => trivial)).hom
    have hc : c.FiniteType := by
      have h1 : (X.hom.appLE ⊤ V (fun _ _ => trivial)).hom.FiniteType :=
        HasRingHomProperty.appLE @LocallyOfFiniteType X.hom hft ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ _
      exact h1.comp (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2)
    letI : Algebra ℂ Γ(X.left, V) := c.toAlgebra
    haveI : Algebra.FiniteType ℂ Γ(X.left, V) := hc
    rw [← sub_eq_zero]
    apply eq_zero_of_forall_algHom_complex
    intro e
    obtain ⟨x, ⟨hxV, hx⟩, -⟩ := haff X V hV e.toRingHom (fun a => e.commutes a)
    have hres := (hval X.left x.left).2.2.1 U V hVU
    have hxU : ⊤ ≤ x.left ⁻¹ᵁ U := fun p hp => hVU (hxV hp)
    have e1 : e (resG X.left hVU f) = valAt' x.left U f := (hx _).symm.trans (hres f hxV)
    have e2 : e (resG X.left hVU f') = valAt' x.left U f' := (hx _).symm.trans (hres f' hxV)
    rw [map_sub, e1, e2, h x hxU, sub_self]
end GlobalTheory
