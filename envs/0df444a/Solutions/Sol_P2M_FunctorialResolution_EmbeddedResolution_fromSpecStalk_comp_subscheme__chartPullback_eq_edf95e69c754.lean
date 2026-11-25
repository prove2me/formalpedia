-- Prove2me | solution 1 for P2M_FunctorialResolution_EmbeddedResolution_fromSpecStalk_comp_subscheme__chartPullback_eq_edf95e69c754
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:48:55.683072+00:00
-- url     : https://prove2.me/submissions/f65f4f99-94a0-49b1-a904-df5c1fa7e23b

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartFiberProduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderPullback
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafSmoothPullback
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansionComparison
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_MaxContactIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_StalkIdealSpreadOut
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_MaxContactChartUniqueness
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_appLE_mem_comap_ideal
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_isAffineOpen_mem
import Theorems.Thm_AlgebraicGeometry_Scheme_presheaf_map_eq_of_parallel
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_algebra_formallyEtale
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_C
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_algebraMap_X_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_algebraMap_X_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_coord_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_coord_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_TaylorExpansion_truncatedSeriesRingHom_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_chartPullbackFstStalkMap_eq
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_chartPullbackFst_comp_eq_chartPullbackSnd_comp
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_chartPullbackSndStalkMap_eq
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_chartPullback_coordTop_eq
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_germ_sectionsAlgebraMap_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isTaylorExpansionOn_mvPolynomial
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_map_le_map_of_pow_mul_iterate_deriv_mem
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_maxContactIdeal_eq_derivIdealSheafIterate
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pow_mul_iterate_deriv_mem_of_mul_derivIdeal_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_sectionsAlgebraMap_appLE_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_sub_mem_of_isTaylorExpansionOn
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_truncatedSeries_length_one
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_truncatedSeries_of_deriv_deriv_eq_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.liftToLocalization_algebraMap
attribute [local simp] Derivation.mapToLocalization_algebraMap
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.coordRingHom_X
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.ofCoords_map
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.algebraMap_X_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.algebraMap_X_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.coord_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.coord_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.TaylorExpansion.truncatedSeriesRingHom_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.maxContactIdeal_eq_derivIdealSheafIterate


section
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
section
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}
private theorem opensι_appLE_self_top_eq_topIso_inv {X₁ : Scheme.{u}} (V : X₁.Opens)
    (e : (⊤ : (V.toScheme).Opens) ≤ V.ι ⁻¹ᵁ V) :
    V.ι.appLE V ⊤ e = V.topIso.inv := by
  simp
  exact AlgebraicGeometry.Scheme.presheaf_map_eq_of_parallel ..
end
private theorem mem_maximalIdeal_of_map_eq_zero {A C : Type*} [CommRing A] [CommRing C]
    [IsLocalRing A] [Nontrivial C] (σ : A →+* C) {a : A} (ha : σ a = 0) :
    a ∈ IsLocalRing.maximalIdeal A := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have h1 : IsUnit (σ a) := hu.map σ
  rw [ha] at h1
  exact zero_ne_one (isUnit_zero_iff.mp h1)
private theorem eqToHom_comp_stalkMap_congr {X W : Scheme.{u}} (f g : W ⟶ X) (hfg : f = g)
    (z : ↥W) (x : ↥X) (hf : f.base z = x) (hg : g.base z = x) :
    eqToHom (congrArg (fun y : ↥X => X.presheaf.stalk y) hf.symm) ≫ f.stalkMap z
      = eqToHom (congrArg (fun y : ↥X => X.presheaf.stalk y) hg.symm) ≫ g.stalkMap z := by
  subst hfg
  rfl
private theorem eqToHom_comp_stalkMap_germ {X W : Scheme.{u}} (f : W ⟶ X) (z : ↥W) (x : ↥X)
    (hfz : f.base z = x) (U : X.Opens) (hxU : x ∈ U) (V : W.Opens) (hzV : z ∈ V)
    (e : V ≤ f ⁻¹ᵁ U) (s : Γ(X, U)) :
    (eqToHom (congrArg (fun y : ↥X => X.presheaf.stalk y) hfz.symm) ≫ f.stalkMap z).hom
        ((X.presheaf.germ U x hxU).hom s)
      = (W.presheaf.germ V z hzV).hom ((f.appLE U V e).hom s) := by
  subst hfz
  have key : X.presheaf.germ U (f.base z) hxU ≫ f.stalkMap z
      = f.appLE U V e ≫ W.presheaf.germ V z hzV := by
    rw [Scheme.Hom.appLE, Category.assoc, W.presheaf.germ_res (homOfLE e) z hzV]
    simp
  have h2 := congrArg (fun t : Γ(X, U) ⟶ W.presheaf.stalk z => CommRingCat.Hom.hom t s) key
  rw [eqToHom_refl, Category.id_comp]
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using h2
private theorem eqToHom_comp_stalkMap_mem_maximalIdeal {X W : Scheme.{u}} (f : W ⟶ X) (z : ↥W)
    (x : ↥X) (hfz : f.base z = x) {a : ↥(X.presheaf.stalk x)}
    (ha : a ∈ IsLocalRing.maximalIdeal ↥(X.presheaf.stalk x)) :
    (eqToHom (congrArg (fun y : ↥X => X.presheaf.stalk y) hfz.symm) ≫ f.stalkMap z).hom a
      ∈ IsLocalRing.maximalIdeal ↥(W.presheaf.stalk z) := by
  subst hfz
  rw [eqToHom_refl, Category.id_comp]
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha ⊢
  intro hu
  exact ha (isUnit_of_map_unit ((f.stalkMap z).hom) a hu)
private theorem appLE_topIso_hom_eq_appTop {X W : Scheme.{u}} (U : X.Opens) (f : W ⟶ X)
    (g : W ⟶ U.toScheme) (hfg : f = g ≫ U.ι) (e : (⊤ : W.Opens) ≤ f ⁻¹ᵁ U)
    (t : Γ(U.toScheme, ⊤)) :
    (f.appLE U ⊤ e).hom (U.topIso.hom.hom t) = (g.appTop).hom t := by
  subst hfg
  have e₀ : (⊤ : (U.toScheme).Opens) ≤ U.ι ⁻¹ᵁ U := fun z _ => z.2
  have e' : (⊤ : W.Opens) ≤ g ⁻¹ᵁ (⊤ : (U.toScheme).Opens) := fun z _ => trivial
  have hcomp : (g ≫ U.ι).appLE U ⊤ e = U.ι.appLE U ⊤ e₀ ≫ g.appLE ⊤ ⊤ e' :=
    (Scheme.Hom.appLE_comp_appLE ..).symm
  have hpar : W.presheaf.map (homOfLE e').op
      = W.presheaf.map (𝟙 (Opposite.op (⊤ : W.Opens))) :=
    AlgebraicGeometry.Scheme.presheaf_map_eq_of_parallel ..
  have hmapid : W.presheaf.map (homOfLE e').op = 𝟙 Γ(W, ⊤) := by
    rw [hpar, CategoryTheory.Functor.map_id]
  have happ : g.appLE (⊤ : (U.toScheme).Opens) (⊤ : W.Opens) e' = g.appTop := by
    show g.app ⊤ ≫ W.presheaf.map (homOfLE e').op = g.appTop
    rw [hmapid]
    exact Category.comp_id _
  rw [hcomp, opensι_appLE_self_top_eq_topIso_inv U e₀, happ]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  exact congrArg ((g.appTop).hom) (Iso.hom_inv_id_apply U.topIso t)
private theorem map_le_map_and_sub_mem_of_etaleCoordinates_shift (kk : Type u) [Field kk] {ι : Type u} {R : Type u}
    [CommRing R] {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [Algebra ℚ B]
    [Algebra kk R] [Algebra (MvPolynomial ι kk) R] [IsScalarTower kk (MvPolynomial ι kk) R]
    [Algebra.FormallyEtale (MvPolynomial ι kk) R]
    (φ φ' : R →+* B) (j : ι) (b : R)
    (hcong : ∀ f : R, φ f - φ' f ∈ IsLocalRing.maximalIdeal B)
    (hβ : φ b ∈ IsLocalRing.maximalIdeal B)
    (hconst : ∀ c : kk, φ (algebraMap (MvPolynomial ι kk) R (MvPolynomial.C c))
      = φ' (algebraMap (MvPolynomial ι kk) R (MvPolynomial.C c)))
    (hne : ∀ i : ι, i ≠ j → φ (EtaleCoordinates.coord kk ι R i)
      = φ' (EtaleCoordinates.coord kk ι R i))
    (hj : φ (EtaleCoordinates.coord kk ι R j) + φ b
      = φ' (EtaleCoordinates.coord kk ι R j)) :
    (∀ M J : Ideal R, b ∈ M → M * derivIdeal kk J ≤ J → Ideal.map φ' J ≤ Ideal.map φ J)
      ∧ (∀ Iid : Ideal B, φ b ∈ Iid → ∀ f : R, φ f - φ' f ∈ Iid) := by
  classical
  have hD1 : (EtaleCoordinates.partialDeriv kk ι R j) (EtaleCoordinates.coord kk ι R j) = 1 :=
    EtaleCoordinates.partialDeriv_coord_self kk ι R j
  have hD0 : ∀ i : ι, i ≠ j →
      (EtaleCoordinates.partialDeriv kk ι R j) (EtaleCoordinates.coord kk ι R i) = 0 :=
    fun i hi => EtaleCoordinates.partialDeriv_coord_of_ne kk ι R j i (Ne.symm hi)
  have hderivConst : ∀ c : kk, (EtaleCoordinates.partialDeriv kk ι R j)
      (algebraMap (MvPolynomial ι kk) R (MvPolynomial.C c)) = 0 := by
    intro c
    have hmap : algebraMap (MvPolynomial ι kk) R (MvPolynomial.C c) = algebraMap kk R c := by
      rw [IsScalarTower.algebraMap_apply kk (MvPolynomial ι kk) R c]
      simp [MvPolynomial.algebraMap_eq]
    rw [hmap]
    exact Derivation.map_algebraMap _ c
  have hvar : ∀ (i : ι) (N : ℕ), 1 ≤ N →
      TaylorExpansion.truncatedSeries φ (EtaleCoordinates.partialDeriv kk ι R j) (φ b) N
          (algebraMap (MvPolynomial ι kk) R (MvPolynomial.X i)) -
        φ' (algebraMap (MvPolynomial ι kk) R (MvPolynomial.X i))
          ∈ IsLocalRing.maximalIdeal B ^ N := by
    intro i N hN
    have hco : algebraMap (MvPolynomial ι kk) R (MvPolynomial.X i)
        = EtaleCoordinates.coord kk ι R i := rfl
    rcases Nat.lt_or_ge N 2 with h2 | h2
    · have hN1 : N = 1 := by omega
      subst hN1
      rw [hco, truncatedSeries_length_one, pow_one]
      rcases eq_or_ne i j with hij | hij
      · subst hij
        have hsub : φ (EtaleCoordinates.coord kk ι R i)
            - φ' (EtaleCoordinates.coord kk ι R i) = -(φ b) := by
          rw [← hj]; ring
        rw [hsub]
        exact Submodule.neg_mem _ hβ
      · rw [hne i hij, sub_self]
        exact Submodule.zero_mem _
    · rcases eq_or_ne i j with hij | hij
      · subst hij
        rw [hco, truncatedSeries_of_deriv_deriv_eq_zero φ _ (φ b) N h2 _
            (by rw [hD1]; simp), hD1, map_one, one_mul, hj, sub_self]
        exact Submodule.zero_mem _
      · rw [hco, truncatedSeries_of_deriv_deriv_eq_zero φ _ (φ b) N h2 _
            (by rw [hD0 i hij]; simp), hD0 i hij, map_zero, zero_mul, add_zero,
          hne i hij, sub_self]
        exact Submodule.zero_mem _
  have hrep := isTaylorExpansionOn_mvPolynomial (k := kk) (ι := ι) φ φ'
    (EtaleCoordinates.partialDeriv kk ι R j) (φ b) hβ hconst hderivConst hvar
  have : Algebra.FormallyUnramified (MvPolynomial ι kk) R := inferInstance
  refine ⟨fun M J hbM hMJ => ?_, fun Iid hbI f => ?_⟩
  · exact map_le_map_of_pow_mul_iterate_deriv_mem (MvPolynomial ι kk) φ φ'
      (EtaleCoordinates.partialDeriv kk ι R j) (φ b) b J hcong hβ hrep rfl
      (pow_mul_iterate_deriv_mem_of_mul_derivIdeal_le kk M J (EtaleCoordinates.partialDeriv kk ι R j) b hMJ hbM)
  · exact sub_mem_of_isTaylorExpansionOn (MvPolynomial ι kk) φ φ'
      (EtaleCoordinates.partialDeriv kk ι R j) (φ b) hcong hβ hrep Iid hbI f
private theorem map_le_map_and_sub_mem_of_etaleChart_coord_shift (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p]
    {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ} (c : EtaleChart p U n) (j : Fin n)
    (x : X) (hx : x ∈ U) [Algebra k ↥(X.presheaf.stalk x)]
    (halg : ∀ a : k, algebraMap k ↥(X.presheaf.stalk x) a = stalkAlgebraMap k p x a)
    {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [Algebra ℚ B]
    (φ φ' : ↥(X.presheaf.stalk x) →+* B) (b : ↥(X.presheaf.stalk x))
    (hcong : ∀ f : ↥(X.presheaf.stalk x), φ f - φ' f ∈ IsLocalRing.maximalIdeal B)
    (hβ : φ b ∈ IsLocalRing.maximalIdeal B)
    (hconst : ∀ a : k, φ (stalkAlgebraMap k p x a) = φ' (stalkAlgebraMap k p x a))
    (hne : ∀ i : Fin n, i ≠ j → φ ((X.presheaf.germ U x hx).hom (c.coord i))
      = φ' ((X.presheaf.germ U x hx).hom (c.coord i)))
    (hj : φ ((X.presheaf.germ U x hx).hom (c.coord j)) + φ b
      = φ' ((X.presheaf.germ U x hx).hom (c.coord j))) :
    (∀ M J : Ideal ↥(X.presheaf.stalk x), b ∈ M → M * derivIdeal k J ≤ J →
        Ideal.map φ' J ≤ Ideal.map φ J)
      ∧ (∀ Iid : Ideal B, φ b ∈ Iid → ∀ f : ↥(X.presheaf.stalk x), φ f - φ' f ∈ Iid) := by
  classical
  let instP : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) ↥(X.presheaf.stalk x) :=
    RingHom.toAlgebra ((X.presheaf.germ U x hx).hom.comp c.coordRingHom)
  have instScalarTower : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k)
      ↥(X.presheaf.stalk x) := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    rw [MvPolynomial.algebraMap_eq, halg a]
    show stalkAlgebraMap k p x a
      = (X.presheaf.germ U x hx).hom (c.coordRingHom (MvPolynomial.C a))
    rw [EtaleChart.coordRingHom_C, germ_sectionsAlgebraMap_apply]
  have instFormallyEtale : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k)
      ↥(X.presheaf.stalk x) := by
    let instChart : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) := c.algebra
    let instGerm : Algebra Γ(X, U) ↥(X.presheaf.stalk x) :=
      (X.presheaf.germ U x hx).hom.toAlgebra
    have : IsScalarTower (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U)
        ↥(X.presheaf.stalk x) := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) :=
      c.algebra_formallyEtale hU
    have : IsLocalization (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
        ↥(X.presheaf.stalk x) := hU.isLocalization_stalk ⟨x, hx⟩
    have : Algebra.FormallyEtale Γ(X, U) ↥(X.presheaf.stalk x) :=
      Algebra.FormallyEtale.of_isLocalization (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    exact Algebra.FormallyEtale.comp (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U)
      ↥(X.presheaf.stalk x)
  have hcd : ∀ i : Fin n,
      EtaleCoordinates.coord k (ULift.{u} (Fin n)) ↥(X.presheaf.stalk x) (ULift.up i)
        = (X.presheaf.germ U x hx).hom (c.coord i) := by
    intro i
    show (X.presheaf.germ U x hx).hom (c.coordRingHom (MvPolynomial.X (ULift.up i))) = _
    rw [EtaleChart.coordRingHom_X]
  have hconst' : ∀ a : k,
      φ (algebraMap (MvPolynomial (ULift.{u} (Fin n)) k) ↥(X.presheaf.stalk x)
            (MvPolynomial.C a))
        = φ' (algebraMap (MvPolynomial (ULift.{u} (Fin n)) k) ↥(X.presheaf.stalk x)
            (MvPolynomial.C a)) := by
    intro a
    have hA : algebraMap (MvPolynomial (ULift.{u} (Fin n)) k) ↥(X.presheaf.stalk x)
        (MvPolynomial.C a) = stalkAlgebraMap k p x a := by
      show (X.presheaf.germ U x hx).hom (c.coordRingHom (MvPolynomial.C a)) = _
      rw [EtaleChart.coordRingHom_C, germ_sectionsAlgebraMap_apply]
    rw [hA, hconst a]
  have hne' : ∀ i : ULift.{u} (Fin n), i ≠ ULift.up j →
      φ (EtaleCoordinates.coord k (ULift.{u} (Fin n)) ↥(X.presheaf.stalk x) i)
        = φ' (EtaleCoordinates.coord k (ULift.{u} (Fin n)) ↥(X.presheaf.stalk x) i) := by
    rintro ⟨i⟩ hi
    have hij : i ≠ j := fun hc => hi (by rw [hc])
    rw [hcd i]
    exact hne i hij
  have hj' : φ (EtaleCoordinates.coord k (ULift.{u} (Fin n)) ↥(X.presheaf.stalk x)
        (ULift.up j)) + φ b
      = φ' (EtaleCoordinates.coord k (ULift.{u} (Fin n)) ↥(X.presheaf.stalk x)
        (ULift.up j)) := by
    rw [hcd j]
    exact hj
  exact map_le_map_and_sub_mem_of_etaleCoordinates_shift k φ φ' (ULift.up j) b hcong hβ hconst' hne' hj'
private theorem chartPullbackStalkMap_compat (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p]
    {U : X.Opens} {n : ℕ} (c₁ c₂ : EtaleChart p U n) (x : X) (hx : x ∈ U)
    (h : ChartsAgreeAt c₁ c₂ x hx) :
    (∀ i : Fin n,
        (chartPullbackFstStalkMap c₁ c₂ x hx h).hom ((X.presheaf.germ U x hx).hom (c₁.coord i))
          = (chartPullbackSndStalkMap c₁ c₂ x hx h).hom
              ((X.presheaf.germ U x hx).hom (c₂.coord i)))
      ∧ (∀ a : k, (chartPullbackFstStalkMap c₁ c₂ x hx h).hom (stalkAlgebraMap k p x a)
          = (chartPullbackSndStalkMap c₁ c₂ x hx h).hom (stalkAlgebraMap k p x a))
      ∧ (∀ a : ↥(X.presheaf.stalk x),
          (chartPullbackSndStalkMap c₁ c₂ x hx h).hom a - (chartPullbackFstStalkMap c₁ c₂ x hx h).hom a
            ∈ IsLocalRing.maximalIdeal
                ↥((chartPullback c₁ c₂).presheaf.stalk (chartPullbackPoint c₁ c₂ x hx h))) := by
  have hfb : (chartPullbackFst c₁ c₂).base (chartPullbackPoint c₁ c₂ x hx h) = x :=
    chartPullbackFst_base_chartPullbackPoint c₁ c₂ x hx h
  have hsb : (chartPullbackSnd c₁ c₂).base (chartPullbackPoint c₁ c₂ x hx h) = x :=
    chartPullbackSnd_base_chartPullbackPoint c₁ c₂ x hx h
  have e₁ : (⊤ : (chartPullback c₁ c₂).Opens) ≤ (chartPullbackFst c₁ c₂) ⁻¹ᵁ U :=
    fun z _ => ((pullback.fst c₁.map c₂.map).base z).2
  have e₂ : (⊤ : (chartPullback c₁ c₂).Opens) ≤ (chartPullbackSnd c₁ c₂) ⁻¹ᵁ U :=
    fun z _ => ((pullback.snd c₁.map c₂.map).base z).2
  have hcoordEach : ∀ i : Fin n,
      (chartPullbackFstStalkMap c₁ c₂ x hx h).hom ((X.presheaf.germ U x hx).hom (c₁.coord i))
        = (chartPullbackSndStalkMap c₁ c₂ x hx h).hom
            ((X.presheaf.germ U x hx).hom (c₂.coord i)) := by
    intro i
    rw [chartPullbackFstStalkMap_eq, chartPullbackSndStalkMap_eq,
      eqToHom_comp_stalkMap_germ (chartPullbackFst c₁ c₂) (chartPullbackPoint c₁ c₂ x hx h) x hfb U hx ⊤
        trivial e₁ (c₁.coord i),
      eqToHom_comp_stalkMap_germ (chartPullbackSnd c₁ c₂) (chartPullbackPoint c₁ c₂ x hx h) x hsb U hx ⊤
        trivial e₂ (c₂.coord i)]
    have hc₁ : c₁.coord i = U.topIso.hom.hom (c₁.coordTop i) := rfl
    have hc₂ : c₂.coord i = U.topIso.hom.hom (c₂.coordTop i) := rfl
    rw [hc₁, hc₂,
      appLE_topIso_hom_eq_appTop U (chartPullbackFst c₁ c₂) (pullback.fst c₁.map c₂.map) rfl e₁
        (c₁.coordTop i),
      appLE_topIso_hom_eq_appTop U (chartPullbackSnd c₁ c₂) (pullback.snd c₁.map c₂.map) rfl e₂
        (c₂.coordTop i)]
    exact congrArg _ (chartPullback_coordTop_eq c₁ c₂ i)
  have hscalar : ∀ a : k,
      (chartPullbackFstStalkMap c₁ c₂ x hx h).hom (stalkAlgebraMap k p x a)
        = (chartPullbackSndStalkMap c₁ c₂ x hx h).hom (stalkAlgebraMap k p x a) := by
    intro a
    rw [← germ_sectionsAlgebraMap_apply k p U x hx a, chartPullbackFstStalkMap_eq,
      chartPullbackSndStalkMap_eq,
      eqToHom_comp_stalkMap_germ (chartPullbackFst c₁ c₂) (chartPullbackPoint c₁ c₂ x hx h) x hfb U hx ⊤
        trivial e₁ (sectionsAlgebraMap k p U a),
      eqToHom_comp_stalkMap_germ (chartPullbackSnd c₁ c₂) (chartPullbackPoint c₁ c₂ x hx h) x hsb U hx ⊤
        trivial e₂ (sectionsAlgebraMap k p U a),
      sectionsAlgebraMap_appLE_apply k p (chartPullbackFst c₁ c₂) U ⊤ e₁ a,
      sectionsAlgebraMap_appLE_apply k p (chartPullbackSnd c₁ c₂) U ⊤ e₂ a,
      chartPullbackFst_comp_eq_chartPullbackSnd_comp c₁ c₂]
  refine ⟨hcoordEach, hscalar, ?_⟩
  have hmor : chartPullbackLift c₁ c₂ x hx h ≫ chartPullbackFst c₁ c₂
      = chartPullbackLift c₁ c₂ x hx h ≫ chartPullbackSnd c₁ c₂ := by
    show chartPullbackLift c₁ c₂ x hx h ≫ (pullback.fst c₁.map c₂.map ≫ U.ι)
      = chartPullbackLift c₁ c₂ x hx h ≫ (pullback.snd c₁.map c₂.map ≫ U.ι)
    rw [chartPullbackLift_fst_assoc, chartPullbackLift_snd_assoc]
  have hbf : (chartPullbackLift c₁ c₂ x hx h ≫ chartPullbackFst c₁ c₂).base
      (specResidueFieldPoint (pointOfMem U x hx)) = x := hfb
  have hbs : (chartPullbackLift c₁ c₂ x hx h ≫ chartPullbackSnd c₁ c₂).base
      (specResidueFieldPoint (pointOfMem U x hx)) = x := hsb
  have hstalkeq := eqToHom_comp_stalkMap_congr (chartPullbackLift c₁ c₂ x hx h ≫ chartPullbackFst c₁ c₂)
    (chartPullbackLift c₁ c₂ x hx h ≫ chartPullbackSnd c₁ c₂) hmor
    (specResidueFieldPoint (pointOfMem U x hx)) x hbf hbs
  obtain ⟨σ, hσ⟩ : ∃ σ : (chartPullback c₁ c₂).presheaf.stalk (chartPullbackPoint c₁ c₂ x hx h) ⟶
      (Spec (U.toScheme.residueField (pointOfMem U x hx))).presheaf.stalk
        (specResidueFieldPoint (pointOfMem U x hx)),
      σ = (chartPullbackLift c₁ c₂ x hx h).stalkMap (specResidueFieldPoint (pointOfMem U x hx)) :=
    ⟨_, rfl⟩
  have hcomp1 : (chartPullbackLift c₁ c₂ x hx h ≫ chartPullbackFst c₁ c₂).stalkMap
        (specResidueFieldPoint (pointOfMem U x hx))
      = (chartPullbackFst c₁ c₂).stalkMap (chartPullbackPoint c₁ c₂ x hx h) ≫ σ := by
    rw [hσ]
    exact Scheme.Hom.stalkMap_comp _ _ _
  have hcomp2 : (chartPullbackLift c₁ c₂ x hx h ≫ chartPullbackSnd c₁ c₂).stalkMap
        (specResidueFieldPoint (pointOfMem U x hx))
      = (chartPullbackSnd c₁ c₂).stalkMap (chartPullbackPoint c₁ c₂ x hx h) ≫ σ := by
    rw [hσ]
    exact Scheme.Hom.stalkMap_comp _ _ _
  have hkey : chartPullbackFstStalkMap c₁ c₂ x hx h ≫ σ
      = chartPullbackSndStalkMap c₁ c₂ x hx h ≫ σ := by
    rw [chartPullbackFstStalkMap_eq, chartPullbackSndStalkMap_eq, Category.assoc, Category.assoc,
      ← hcomp1, ← hcomp2]
    exact hstalkeq
  intro a
  have hc := congrArg CommRingCat.Hom.hom hkey
  have h0 : σ.hom ((chartPullbackFstStalkMap c₁ c₂ x hx h).hom a)
      = σ.hom ((chartPullbackSndStalkMap c₁ c₂ x hx h).hom a) := DFunLike.congr_fun hc a
  refine mem_maximalIdeal_of_map_eq_zero σ.hom ?_
  rw [map_sub, ← h0, sub_self]
private theorem spec_map_comp_fromSpecStalk_eq {X Z : Scheme.{u}} (z : ↥Z) {x₁ x₂ : ↥X}
    (hx : x₁ = x₂) (α : X.presheaf.stalk x₁ ⟶ Z.presheaf.stalk z)
    (β : X.presheaf.stalk x₂ ⟶ Z.presheaf.stalk z)
    (hαβ : α = eqToHom (congrArg (fun y : ↥X => X.presheaf.stalk y) hx) ≫ β) :
    Spec.map α ≫ X.fromSpecStalk x₁ = Spec.map β ≫ X.fromSpecStalk x₂ := by
  subst hx
  rw [hαβ, eqToHom_refl, Category.id_comp]
private theorem fromSpecStalk_comp_eq_of_stalkMap_eq {X Y Z : Scheme.{u}} (ιm : Z ⟶ Y) (f g : Y ⟶ X) (z : ↥Z)
    (w : ↥Y) (hw : ιm.base z = w) (x : ↥X) (hf : f.base w = x) (hg : g.base w = x)
    (φ₁ φ₂ : X.presheaf.stalk x ⟶ Y.presheaf.stalk w)
    (hφ₁ : φ₁ = eqToHom (congrArg (fun y : ↥X => X.presheaf.stalk y) hf.symm) ≫ f.stalkMap w)
    (hφ₂ : φ₂ = eqToHom (congrArg (fun y : ↥X => X.presheaf.stalk y) hg.symm) ≫ g.stalkMap w)
    (ρ : Y.presheaf.stalk w ⟶ Z.presheaf.stalk z)
    (hρ : ρ = eqToHom (congrArg (fun y : ↥Y => Y.presheaf.stalk y) hw.symm) ≫ ιm.stalkMap z)
    (hker : ∀ a : ↥(X.presheaf.stalk x), ρ.hom (φ₁.hom a) = ρ.hom (φ₂.hom a)) :
    Z.fromSpecStalk z ≫ ιm ≫ f = Z.fromSpecStalk z ≫ ιm ≫ g := by
  subst hφ₁
  subst hφ₂
  subst hρ
  subst hw
  subst hf
  have hstalk : f.stalkMap (ιm.base z) ≫ ιm.stalkMap z
      = eqToHom (congrArg (fun y : ↥X => X.presheaf.stalk y) hg.symm)
          ≫ (g.stalkMap (ιm.base z) ≫ ιm.stalkMap z) := by
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    have ha := hker a
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, eqToHom_refl,
      CommRingCat.hom_id, RingHom.id_apply] at ha ⊢
    exact ha
  have key := spec_map_comp_fromSpecStalk_eq (X := X) z hg.symm
    (f.stalkMap (ιm.base z) ≫ ιm.stalkMap z) (g.stalkMap (ιm.base z) ≫ ιm.stalkMap z) hstalk
  have L : ∀ u : Y ⟶ X, Z.fromSpecStalk z ≫ ιm ≫ u
      = Spec.map (u.stalkMap (ιm.base z) ≫ ιm.stalkMap z)
        ≫ X.fromSpecStalk (u.base (ιm.base z)) := by
    intro u
    rw [← Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk ιm (x := z), Category.assoc,
      ← Scheme.SpecMap_stalkMap_fromSpecStalk u (x := ιm.base z), ← Category.assoc,
      ← Spec.map_comp]
  rw [L f, L g]
  exact key
private theorem subschemeι_appLE_eq_zero {Y : Scheme.{u}} (J : Y.IdealSheafData)
    (V : Y.affineOpens) {s : Γ(Y, V.1)} (hs : s ∈ J.ideal V) :
    (J.subschemeι.appLE V.1 (J.subschemeι ⁻¹ᵁ V.1) le_rfl).hom s = 0 := by
  have hker : J.subschemeι.ker = J := Scheme.IdealSheafData.ker_subschemeι ..
  have h2 : s ∈ (J.subschemeι.ker).ideal V := by rw [hker]; exact hs
  have h3 : (J.subschemeι.app V.1).hom s = 0 :=
    RingHom.mem_ker.mp (J.subschemeι.ideal_ker_le V h2)
  rw [Scheme.Hom.appLE]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, h3, map_zero]
private theorem stalkMap_germ_eq_zero_of_mem_ideal {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.IdealSheafData)
    (z : ↥((M.comap f).subscheme)) (w : ↥Y)
    (hw : (M.comap f).subschemeι.base z = w)
    (x : ↥X) (hf : f.base w = x) (U : X.Opens) (hU : IsAffineOpen U) (hxU : x ∈ U)
    (V : Y.Opens) (hV : IsAffineOpen V) (hwV : w ∈ V) (eV : V ≤ f ⁻¹ᵁ U)
    (s : Γ(X, U)) (hs : s ∈ M.ideal ⟨U, hU⟩) :
    (eqToHom (congrArg (fun y : ↥Y => Y.presheaf.stalk y) hw.symm)
        ≫ (M.comap f).subschemeι.stalkMap z).hom
      ((eqToHom (congrArg (fun y : ↥X => X.presheaf.stalk y) hf.symm) ≫ f.stalkMap w).hom
        ((X.presheaf.germ U x hxU).hom s)) = 0 := by
  rw [eqToHom_comp_stalkMap_germ f w x hf U hxU V hwV eV s]
  have hzV : z ∈ (M.comap f).subschemeι ⁻¹ᵁ V := by
    show (M.comap f).subschemeι.base z ∈ V
    rw [hw]
    exact hwV
  rw [eqToHom_comp_stalkMap_germ (M.comap f).subschemeι z w hw V hwV
      ((M.comap f).subschemeι ⁻¹ᵁ V) hzV le_rfl ((f.appLE U V eV).hom s)]
  have h3 : (f.appLE U V eV).hom s ∈ (M.comap f).ideal ⟨V, hV⟩ :=
    Scheme.IdealSheafData.appLE_mem_comap_ideal M f ⟨U, hU⟩ ⟨V, hV⟩ eV hs
  rw [subschemeι_appLE_eq_zero (M.comap f) ⟨V, hV⟩ h3, map_zero]
private theorem chartPullbackFstStalkMap_eq_snd_of_coord_eq_zero
    (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p]
    {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ} (c₁ c₂ : EtaleChart p U n) (j : Fin n)
    (hcoord : ∀ i : Fin n, i ≠ j → c₁.coord i = c₂.coord i)
    (x : X) (hx : x ∈ U)
    (hg₁ : (X.presheaf.germ U x hx).hom (c₁.coord j) ∈
      IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x))
    (hg₂ : (X.presheaf.germ U x hx).hom (c₂.coord j) ∈
      IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x))
    [IsLocallyNoetherian (chartPullback c₁ c₂)]
    (h : ChartsAgreeAt c₁ c₂ x hx)
    (C : CommRingCat.{u})
    (ρ : (chartPullback c₁ c₂).presheaf.stalk (chartPullbackPoint c₁ c₂ x hx h) ⟶ C)
    (hv₁ : ρ.hom ((chartPullbackFstStalkMap c₁ c₂ x hx h).hom
      ((X.presheaf.germ U x hx).hom (c₁.coord j))) = 0)
    (hv₂ : ρ.hom ((chartPullbackFstStalkMap c₁ c₂ x hx h).hom
      ((X.presheaf.germ U x hx).hom (c₂.coord j))) = 0) :
    ∀ a : ↥(X.presheaf.stalk x),
      ρ.hom ((chartPullbackFstStalkMap c₁ c₂ x hx h).hom a)
        = ρ.hom ((chartPullbackSndStalkMap c₁ c₂ x hx h).hom a) := by
  classical
  obtain ⟨hcoordEach, hscalar, hcong21⟩ := chartPullbackStalkMap_compat k p c₁ c₂ x hx h
  have hcong12 : ∀ a : ↥(X.presheaf.stalk x),
      (chartPullbackFstStalkMap c₁ c₂ x hx h).hom a - (chartPullbackSndStalkMap c₁ c₂ x hx h).hom a
        ∈ IsLocalRing.maximalIdeal
            ↥((chartPullback c₁ c₂).presheaf.stalk (chartPullbackPoint c₁ c₂ x hx h)) := by
    intro a
    have hneg := Submodule.neg_mem _ (hcong21 a)
    rwa [neg_sub] at hneg
  have hfb : (chartPullbackFst c₁ c₂).base (chartPullbackPoint c₁ c₂ x hx h) = x :=
    chartPullbackFst_base_chartPullbackPoint c₁ c₂ x hx h
  have hcoordNe : ∀ i : Fin n, i ≠ j →
      (X.presheaf.germ U x hx).hom (c₁.coord i) = (X.presheaf.germ U x hx).hom (c₂.coord i) :=
    fun i hi => congrArg _ (hcoord i hi)
  let instRk : Algebra k ↥(X.presheaf.stalk x) := stalkAlgebra k p x
  have instBnoeth : IsNoetherianRing
      ↥((chartPullback c₁ c₂).presheaf.stalk (chartPullbackPoint c₁ c₂ x hx h)) := inferInstance
  let instAlgebraRat : Algebra ℚ ↥((chartPullback c₁ c₂).presheaf.stalk (chartPullbackPoint c₁ c₂ x hx h)) :=
    RingHom.toAlgebra
      ((stalkAlgebraMap k (chartPullbackFst c₁ c₂ ≫ p) (chartPullbackPoint c₁ c₂ x hx h)).comp
        (algebraMap ℚ k))
  have hne : ∀ i : Fin n, i ≠ j →
      (chartPullbackFstStalkMap c₁ c₂ x hx h).hom ((X.presheaf.germ U x hx).hom (c₂.coord i))
        = (chartPullbackSndStalkMap c₁ c₂ x hx h).hom
            ((X.presheaf.germ U x hx).hom (c₂.coord i)) := by
    intro i hi
    rw [← hcoordNe i hi, hcoordEach i, hcoordNe i hi]
  have hj' : (chartPullbackFstStalkMap c₁ c₂ x hx h).hom
        ((X.presheaf.germ U x hx).hom (c₂.coord j))
      + (chartPullbackFstStalkMap c₁ c₂ x hx h).hom
          ((X.presheaf.germ U x hx).hom (c₁.coord j)
            - (X.presheaf.germ U x hx).hom (c₂.coord j))
      = (chartPullbackSndStalkMap c₁ c₂ x hx h).hom
          ((X.presheaf.germ U x hx).hom (c₂.coord j)) := by
    rw [map_sub, ← hcoordEach j]
    ring
  have hβ : (chartPullbackFstStalkMap c₁ c₂ x hx h).hom
      ((X.presheaf.germ U x hx).hom (c₁.coord j)
        - (X.presheaf.germ U x hx).hom (c₂.coord j))
      ∈ IsLocalRing.maximalIdeal
          ↥((chartPullback c₁ c₂).presheaf.stalk (chartPullbackPoint c₁ c₂ x hx h)) :=
    eqToHom_comp_stalkMap_mem_maximalIdeal (chartPullbackFst c₁ c₂) (chartPullbackPoint c₁ c₂ x hx h) x
      hfb (Submodule.sub_mem _ hg₁ hg₂)
  have hbI : (chartPullbackFstStalkMap c₁ c₂ x hx h).hom
      ((X.presheaf.germ U x hx).hom (c₁.coord j)
        - (X.presheaf.germ U x hx).hom (c₂.coord j)) ∈ RingHom.ker ρ.hom := by
    rw [RingHom.mem_ker, map_sub, map_sub, hv₁, hv₂, sub_zero]
  have hsub := (map_le_map_and_sub_mem_of_etaleChart_coord_shift k p hU c₂ j x hx (fun _ => rfl)
    (chartPullbackFstStalkMap c₁ c₂ x hx h).hom (chartPullbackSndStalkMap c₁ c₂ x hx h).hom
    ((X.presheaf.germ U x hx).hom (c₁.coord j) - (X.presheaf.germ U x hx).hom (c₂.coord j))
    hcong12 hβ hscalar hne hj').2 (RingHom.ker ρ.hom) hbI
  intro a
  have ha := hsub a
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at ha
  exact ha
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution
    (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p]
    (I : X.IdealSheafData) {m : ℕ} (_hm : 1 ≤ m)
    (_hinv : IsMaxContactInvariant k p I m)
    {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ} (c₁ c₂ : EtaleChart p U n) (j : Fin n)
    (hcoord : ∀ i : Fin n, i ≠ j → c₁.coord i = c₂.coord i)
    (x : X) (hx : x ∈ U)
    (hmem₁ : c₁.coord j ∈ (maxContactIdeal k p I m).ideal ⟨U, hU⟩)
    (hmem₂ : c₂.coord j ∈ (maxContactIdeal k p I m).ideal ⟨U, hU⟩)
    (hg₁ : (X.presheaf.germ U x hx).hom (c₁.coord j) ∈
      IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x))
    (hg₂ : (X.presheaf.germ U x hx).hom (c₂.coord j) ∈
      IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x))
    (_hsupp : x ∈ (maxContactIdeal k p I m).support)
    [IsLocallyNoetherian (chartPullback c₁ c₂)]
    [IsLocallyNoetherian ((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subscheme]
    (h : ChartsAgreeAt c₁ c₂ x hx)
    (z : ↥(((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subscheme))
    (hz : ((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subschemeι.base z =
      chartPullbackPoint c₁ c₂ x hx h) :
    (((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subscheme).fromSpecStalk z ≫
        ((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subschemeι ≫
          chartPullbackFst c₁ c₂ =
      (((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subscheme).fromSpecStalk z ≫
        ((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subschemeι ≫
          chartPullbackSnd c₁ c₂ := by
  classical
  obtain ⟨V₀, hwV₀, hV₀⟩ :=
    AlgebraicGeometry.Scheme.exists_isAffineOpen_mem (chartPullbackPoint c₁ c₂ x hx h)
  have hwpre : chartPullbackPoint c₁ c₂ x hx h ∈ (chartPullbackFst c₁ c₂) ⁻¹ᵁ U := by
    show (chartPullbackFst c₁ c₂).base (chartPullbackPoint c₁ c₂ x hx h) ∈ U
    rw [chartPullbackFst_base_chartPullbackPoint c₁ c₂ x hx h]
    exact hx
  obtain ⟨t, htle, hwt⟩ := hV₀.exists_basicOpen_le
    (V := (V₀ ⊓ ((chartPullbackFst c₁ c₂) ⁻¹ᵁ U) : (chartPullback c₁ c₂).Opens))
    ⟨chartPullbackPoint c₁ c₂ x hx h, ⟨hwV₀, hwpre⟩⟩ hwV₀
  have hVaff : IsAffineOpen ((chartPullback c₁ c₂).basicOpen t) := hV₀.basicOpen t
  have hVle : ((chartPullback c₁ c₂).basicOpen t) ≤ (chartPullbackFst c₁ c₂) ⁻¹ᵁ U :=
    fun y hy => (htle hy).2
  refine fromSpecStalk_comp_eq_of_stalkMap_eq
    ((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subschemeι
    (chartPullbackFst c₁ c₂) (chartPullbackSnd c₁ c₂) z (chartPullbackPoint c₁ c₂ x hx h) hz x
    (chartPullbackFst_base_chartPullbackPoint c₁ c₂ x hx h) (chartPullbackSnd_base_chartPullbackPoint c₁ c₂ x hx h)
    (chartPullbackFstStalkMap c₁ c₂ x hx h) (chartPullbackSndStalkMap c₁ c₂ x hx h)
    (chartPullbackFstStalkMap_eq c₁ c₂ x hx h) (chartPullbackSndStalkMap_eq c₁ c₂ x hx h) _ rfl ?_
  refine chartPullbackFstStalkMap_eq_snd_of_coord_eq_zero k p hU c₁ c₂ j hcoord x hx hg₁ hg₂ h _ _ ?_ ?_
  · exact stalkMap_germ_eq_zero_of_mem_ideal (chartPullbackFst c₁ c₂) (maxContactIdeal k p I m) z
      (chartPullbackPoint c₁ c₂ x hx h) hz x (chartPullbackFst_base_chartPullbackPoint c₁ c₂ x hx h) U hU hx
      ((chartPullback c₁ c₂).basicOpen t) hVaff hwt hVle (c₁.coord j) hmem₁
  · exact stalkMap_germ_eq_zero_of_mem_ideal (chartPullbackFst c₁ c₂) (maxContactIdeal k p I m) z
      (chartPullbackPoint c₁ c₂ x hx h) hz x (chartPullbackFst_base_chartPullbackPoint c₁ c₂ x hx h) U hU hx
      ((chartPullback c₁ c₂).basicOpen t) hVaff hwt hVle (c₂.coord j) hmem₂
end FunctorialResolution.EmbeddedResolution
