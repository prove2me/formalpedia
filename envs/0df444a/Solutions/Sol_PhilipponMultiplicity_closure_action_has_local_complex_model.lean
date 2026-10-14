-- Prove2me | solution 1 for PhilipponMultiplicity.closure_action_has_local_complex_model
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-11T12:25:11.283656+00:00
-- url     : https://prove2.me/submissions/bcfb4e41-3d16-45a6-9b79-cae928d361d4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_PhilipponMultiplicity_Analytic
import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_Geometry
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
import Definitions.Def_PhilipponMultiplicity_SectionFive
import Definitions.Def_PhilipponMultiplicity_SectionThree
import Definitions.Def_PhilipponMultiplicity_Support
import Definitions.Def_WeierstrassEllipticZeta_SubgroupCoordinateCases
import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Homology.EulerCharacteristic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.Shrink
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Ring.Periodic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.Tactic.Ring
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.JacobsonSpace
import Mathlib.Topology.KrullDimension
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_finite_euler_quotient_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_mvPolynomial_totalDegree_le_forall_eulerChar_tensor_eq_monoidalV2
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_finrank_sections_eq_eulerChar_of_iso_of_forall_subsingleton_HSucc
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_of_iSup_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_linearMap_sections_tensorPow_twistObj_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_projPresentation_pullback_sigma_eq_toProj_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_nonempty_iso_of_toProj_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_forall_subsingleton_HSucc_tensorObj_tensorPow_of_isFinite_toProj_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_glueOfCocycle_mul_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_glueOfCocycle_app_eq_glueFrame
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isInvertible_glueOfCocycle
import Theorems.Thm_PhilipponMultiplicity_Hilbert_idealDimension_antitone
import Theorems.Thm_PhilipponMultiplicity_Hilbert_relevant_prime_dimension_strict

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponDehomogenizedProjChart

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity.DehomogenizedProjChart

open scoped DirectSum
open HomogeneousLocalization

variable {R S : Type*} [CommRing R] [SetLike S R] [AddSubgroupClass S R]
    (𝒜 : ℕ → S) [GradedRing 𝒜] {f : R} (hf : f ∈ 𝒜 1)

def component (n : ℕ) : 𝒜 n →+ HomogeneousLocalization.Away 𝒜 f where
  toFun x := HomogeneousLocalization.Away.mk 𝒜 hf n x (by simpa using x.property)
  map_zero' := by
    apply HomogeneousLocalization.val_injective
    simp only [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero]
    exact Localization.mk_zero _
  map_add' x y := by
    apply HomogeneousLocalization.val_injective
    simp only [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_add]
    change Localization.mk ((x : R) + (y : R)) _ =
      Localization.mk (x : R) _ + Localization.mk (y : R) _
    exact (Localization.add_mk_self _ _ _).symm

theorem component_one : component 𝒜 hf 0 (1 : 𝒜 0) = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [component, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_one]
  simpa using (Localization.mk_one : (Localization.mk (1 : R) 1 : Localization.Away f) = 1)

theorem component_mul {i j : ℕ} (x : 𝒜 i) (y : 𝒜 j) :
    component 𝒜 hf (i + j) (@GradedMonoid.GMul.mul ℕ (fun n => ↥(𝒜 n)) _ _ i j x y) =
      component 𝒜 hf i x * component 𝒜 hf j y := by
  apply HomogeneousLocalization.val_injective
  simp only [component, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_mul,
    Localization.mk_mul]
  congr 1
  apply Subtype.ext
  exact pow_add f i j

def dehomogenize : R →+* HomogeneousLocalization.Away 𝒜 f :=
  (DirectSum.toSemiring (component 𝒜 hf) (component_one 𝒜 hf)
    (component_mul 𝒜 hf)).comp (DirectSum.decomposeRingEquiv 𝒜).toRingHom

theorem dehomogenize_of_mem {n : ℕ} {a : R} (ha : a ∈ 𝒜 n) :
    dehomogenize 𝒜 hf a = HomogeneousLocalization.Away.mk 𝒜 hf n a (by simpa using ha) := by
  change DirectSum.toSemiring (component 𝒜 hf) (component_one 𝒜 hf)
    (component_mul 𝒜 hf) (DirectSum.decompose 𝒜 a) = _
  rw [DirectSum.decompose_of_mem 𝒜 ha, DirectSum.toSemiring_of]
  rfl

theorem dehomogenize_f : dehomogenize 𝒜 hf f = 1 := by
  rw [dehomogenize_of_mem 𝒜 hf hf]
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_one, pow_one]
  exact Localization.mk_self ⟨f, Submonoid.mem_powers f⟩

def ideal (f : R) : Ideal R := Ideal.span {f - 1}

theorem quotient_f : Ideal.Quotient.mk (ideal f) f = 1 := by
  have h : Ideal.Quotient.mk (ideal f) (f - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  simpa only [map_sub, map_one, sub_eq_zero] using h

def toQuotient : HomogeneousLocalization.Away 𝒜 f →+* (R ⧸ ideal f) :=
  (IsLocalization.Away.lift f (S := Localization.Away f)
    (g := Ideal.Quotient.mk (ideal f)) (by rw [quotient_f]; exact isUnit_one)).comp
      (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f))

theorem toQuotient_mk (n : ℕ) (a : R) (ha : a ∈ 𝒜 (n • (1 : ℕ))) :
    toQuotient 𝒜 (HomogeneousLocalization.Away.mk 𝒜 hf n a ha) =
      Ideal.Quotient.mk (ideal f) a := by
  dsimp only [toQuotient, RingHom.coe_comp, Function.comp_apply]
  rw [HomogeneousLocalization.algebraMap_apply]
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
  unfold IsLocalization.Away.lift
  apply (IsLocalization.lift_mk'_spec _ _ _ _).mpr
  simp only [map_pow, quotient_f, one_pow, one_mul]

def fromQuotient : (R ⧸ ideal f) →+* HomogeneousLocalization.Away 𝒜 f :=
  Ideal.Quotient.lift (ideal f) (dehomogenize 𝒜 hf) (by
    change Ideal.span {f - 1} ≤ RingHom.ker (dehomogenize 𝒜 hf)
    apply Ideal.span_le.mpr
    intro a ha
    rcases Set.mem_singleton_iff.mp ha with rfl
    change dehomogenize 𝒜 hf (f - 1) = 0
    rw [map_sub, dehomogenize_f, map_one, sub_self])

@[simp] theorem fromQuotient_mk (a : R) :
    fromQuotient 𝒜 hf (Ideal.Quotient.mk (ideal f) a) = dehomogenize 𝒜 hf a := rfl

theorem toQuotient_dehomogenize (a : R) :
    toQuotient 𝒜 (dehomogenize 𝒜 hf a) = Ideal.Quotient.mk (ideal f) a := by
  classical
  have hs := DirectSum.sum_support_decompose 𝒜 a
  calc
    toQuotient 𝒜 (dehomogenize 𝒜 hf a) =
        toQuotient 𝒜 (dehomogenize 𝒜 hf
          (∑ n ∈ (DirectSum.decompose 𝒜 a).support,
            ((DirectSum.decompose 𝒜 a n : 𝒜 n) : R))) := congrArg _ (congrArg _ hs.symm)
    _ = ∑ n ∈ (DirectSum.decompose 𝒜 a).support,
          Ideal.Quotient.mk (ideal f) ((DirectSum.decompose 𝒜 a n : 𝒜 n) : R) := by
      simp only [map_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [dehomogenize_of_mem 𝒜 hf (DirectSum.decompose 𝒜 a n).property,
        toQuotient_mk]
    _ = Ideal.Quotient.mk (ideal f) a := by rw [← map_sum, hs]

@[simp] theorem toQuotient_fromQuotient (a : R ⧸ ideal f) :
    toQuotient 𝒜 (fromQuotient 𝒜 hf a) = a := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact toQuotient_dehomogenize 𝒜 hf a

@[simp] theorem fromQuotient_toQuotient (a : HomogeneousLocalization.Away 𝒜 f) :
    fromQuotient 𝒜 hf (toQuotient 𝒜 a) = a := by
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hf a
  rw [toQuotient_mk, fromQuotient_mk]
  exact dehomogenize_of_mem 𝒜 hf (by simpa using ha)

def ringEquiv : HomogeneousLocalization.Away 𝒜 f ≃+* (R ⧸ ideal f) :=
  { toQuotient 𝒜 with
    invFun := fromQuotient 𝒜 hf
    left_inv := fromQuotient_toQuotient 𝒜 hf
    right_inv := toQuotient_fromQuotient 𝒜 hf }

@[simp] theorem ringEquiv_mk (n : ℕ) (a : R) (ha : a ∈ 𝒜 (n • (1 : ℕ))) :
    ringEquiv 𝒜 hf (HomogeneousLocalization.Away.mk 𝒜 hf n a ha) =
      Ideal.Quotient.mk (ideal f) a := toQuotient_mk 𝒜 hf n a ha

end PhilipponMultiplicity.DehomogenizedProjChart

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponHomogeneousQuotientGrading

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity.HomogeneousQuotientGrading

open scoped DirectSum

variable {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]
    (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜] (I : Ideal R)

def piece (n : ℕ) : Submodule K (R ⧸ I) :=
  (𝒜 n).map (Ideal.Quotient.mkₐ K I).toLinearMap

instance : SetLike.GradedMonoid (piece 𝒜 I) where
  one_mem := ⟨1, SetLike.GradedOne.one_mem, map_one (Ideal.Quotient.mk I)⟩
  mul_mem := by
    rintro i j x y ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, SetLike.mul_mem_graded ha hb, map_mul (Ideal.Quotient.mk I) a b⟩

def projection (hI : I.IsHomogeneous 𝒜) (n : ℕ) : (R ⧸ I) →ₗ[K] (R ⧸ I) :=
  (I.restrictScalars K).liftQ
    ((Ideal.Quotient.mkₐ K I).toLinearMap.comp (GradedAlgebra.proj 𝒜 n)) (by
      intro a ha
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hI n ha))

theorem projection_on_piece (hI : I.IsHomogeneous 𝒜) (n m : ℕ)
    {x : R ⧸ I} (hx : x ∈ piece 𝒜 I m) :
    projection 𝒜 I hI n x = if n = m then x else 0 := by
  obtain ⟨a, ha, rfl⟩ := hx
  change Ideal.Quotient.mk I (GradedAlgebra.proj 𝒜 n a) = _
  rw [GradedAlgebra.proj_apply]
  by_cases h : n = m
  · subst m
    rw [DirectSum.decompose_of_mem_same 𝒜 ha, if_pos rfl]
    rfl
  · rw [DirectSum.decompose_of_mem_ne 𝒜 ha (Ne.symm h), map_zero, if_neg h]

theorem piece_iSupIndep (hI : I.IsHomogeneous 𝒜) : iSupIndep (piece 𝒜 I) := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hz n hn
  have h := congrArg (projection 𝒜 I hI n) hz
  rw [map_sum, map_zero] at h
  have heq : (∑ m ∈ s, projection 𝒜 I hI n (v m)) = v n := by
    rw [Finset.sum_eq_single n]
    · simpa using projection_on_piece 𝒜 I hI n n (hv n hn)
    · intro m hm hmn
      rw [projection_on_piece 𝒜 I hI n m (hv m hm), if_neg hmn.symm]
    · exact fun hnot => False.elim (hnot hn)
  exact heq.symm.trans h

theorem iSup_piece : (⨆ n, piece 𝒜 I n) = ⊤ := by
  change (⨆ n, (𝒜 n).map (Ideal.Quotient.mkₐ K I).toLinearMap) = ⊤
  rw [← Submodule.map_iSup,
    (DirectSum.Decomposition.isInternal 𝒜).submodule_iSup_eq_top, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (Ideal.Quotient.mk_surjective)

@[instance_reducible]
def gradedAlgebra (hI : I.IsHomogeneous 𝒜) : GradedAlgebra (piece 𝒜 I) :=
  (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (piece_iSupIndep 𝒜 I hI) (iSup_piece 𝒜 I)).gradedAlgebra

end PhilipponMultiplicity.HomogeneousQuotientGrading

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponHomogeneousQuotientCharts

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity.HomogeneousQuotientGrading

open AlgebraicGeometry CategoryTheory

variable {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]
    (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜] (I : Ideal R)

theorem quotient_mem_piece {n : ℕ} {a : R} (ha : a ∈ 𝒜 n) :
    Ideal.Quotient.mk I a ∈ piece 𝒜 I n := ⟨a, ha, rfl⟩

def normalizedIdeal (f : R) : Ideal R := I ⊔ Ideal.span {f - 1}

theorem normalizedIdeal_map (f : R) :
    DehomogenizedProjChart.ideal (Ideal.Quotient.mk I f) =
      (Ideal.span {f - 1}).map (Ideal.Quotient.mk I) := by
  rw [Ideal.map_span, Set.image_singleton, map_sub, map_one]
  rfl

variable [GradedAlgebra (piece 𝒜 I)]

def normalizedRingEquiv {f : R} (hf : f ∈ 𝒜 1) :
    HomogeneousLocalization.Away (piece 𝒜 I) (Ideal.Quotient.mk I f) ≃+*
      (R ⧸ normalizedIdeal I f) :=
  (DehomogenizedProjChart.ringEquiv (piece 𝒜 I) (quotient_mem_piece 𝒜 I hf)).trans
    ((Ideal.quotEquivOfEq (normalizedIdeal_map I f)).trans
      (DoubleQuot.quotQuotEquivQuotSup I (Ideal.span {f - 1})))

@[simp] theorem normalizedRingEquiv_mk {f : R} (hf : f ∈ 𝒜 1)
    (n : ℕ) (a : R) (ha : a ∈ 𝒜 n) :
    normalizedRingEquiv 𝒜 I hf
      (HomogeneousLocalization.Away.mk (piece 𝒜 I) (quotient_mem_piece 𝒜 I hf) n
        (Ideal.Quotient.mk I a) (by simpa using quotient_mem_piece 𝒜 I ha)) =
      Ideal.Quotient.mk (normalizedIdeal I f) a := by
  rw [normalizedRingEquiv, RingEquiv.trans_apply, DehomogenizedProjChart.ringEquiv_mk,
    RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  rfl

def normalizedSchemeIso {f : R} (hf : f ∈ 𝒜 1) :
    (Proj.basicOpen (piece 𝒜 I) (Ideal.Quotient.mk I f)).toScheme ≅
      Spec (.of (R ⧸ normalizedIdeal I f)) :=
  Proj.basicOpenIsoSpec (piece 𝒜 I) (Ideal.Quotient.mk I f)
    (quotient_mem_piece 𝒜 I hf) (by decide) ≪≫
    Scheme.Spec.mapIso (normalizedRingEquiv 𝒜 I hf).symm.toCommRingCatIso.op

theorem normalizedIdeal_isRadical (hred : I.IsRadical) {f : R} (hf : f ∈ 𝒜 1) :
    (normalizedIdeal I f).IsRadical := by
  letI : IsReduced (R ⧸ I) := (Ideal.isRadical_iff_quotient_reduced I).mp hred
  letI : IsReduced (HomogeneousLocalization.Away (piece 𝒜 I) (Ideal.Quotient.mk I f)) :=
    isReduced_of_injective
      (algebraMap (HomogeneousLocalization.Away (piece 𝒜 I) (Ideal.Quotient.mk I f))
        (Localization.Away (Ideal.Quotient.mk I f)))
      (HomogeneousLocalization.val_injective _)
  apply (Ideal.isRadical_iff_quotient_reduced _).mpr
  exact isReduced_of_injective (normalizedRingEquiv 𝒜 I hf).symm
    (normalizedRingEquiv 𝒜 I hf).symm.injective

end PhilipponMultiplicity.HomogeneousQuotientGrading

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponAffineClosedPoints

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section

namespace PhilipponMultiplicity.AffineClosedPoints

open MvPolynomial
open Topology

variable {K : Type*} [Field K] {σ τ : Type*}

@[instance_reducible] def locusTopology (I : Ideal (MvPolynomial σ K)) :
    TopologicalSpace (zeroLocus K I) :=
  TopologicalSpace.induced (fun x : zeroLocus K I => pointToPoint (k := K) x.val)
    inferInstance

theorem nonzero_sets_basis (I : Ideal (MvPolynomial σ K)) :
    letI := locusTopology I
    TopologicalSpace.IsTopologicalBasis
      (Set.range (fun P : MvPolynomial σ K => {x : zeroLocus K I | aeval x.val P ≠ 0})) := by
  let _ := locusTopology I
  have hb := PrimeSpectrum.isTopologicalBasis_basic_opens.induced
    (fun x : zeroLocus K I => pointToPoint (k := K) x.val)
  have hpre (P : MvPolynomial σ K) :
      (fun x : zeroLocus K I => pointToPoint (k := K) x.val) ⁻¹'
        (PrimeSpectrum.basicOpen P : Set (PrimeSpectrum (MvPolynomial σ K))) =
      {x : zeroLocus K I | aeval x.val P ≠ 0} := by
    ext x
    change (P ∉ vanishingIdeal K {x.val}) ↔ aeval x.val P ≠ 0
    rw [mem_vanishingIdeal_singleton_iff]
  simpa only [← Set.range_comp, Function.comp_def, hpre] using hb

def evaluation (I : Ideal (MvPolynomial σ K)) (x : zeroLocus K I) :
    (MvPolynomial σ K ⧸ I) →ₐ[K] K :=
  Ideal.Quotient.liftₐ I (aeval x.val) x.property

@[simp] theorem evaluation_mk (I : Ideal (MvPolynomial σ K))
    (x : zeroLocus K I) (P : MvPolynomial σ K) :
    evaluation I x (Ideal.Quotient.mk I P) = aeval x.val P := rfl

theorem evaluation_surjective (I : Ideal (MvPolynomial σ K))
    (x : zeroLocus K I) : Function.Surjective (evaluation I x) := by
  intro c
  exact ⟨Ideal.Quotient.mk I (C c), by simp⟩

def point (I : Ideal (MvPolynomial σ K)) (x : zeroLocus K I) :
    MaximalSpectrum (MvPolynomial σ K ⧸ I) :=
  ⟨RingHom.ker (evaluation I x).toRingHom,
    RingHom.ker_isMaximal_of_surjective _ (evaluation_surjective I x)⟩

theorem comap_point (I : Ideal (MvPolynomial σ K)) (x : zeroLocus K I) :
    Ideal.comap (Ideal.Quotient.mk I) (point I x).asIdeal =
      vanishingIdeal K {x.val} := by
  ext P
  change evaluation I x (Ideal.Quotient.mk I P) = 0 ↔
    P ∈ vanishingIdeal K {x.val}
  rw [evaluation_mk, mem_vanishingIdeal_singleton_iff]

theorem point_injective (I : Ideal (MvPolynomial σ K)) :
    Function.Injective (point I) := by
  intro x y h
  have heq : vanishingIdeal K {x.val} = vanishingIdeal K {y.val} := by
    rw [← comap_point I x, ← comap_point I y, h]
  apply Subtype.ext
  funext i
  have hx : X i - C (x.val i) ∈ vanishingIdeal K {x.val} := by
    simp
  rw [heq, mem_vanishingIdeal_singleton_iff] at hx
  simpa using (sub_eq_zero.mp (by simpa using hx)).symm

theorem point_surjective [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) : Function.Surjective (point I) := by
  intro m
  let q := Ideal.Quotient.mk I
  have hm : (Ideal.comap q m.asIdeal).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective q Ideal.Quotient.mk_surjective
  obtain ⟨x, hx⟩ := eq_vanishingIdeal_singleton_of_isMaximal K hm
  have hIx : x ∈ zeroLocus K I := by
    intro P hP
    have hmem : P ∈ Ideal.comap q m.asIdeal := by
      change Ideal.Quotient.mk I P ∈ m.asIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hP]
      exact m.asIdeal.zero_mem
    rw [hx, mem_vanishingIdeal_singleton_iff] at hmem
    exact hmem
  refine ⟨⟨x, hIx⟩, ?_⟩
  apply MaximalSpectrum.ext
  apply Ideal.comap_injective_of_surjective q Ideal.Quotient.mk_surjective
  exact (comap_point I ⟨x, hIx⟩).trans hx.symm

theorem evaluate_substitution (P : τ → MvPolynomial σ K) (x : σ → K)
    (F : MvPolynomial τ K) :
    aeval x (aeval P F) = aeval (fun i => aeval x (P i)) F := by
  have h : (aeval x).comp (aeval P) = aeval (fun i => aeval x (P i)) := by
    ext i
    simp
  exact DFunLike.congr_fun h F

theorem substitution_mem [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial τ K)) (J : Ideal (MvPolynomial σ K))
    (hJ : J.IsRadical) (g : zeroLocus K J → zeroLocus K I)
    (P : τ → MvPolynomial σ K)
    (hg : ∀ x i, (g x).val i = aeval x.val (P i))
    (F : MvPolynomial τ K) (hF : F ∈ I) : aeval P F ∈ J := by
  have hvan : aeval P F ∈ vanishingIdeal K (zeroLocus K J) := by
    intro x hx
    rw [evaluate_substitution]
    have heq : (fun i => aeval x (P i)) = (g ⟨x, hx⟩).val :=
      funext (fun i => (hg ⟨x, hx⟩ i).symm)
    rw [heq]
    exact (g ⟨x, hx⟩).property F hF
  rwa [vanishingIdeal_zeroLocus_eq_radical, hJ.radical] at hvan

def quotientMap [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial τ K)) (J : Ideal (MvPolynomial σ K))
    (hJ : J.IsRadical) (g : zeroLocus K J → zeroLocus K I)
    (P : τ → MvPolynomial σ K)
    (hg : ∀ x i, (g x).val i = aeval x.val (P i)) :
    (MvPolynomial τ K ⧸ I) →ₐ[K] (MvPolynomial σ K ⧸ J) :=
  Ideal.Quotient.liftₐ I ((Ideal.Quotient.mkₐ K J).comp (aeval P)) (by
    intro F hF
    change Ideal.Quotient.mk J (aeval P F) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (substitution_mem I J hJ g P hg F hF))

@[simp] theorem quotientMap_mk [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial τ K)) (J : Ideal (MvPolynomial σ K))
    (hJ : J.IsRadical) (g : zeroLocus K J → zeroLocus K I)
    (P : τ → MvPolynomial σ K)
    (hg : ∀ x i, (g x).val i = aeval x.val (P i)) (F : MvPolynomial τ K) :
    quotientMap I J hJ g P hg (Ideal.Quotient.mk I F) =
      Ideal.Quotient.mk J (aeval P F) := rfl

end PhilipponMultiplicity.AffineClosedPoints

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponAffineRegularFunctions

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section

namespace PhilipponMultiplicity.AffineRegularFunctions
open MvPolynomial

variable {K σ X : Type*} [Field K]

def clearingIdeal (a : X → σ → K) (f : X → K) : Ideal (MvPolynomial σ K) where
  carrier := {P | ∃ Q : MvPolynomial σ K, ∀ x, f x * aeval (a x) P = aeval (a x) Q}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro P Q ⟨P', hP⟩ ⟨Q', hQ⟩
    refine ⟨P' + Q', ?_⟩
    intro x
    simp only [map_add, mul_add, hP x, hQ x]
  smul_mem' := by
    rintro P Q ⟨Q', hQ⟩
    refine ⟨P * Q', ?_⟩
    intro x
    simp only [smul_eq_mul, map_mul]
    calc
      f x * (aeval (a x) P * aeval (a x) Q) =
          aeval (a x) P * (f x * aeval (a x) Q) := by ring
      _ = aeval (a x) P * aeval (a x) Q' := by rw [hQ x]

theorem ideal_le_clearingIdeal (J : Ideal (MvPolynomial σ K))
    (a : X → zeroLocus K J) (f : X → K) :
    J ≤ clearingIdeal (fun x => (a x).val) f := by
  intro P hP
  refine ⟨0, ?_⟩
  intro x
  rw [(a x).property P hP, mul_zero, map_zero]

theorem local_fraction_clears [TopologicalSpace X]
    (J : Ideal (MvPolynomial σ K))
    (a : @Homeomorph X (zeroLocus K J) _ (AffineClosedPoints.locusTopology J))
    (f : X → K) (x : X)
    (hloc : ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ P Q : MvPolynomial σ K, ∀ z ∈ U,
        aeval (a z).val Q ≠ 0 ∧ f z = aeval (a z).val P / aeval (a z).val Q) :
    ∃ H ∈ clearingIdeal (fun z => (a z).val) f, aeval (a x).val H ≠ 0 := by
  let _ := AffineClosedPoints.locusTopology J
  obtain ⟨U, hU, hx, P, Q, hPQ⟩ := hloc
  have hopen : IsOpen (a.symm ⁻¹' U) := hU.preimage a.symm.continuous
  have hmem : a x ∈ a.symm ⁻¹' U := by simpa using hx
  obtain ⟨W, ⟨H, rfl⟩, hHx, hHU⟩ :=
    (AffineClosedPoints.nonzero_sets_basis J).isOpen_iff.mp hopen (a x) hmem
  have hin (z : X) (hz : aeval (a z).val H ≠ 0) : z ∈ U := by
    have h := hHU hz
    simpa using h
  refine ⟨H * Q, ⟨H * P, ?_⟩, ?_⟩
  · intro z
    simp only [map_mul]
    by_cases hHz : aeval (a z).val H = 0
    · simp [hHz]
    · obtain ⟨hQ, hf⟩ := hPQ z (hin z hHz)
      have heq := (eq_div_iff hQ).mp hf
      calc
        f z * (aeval (a z).val H * aeval (a z).val Q) =
            aeval (a z).val H * (f z * aeval (a z).val Q) := by ring
        _ = aeval (a z).val H * aeval (a z).val P := by rw [heq]
  · rw [map_mul]
    exact mul_ne_zero hHx (hPQ x hx).1

theorem eq_top_of_no_zero [IsAlgClosed K] [Finite σ]
    (J D : Ideal (MvPolynomial σ K)) (hJD : J ≤ D)
    (hnz : ∀ x : zeroLocus K J, ∃ P ∈ D, aeval x.val P ≠ 0) : D = ⊤ := by
  have hempty : zeroLocus K D = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxJ : x ∈ zeroLocus K J := zeroLocus_anti_mono hJD hx
    obtain ⟨P, hP, hnP⟩ := hnz ⟨x, hxJ⟩
    exact hnP (hx P hP)
  apply Ideal.radical_eq_top.mp
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := K), hempty, vanishingIdeal_empty]

theorem locally_rational_is_polynomial [IsAlgClosed K] [Finite σ] [TopologicalSpace X]
    (J : Ideal (MvPolynomial σ K))
    (a : @Homeomorph X (zeroLocus K J) _ (AffineClosedPoints.locusTopology J))
    (f : X → K)
    (hloc : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ P Q : MvPolynomial σ K, ∀ z ∈ U,
        aeval (a z).val Q ≠ 0 ∧ f z = aeval (a z).val P / aeval (a z).val Q) :
    ∃ P : MvPolynomial σ K, ∀ x, f x = aeval (a x).val P := by
  let _ := AffineClosedPoints.locusTopology J
  have hD : clearingIdeal (fun z => (a z).val) f = ⊤ := by
    apply eq_top_of_no_zero J _ (ideal_le_clearingIdeal J a f)
    intro y
    obtain ⟨P, hP, hnP⟩ := local_fraction_clears J a f (a.symm y) (hloc _)
    exact ⟨P, hP, by simpa using hnP⟩
  have hone : (1 : MvPolynomial σ K) ∈ clearingIdeal (fun z => (a z).val) f := by
    rw [hD]
    trivial
  obtain ⟨P, hP⟩ := hone
  exact ⟨P, fun x => by simpa using hP x⟩

end PhilipponMultiplicity.AffineRegularFunctions

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponAffineSchemeRealization

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity.AffineClosedPoints

open MvPolynomial AlgebraicGeometry CategoryTheory
open scoped Topology

universe u
variable {K : Type u} [Field K] {σ τ υ : Type}

theorem evaluation_ext [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (hI : I.IsRadical)
    {a b : MvPolynomial σ K ⧸ I}
    (h : ∀ x : zeroLocus K I, evaluation I x a = evaluation I x b) : a = b := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨Q, rfl⟩ := Ideal.Quotient.mk_surjective b
  apply sub_eq_zero.mp
  rw [← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  rw [← hI.radical, ← vanishingIdeal_zeroLocus_eq_radical (K := K)]
  intro x hx
  simpa only [map_sub, evaluation_mk] using sub_eq_zero.mpr (h ⟨x, hx⟩)

theorem algHom_ext [IsAlgClosed K] [Finite σ]
    (J : Ideal (MvPolynomial σ K)) (hJ : J.IsRadical)
    {A : Type u} [CommRing A] [Algebra K A]
    {φ ψ : A →ₐ[K] (MvPolynomial σ K ⧸ J)}
    (h : ∀ x a, evaluation J x (φ a) = evaluation J x (ψ a)) : φ = ψ := by
  ext a
  exact evaluation_ext J hJ (fun x => h x a)

def pointMap (I : Ideal (MvPolynomial τ K)) (J : Ideal (MvPolynomial σ K))
    (φ : (MvPolynomial τ K ⧸ I) →ₐ[K] (MvPolynomial σ K ⧸ J))
    (x : zeroLocus K J) : zeroLocus K I := by
  let v : τ → K := fun j => evaluation J x (φ (Ideal.Quotient.mk I (X j)))
  have hv : aeval v = ((evaluation J x).comp φ).comp (Ideal.Quotient.mkₐ K I) := by
    ext j
    simp [v]
  refine ⟨v, ?_⟩
  intro P hP
  rw [hv]
  simp [Ideal.Quotient.eq_zero_iff_mem.mpr hP]

@[simp] theorem pointMap_coordinate
    (I : Ideal (MvPolynomial τ K)) (J : Ideal (MvPolynomial σ K))
    (φ : (MvPolynomial τ K ⧸ I) →ₐ[K] (MvPolynomial σ K ⧸ J))
    (x : zeroLocus K J) (j : τ) :
    (pointMap I J φ x).val j = evaluation J x (φ (Ideal.Quotient.mk I (X j))) := rfl

@[simp] theorem evaluation_pointMap
    (I : Ideal (MvPolynomial τ K)) (J : Ideal (MvPolynomial σ K))
    (φ : (MvPolynomial τ K ⧸ I) →ₐ[K] (MvPolynomial σ K ⧸ J))
    (x : zeroLocus K J) (a : MvPolynomial τ K ⧸ I) :
    evaluation I (pointMap I J φ x) a = evaluation J x (φ a) := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
  have h : aeval (pointMap I J φ x).val =
      ((evaluation J x).comp φ).comp (Ideal.Quotient.mkₐ K I) := by
    ext j
    simp
  exact DFunLike.congr_fun h P

theorem pointMap_injective [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial τ K)) (J : Ideal (MvPolynomial σ K)) (hJ : J.IsRadical) :
    Function.Injective (pointMap I J) := by
  intro φ ψ h
  apply algHom_ext J hJ
  intro x a
  rw [← evaluation_pointMap I J φ, ← evaluation_pointMap I J ψ, h]

def IsLocallyRationalMap (I : Ideal (MvPolynomial τ K))
    (J : Ideal (MvPolynomial σ K)) (f : zeroLocus K J → zeroLocus K I) : Prop :=
  let _ := locusTopology J
  ∀ x j, ∃ U : Set (zeroLocus K J), IsOpen U ∧ x ∈ U ∧
    ∃ P Q : MvPolynomial σ K, ∀ z ∈ U,
      aeval z.val Q ≠ 0 ∧ (f z).val j = aeval z.val P / aeval z.val Q

theorem isLocallyRationalMap_iff_polynomial [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial τ K)) (J : Ideal (MvPolynomial σ K))
    (f : zeroLocus K J → zeroLocus K I) :
    IsLocallyRationalMap I J f ↔
      ∃ P : τ → MvPolynomial σ K, ∀ x j, (f x).val j = aeval x.val (P j) := by
  classical
  let _ := locusTopology J
  constructor
  · intro h
    have hex (j : τ) : ∃ P : MvPolynomial σ K,
        ∀ x : zeroLocus K J, (f x).val j = aeval x.val P :=
      AffineRegularFunctions.locally_rational_is_polynomial J (Homeomorph.refl _)
        (fun x => (f x).val j) (fun x => h x j)
    choose P hP using hex
    exact ⟨P, fun x j => hP j x⟩
  · rintro ⟨P, hP⟩ x j
    exact ⟨Set.univ, isOpen_univ, Set.mem_univ _, P j, 1, fun z _ => by simp [hP z j]⟩

theorem existsUnique_pullback [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial τ K)) (J : Ideal (MvPolynomial σ K)) (hJ : J.IsRadical)
    (f : zeroLocus K J → zeroLocus K I) (hf : IsLocallyRationalMap I J f) :
    ∃! φ : (MvPolynomial τ K ⧸ I) →ₐ[K] (MvPolynomial σ K ⧸ J),
      pointMap I J φ = f := by
  obtain ⟨P, hP⟩ := (isLocallyRationalMap_iff_polynomial I J f).mp hf
  refine ⟨quotientMap I J hJ f P hP, ?_, ?_⟩
  · funext x
    apply Subtype.ext
    funext j
    simp [hP x j]
  · intro φ hφ
    apply pointMap_injective I J hJ
    rw [hφ]
    funext x
    apply Subtype.ext
    funext j
    simp [hP x j]

def affineScheme (I : Ideal (MvPolynomial σ K)) : Scheme.{u} :=
  Spec (CommRingCat.of (MvPolynomial σ K ⧸ I))

def structureMap (I : Ideal (MvPolynomial σ K)) : affineScheme I ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial σ K ⧸ I)))

def schemeMap (I : Ideal (MvPolynomial τ K)) (J : Ideal (MvPolynomial σ K))
    (φ : (MvPolynomial τ K ⧸ I) →ₐ[K] (MvPolynomial σ K ⧸ J)) :
    affineScheme J ⟶ affineScheme I :=
  Spec.map (CommRingCat.ofHom φ.toRingHom)

@[simp] theorem schemeMap_over
    (I : Ideal (MvPolynomial τ K)) (J : Ideal (MvPolynomial σ K))
    (φ : (MvPolynomial τ K ⧸ I) →ₐ[K] (MvPolynomial σ K ⧸ J)) :
    schemeMap I J φ ≫ structureMap I = structureMap J := by
  rw [schemeMap, structureMap, ← Spec.map_comp]
  congr 1
  ext a
  exact φ.commutes a

theorem schemeMap_point
    (I : Ideal (MvPolynomial τ K)) (J : Ideal (MvPolynomial σ K))
    (φ : (MvPolynomial τ K ⧸ I) →ₐ[K] (MvPolynomial σ K ⧸ J))
    (x : zeroLocus K J) :
    schemeMap I J φ (point J x).toPrimeSpectrum =
      (point I (pointMap I J φ x)).toPrimeSpectrum := by
  apply PrimeSpectrum.ext
  ext a
  change evaluation J x (φ a) = 0 ↔ evaluation I (pointMap I J φ x) a = 0
  rw [evaluation_pointMap]

end PhilipponMultiplicity.AffineClosedPoints

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponAffineSchemeMaps

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity.AffineClosedPoints

open MvPolynomial AlgebraicGeometry CategoryTheory

universe u
variable {K : Type u} [Field K] {σ τ υ : Type}

def coordinateHom (I : Ideal (MvPolynomial τ K)) (J : Ideal (MvPolynomial σ K))
    (f : affineScheme J ⟶ affineScheme I)
    (hf : f ≫ structureMap I = structureMap J) :
    (MvPolynomial τ K ⧸ I) →ₐ[K] (MvPolynomial σ K ⧸ J) :=
  { (Spec.preimage f).hom with
    commutes' := fun a => by
      have h : CommRingCat.ofHom (algebraMap K (MvPolynomial τ K ⧸ I)) ≫
          Spec.preimage f = CommRingCat.ofHom (algebraMap K (MvPolynomial σ K ⧸ J)) := by
        apply Spec.map_injective
        rw [Spec.map_comp, Spec.map_preimage]
        exact hf
      exact ConcreteCategory.congr_hom h a }

@[simp] theorem schemeMap_coordinateHom
    (I : Ideal (MvPolynomial τ K)) (J : Ideal (MvPolynomial σ K))
    (f : affineScheme J ⟶ affineScheme I)
    (hf : f ≫ structureMap I = structureMap J) :
    schemeMap I J (coordinateHom I J f hf) = f := Spec.map_preimage f

theorem primePoint_injective (I : Ideal (MvPolynomial σ K)) :
    Function.Injective (fun x : zeroLocus K I => (point I x).toPrimeSpectrum) := by
  intro x y h
  apply point_injective I
  apply MaximalSpectrum.ext
  exact congrArg PrimeSpectrum.asIdeal h

theorem existsUnique_schemeRealization [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial τ K)) (J : Ideal (MvPolynomial σ K)) (hJ : J.IsRadical)
    (f : zeroLocus K J → zeroLocus K I) (hf : IsLocallyRationalMap I J f) :
    ∃! F : affineScheme J ⟶ affineScheme I,
      F ≫ structureMap I = structureMap J ∧
      ∀ x : zeroLocus K J,
        F (point J x).toPrimeSpectrum = (point I (f x)).toPrimeSpectrum := by
  obtain ⟨φ, hφ, huniq⟩ := existsUnique_pullback I J hJ f hf
  refine ⟨schemeMap I J φ, ⟨schemeMap_over I J φ, ?_⟩, ?_⟩
  · intro x
    rw [schemeMap_point, hφ]
  · intro F hF
    let ψ := coordinateHom I J F hF.1
    have hψ : pointMap I J ψ = f := by
      funext x
      apply primePoint_injective I
      change (point I (pointMap I J (coordinateHom I J F hF.1) x)).toPrimeSpectrum =
        (point I (f x)).toPrimeSpectrum
      rw [← schemeMap_point, schemeMap_coordinateHom]
      exact hF.2 x
    have heq := huniq ψ hψ
    rw [← schemeMap_coordinateHom I J F hF.1]
    exact congrArg (schemeMap I J) heq

end PhilipponMultiplicity.AffineClosedPoints

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectiveCoordinateScheme

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity.ProjectiveCoordinateScheme

open AlgebraicGeometry CategoryTheory MvPolynomial

universe u

theorem proj_isReduced {R S : Type*} [CommRing R] [SetLike S R] [AddSubgroupClass S R]
    (𝒜 : ℕ → S) [GradedRing 𝒜] [_root_.IsReduced R] : IsReduced (Proj 𝒜) := by
  have hcharts (i : (Proj.affineOpenCover 𝒜).I₀) :
      IsReduced ((Proj.affineOpenCover 𝒜).openCover.X i) := by
    letI : _root_.IsReduced (HomogeneousLocalization.Away 𝒜 (i.2 : R)) :=
      isReduced_of_injective
        (algebraMap (HomogeneousLocalization.Away 𝒜 (i.2 : R)) (Localization.Away (i.2 : R)))
        (HomogeneousLocalization.val_injective _)
    change IsReduced (Spec (.of (HomogeneousLocalization.Away 𝒜 (i.2 : R))))
    infer_instance
  letI := hcharts
  exact IsReduced.of_openCover _ (Proj.affineOpenCover 𝒜).openCover

variable {K : Type u} [Field K] {σ : Type}

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev grading (I : Ideal (MvPolynomial σ K)) : ℕ → Submodule K (MvPolynomial σ K ⧸ I) :=
  HomogeneousQuotientGrading.piece (homogeneousSubmodule σ K) I

local instance zeroAlgebra (I : Ideal (MvPolynomial σ K)) :
    Algebra (grading I 0) (MvPolynomial σ K ⧸ I) :=
  Algebra.ofSubsemiring (SetLike.GradeZero.subsemiring (grading I))

local instance zeroSMul (I : Ideal (MvPolynomial σ K)) :
    SMul (grading I 0) (MvPolynomial σ K ⧸ I) := (zeroAlgebra I).toSMul

def scheme (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) : Scheme.{u} := by
  letI := HomogeneousQuotientGrading.gradedAlgebra (homogeneousSubmodule σ K) I hI
  exact Proj (grading I)

theorem zero_algebraMap_surjective (I : Ideal (MvPolynomial σ K)) :
    Function.Surjective (algebraMap K (grading I 0)) := by
  rintro ⟨a, ha⟩
  obtain ⟨P, hP, hPa⟩ := ha
  have hC : P = C (P.coeff 0) := by
    exact (homogeneousComponent_of_mem hP).symm.trans (homogeneousComponent_zero _)
  refine ⟨P.coeff 0, Subtype.ext ?_⟩
  change Ideal.Quotient.mk I (C (P.coeff 0)) = a
  rw [← hC]
  exact hPa

def structureMap (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) : scheme I hI ⟶ Spec (.of K) := by
  letI := HomogeneousQuotientGrading.gradedAlgebra (homogeneousSubmodule σ K) I hI
  exact Proj.toSpecZero (grading I) ≫ Spec.map (CommRingCat.ofHom (algebraMap K (grading I 0)))

theorem finiteType_over_zero [Finite σ] (I : Ideal (MvPolynomial σ K)) :
    Algebra.FiniteType (grading I 0) (MvPolynomial σ K ⧸ I) := by
  letI : IsScalarTower K (grading I 0) (MvPolynomial σ K ⧸ I) :=
    IsScalarTower.of_algebraMap_eq (R := K) (S := grading I 0)
      (A := MvPolynomial σ K ⧸ I) (fun _ => rfl)
  letI : Algebra.FiniteType K (MvPolynomial σ K ⧸ I) :=
    Algebra.FiniteType.quotient K I
  exact Algebra.FiniteType.of_restrictScalars_finiteType K (grading I 0) (MvPolynomial σ K ⧸ I)

theorem structureMap_isProper [Finite σ] (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) : IsProper (structureMap I hI) := by
  letI := HomogeneousQuotientGrading.gradedAlgebra (homogeneousSubmodule σ K) I hI
  letI : Algebra.FiniteType (grading I 0) (MvPolynomial σ K ⧸ I) :=
    finiteType_over_zero I
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap K (grading I 0)))) :=
    IsClosedImmersion.spec_of_surjective _ (zero_algebraMap_surjective I)
  change IsProper (Proj.toSpecZero (grading I) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (grading I 0))))
  infer_instance

theorem scheme_isReduced (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (hred : I.IsRadical) :
    IsReduced (scheme I hI) := by
  letI := HomogeneousQuotientGrading.gradedAlgebra (homogeneousSubmodule σ K) I hI
  letI : _root_.IsReduced (MvPolynomial σ K ⧸ I) :=
    (Ideal.isRadical_iff_quotient_reduced I).mp hred
  exact proj_isReduced (grading I)

def chartIdeal (I : Ideal (MvPolynomial σ K)) (j : σ) : Ideal (MvPolynomial σ K) :=
  HomogeneousQuotientGrading.normalizedIdeal I (X j)

theorem chartIdeal_isRadical (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (hred : I.IsRadical) (j : σ) :
    (chartIdeal I j).IsRadical := by
  letI := HomogeneousQuotientGrading.gradedAlgebra (homogeneousSubmodule σ K) I hI
  exact HomogeneousQuotientGrading.normalizedIdeal_isRadical
    (homogeneousSubmodule σ K) I hred (isHomogeneous_X K j)

def chartIso (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (j : σ) :
    letI := HomogeneousQuotientGrading.gradedAlgebra (homogeneousSubmodule σ K) I hI
    (Proj.basicOpen (grading I) (Ideal.Quotient.mk I (X j))).toScheme ≅
      AffineClosedPoints.affineScheme (chartIdeal I j) := by
  letI := HomogeneousQuotientGrading.gradedAlgebra (homogeneousSubmodule σ K) I hI
  exact HomogeneousQuotientGrading.normalizedSchemeIso
    (homogeneousSubmodule σ K) I (isHomogeneous_X K j)

theorem coordinates_generate (I : Ideal (MvPolynomial σ K)) :
    Algebra.adjoin (grading I 0) (Set.range (fun j : σ => Ideal.Quotient.mk I (X j))) = ⊤ := by
  apply top_unique
  intro a ha
  clear ha
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
  induction P using MvPolynomial.induction_on with
  | C a =>
      exact (Algebra.adjoin (grading I 0) _).algebraMap_mem (algebraMap K (grading I 0) a)
  | add P Q hP hQ =>
      simpa only [map_add] using add_mem hP hQ
  | mul_X P j hP =>
      simpa only [map_mul] using mul_mem hP (Algebra.subset_adjoin (Set.mem_range_self j))

def chartOpen (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (j : σ) : (scheme I hI).Opens := by
  letI := HomogeneousQuotientGrading.gradedAlgebra (homogeneousSubmodule σ K) I hI
  exact Proj.basicOpen (grading I) (Ideal.Quotient.mk I (X j))

theorem iSup_chartOpen (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) : (⨆ j, chartOpen I hI j) = ⊤ := by
  letI := HomogeneousQuotientGrading.gradedAlgebra (homogeneousSubmodule σ K) I hI
  apply Proj.iSup_basicOpen_eq_top'
  · intro j
    exact ⟨1, HomogeneousQuotientGrading.quotient_mem_piece
      (homogeneousSubmodule σ K) I (isHomogeneous_X K j)⟩
  · exact coordinates_generate I

def chartImmersion (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (j : σ) :
    AffineClosedPoints.affineScheme (chartIdeal I j) ⟶ scheme I hI :=
  (chartIso I hI j).inv ≫ (chartOpen I hI j).ι

theorem chartImmersion_isOpenImmersion (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (j : σ) :
    IsOpenImmersion (chartImmersion I hI j) := by
  unfold chartImmersion
  infer_instance

theorem chartImmersion_opensRange (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (j : σ) :
    letI := chartImmersion_isOpenImmersion I hI j
    (chartImmersion I hI j).opensRange = chartOpen I hI j := by
  letI := chartImmersion_isOpenImmersion I hI j
  exact (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (chartOpen I hI j).opensRange_ι

theorem chartImmersion_over (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (j : σ) :
    chartImmersion I hI j ≫ structureMap I hI =
      AffineClosedPoints.structureMap (chartIdeal I j) := by
  letI := HomogeneousQuotientGrading.gradedAlgebra (homogeneousSubmodule σ K) I hI
  let e := HomogeneousQuotientGrading.normalizedRingEquiv
    (homogeneousSubmodule σ K) I (isHomogeneous_X K j)
  have he : chartImmersion I hI j = Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Proj.awayι (grading I) (Ideal.Quotient.mk I (X j))
        (HomogeneousQuotientGrading.quotient_mem_piece
          (homogeneousSubmodule σ K) I (isHomogeneous_X K j)) (by decide) := rfl
  rw [he]
  change (_ ≫ _) ≫ (Proj.toSpecZero (grading I) ≫ _) = _
  rw [Category.assoc, ← Category.assoc (Proj.awayι _ _ _ _), Proj.awayι_toSpecZero,
    ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext a
  change e (HomogeneousLocalization.fromZeroRingHom (grading I) _
    (algebraMap K (grading I 0) a)) = Ideal.Quotient.mk (chartIdeal I j) (C a)
  exact HomogeneousQuotientGrading.normalizedRingEquiv_mk
    (homogeneousSubmodule σ K) I (isHomogeneous_X K j) 0 (C a) (isHomogeneous_C σ a)

end PhilipponMultiplicity.ProjectiveCoordinateScheme

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectiveQuotientImmersion

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section

namespace PhilipponMultiplicity.ProjectiveCoordinateScheme
open AlgebraicGeometry CategoryTheory MvPolynomial
open HomogeneousLocalization HomogeneousIdeal
open Topology
universe u

section LocalSurjectivity
variable {R S σ τ : Type u} [CommRing R] [CommRing S]
    [SetLike σ R] [AddSubgroupClass σ R] [SetLike τ S] [AddSubgroupClass τ S]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

theorem localRingHom_surjective (f : 𝒜 →+*ᵍ ℬ)
    (hf : ∀ n y, y ∈ ℬ n → ∃ x, x ∈ 𝒜 n ∧ f x = y)
    (J : Ideal S) [J.IsPrime] :
    Function.Surjective (HomogeneousLocalization.localRingHom f (J.comap f) J rfl) := by
  intro z
  obtain ⟨⟨n, ⟨a, ha⟩, ⟨b, hb⟩, hJ⟩, rfl⟩ := z.mk_surjective
  obtain ⟨a', ha', rfl⟩ := hf n a ha
  obtain ⟨b', hb', rfl⟩ := hf n b hb
  refine ⟨HomogeneousLocalization.mk ⟨n, ⟨a', ha'⟩, ⟨b', hb'⟩, hJ⟩, ?_⟩
  rw [HomogeneousLocalization.localRingHom, HomogeneousLocalization.map_mk]

end LocalSurjectivity

variable {K : Type u} [Field K] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

def quotientGradedMap (I : Ideal (MvPolynomial σ K)) :
    homogeneousSubmodule σ K →+*ᵍ grading I where
  __ := Ideal.Quotient.mk I
  map_mem hx := ⟨_, hx, rfl⟩

theorem quotientGradedMap_irrelevant (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) :
    letI := HomogeneousQuotientGrading.gradedAlgebra (homogeneousSubmodule σ K) I hI
    (grading I)₊ ≤ (homogeneousSubmodule σ K)₊.map (quotientGradedMap I) := by
  letI := HomogeneousQuotientGrading.gradedAlgebra (homogeneousSubmodule σ K) I hI
  rw [HomogeneousIdeal.irrelevant_le]
  intro n hn a ha
  obtain ⟨P, hP, rfl⟩ := ha
  exact Ideal.mem_map_of_mem (quotientGradedMap I)
    (HomogeneousIdeal.mem_irrelevant_of_mem _ hn hP)

def quotientMap (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) :
    scheme I hI ⟶ Proj (homogeneousSubmodule σ K) := by
  letI := HomogeneousQuotientGrading.gradedAlgebra (homogeneousSubmodule σ K) I hI
  exact Proj.map (quotientGradedMap I) (quotientGradedMap_irrelevant I hI)

def polynomialStructureMap : Proj (homogeneousSubmodule σ K) ⟶ Spec (.of K) :=
  Proj.toSpecZero (homogeneousSubmodule σ K) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (homogeneousSubmodule σ K 0)))

theorem quotientMap_over (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) :
    quotientMap I hI ≫ polynomialStructureMap = structureMap I hI := by
  letI := HomogeneousQuotientGrading.gradedAlgebra (homogeneousSubmodule σ K) I hI
  let f := quotientGradedMap I
  let hf := quotientGradedMap_irrelevant I hI
  apply (Proj.mapAffineOpenCover f hf).openCover.hom_ext
  intro s
  change Proj.awayι (grading I) (f s.2) _ _ ≫
      (Proj.map f hf ≫ (Proj.toSpecZero (homogeneousSubmodule σ K) ≫ _)) =
    Proj.awayι (grading I) (f s.2) _ _ ≫ (Proj.toSpecZero (grading I) ≫ _)
  rw [Proj.awayι_comp_map_assoc f hf s.1.2 _ s.2.2,
    ← Category.assoc (Proj.awayι _ _ _ _), Proj.awayι_toSpecZero,
    ← Category.assoc (Proj.awayι _ _ _ _), Proj.awayι_toSpecZero,
    ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext a
  rfl

theorem quotientMap_injective (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) :
    Function.Injective (quotientMap I hI) := by
  letI := HomogeneousQuotientGrading.gradedAlgebra (homogeneousSubmodule σ K) I hI
  intro p q hpq
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext
  apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  exact congrArg (fun x => x.asHomogeneousIdeal.toIdeal) hpq

theorem quotientMap_surjectiveOnStalks (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) :
    SurjectiveOnStalks (quotientMap I hI) := by
  letI := HomogeneousQuotientGrading.gradedAlgebra (homogeneousSubmodule σ K) I hI
  refine ⟨fun p => ?_⟩
  change Function.Surjective ((Proj.sheafedSpaceMap (quotientGradedMap I)
    (quotientGradedMap_irrelevant I hI)).hom.stalkMap p).hom
  rw [← Proj.localRingHom_comp_stalkIso]
  exact ((ConcreteCategory.bijective_of_isIso (Proj.stalkIso _ p).inv).2.comp
    (localRingHom_surjective (quotientGradedMap I) (fun n y hy => hy) _)).comp
    (ConcreteCategory.bijective_of_isIso (Proj.stalkIso _ _).hom).2

theorem quotientMap_isClosedImmersion [Finite σ] (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) :
    IsClosedImmersion (quotientMap I hI) := by
  letI := quotientMap_surjectiveOnStalks I hI
  letI : IsProper (quotientMap I hI ≫ polynomialStructureMap) :=
    quotientMap_over I hI ▸ structureMap_isProper I hI
  letI : IsSeparated (polynomialStructureMap (K := K) (σ := σ)) := by
    unfold polynomialStructureMap
    infer_instance
  letI := IsProper.of_comp (quotientMap I hI) polynomialStructureMap
  refine ⟨?_⟩
  exact IsClosedEmbedding.of_continuous_injective_isClosedMap
    (quotientMap I hI).continuous (quotientMap_injective I hI)
    (quotientMap I hI).isClosedMap

end PhilipponMultiplicity.ProjectiveCoordinateScheme

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectiveGeometry

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity
universe u
namespace MultiProjectiveSpace

variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem IsHomogeneous.mul {P Q : M.CoordinateRing} {D E : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q E) :
    M.IsHomogeneous (P * Q) (D + E) := by
  classical
  intro d hd i
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hd)
  simpa only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hP a ha i,
    hQ b hb i]

theorem isHomogeneous_one : M.IsHomogeneous 1 0 := by
  classical
  intro d hd i
  have hd0 : d = 0 := by simpa using hd
  simp [hd0]

theorem isOpen_basic (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) :
    @IsOpen _ M.zariskiTopology {x | M.eval P x ≠ 0} := by
  exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨P, D, hP, rfl⟩

theorem isClosed_zero (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) :
    @IsClosed _ M.zariskiTopology {x | M.eval P x = 0} := by
  letI := M.zariskiTopology
  simpa only [Set.compl_setOf, not_not] using (M.isOpen_basic P D hP).isClosed_compl

theorem isTopologicalBasis_basic :
    @TopologicalSpace.IsTopologicalBasis _ M.zariskiTopology
      {U | ∃ P : M.CoordinateRing, ∃ D, M.IsHomogeneous P D ∧
        U = {x | M.eval P x ≠ 0}} := by
  classical
  letI := M.zariskiTopology
  have h := TopologicalSpace.isTopologicalBasis_of_subbasis_of_inter
    (show M.zariskiTopology = TopologicalSpace.generateFrom _ from rfl) (by
      rintro U ⟨P, D, hP, rfl⟩ V ⟨Q, E, hQ, rfl⟩
      refine ⟨P * Q, D + E, hP.mul M hQ, ?_⟩
      ext x
      simp [eval, mul_ne_zero_iff])
  have huniv : Set.univ ∈ {U | ∃ P : M.CoordinateRing, ∃ D,
      M.IsHomogeneous P D ∧ U = {x | M.eval P x ≠ 0}} := by
    refine ⟨1, 0, M.isHomogeneous_one, ?_⟩
    ext x
    simp [eval]
  simpa only [Set.insert_eq_of_mem huniv] using h

theorem eval_eq_zero_of_mem_vanishingIdeal {S : Set M.Point}
    {P : M.CoordinateRing} (hP : P ∈ M.vanishingIdeal S)
    {x : M.Point} (hx : x ∈ S) : M.eval P x = 0 := by
  have hle : M.vanishingIdeal S ≤ RingHom.ker (MvPolynomial.eval (M.coordinate x)) := by
    apply Ideal.span_le.mpr
    rintro Q ⟨_, hQ⟩
    exact hQ x hx
  exact hle hP

theorem vanishingIdeal_antitone {S T : Set M.Point} (h : S ⊆ T) :
    M.vanishingIdeal T ≤ M.vanishingIdeal S := by
  apply Ideal.span_mono
  rintro P ⟨hP, hz⟩
  exact ⟨hP, fun x hx => hz x (h hx)⟩

theorem isClosed_zeroLocus_vanishingIdeal (S : Set M.Point) :
    @IsClosed _ M.zariskiTopology (M.zeroLocus (M.vanishingIdeal S)) := by
  letI := M.zariskiTopology
  have hset : M.zeroLocus (M.vanishingIdeal S) =
      ⋂ P : {P : M.CoordinateRing // (∃ D, M.IsHomogeneous P D) ∧
        ∀ x ∈ S, M.eval P x = 0}, {x | M.eval P.val x = 0} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq, zeroLocus]
    constructor
    · intro hx P
      exact hx P (Ideal.subset_span P.property)
    · intro hx P hP
      have hle : M.vanishingIdeal S ≤ RingHom.ker (MvPolynomial.eval (M.coordinate x)) := by
        apply Ideal.span_le.mpr
        intro Q hQ
        exact hx ⟨Q, hQ⟩
      exact hle hP
  rw [hset]
  apply isClosed_iInter
  intro P
  obtain ⟨D, hD⟩ := P.property.1
  exact M.isClosed_zero P.val D hD

theorem zeroLocus_vanishingIdeal_eq_closure (S : Set M.Point) :
    M.zeroLocus (M.vanishingIdeal S) = @closure _ M.zariskiTopology S := by
  letI := M.zariskiTopology
  apply Set.Subset.antisymm
  · intro x hx
    apply M.isTopologicalBasis_basic.mem_closure_iff.mpr
    rintro U ⟨P, D, hP, rfl⟩ hxU
    by_contra hn
    have hPS : ∀ y ∈ S, M.eval P y = 0 := by
      intro y hy
      by_contra hp
      exact hn ⟨y, hp, hy⟩
    exact hxU (hx P (Ideal.subset_span ⟨⟨D, hP⟩, hPS⟩))
  · apply closure_minimal
    · intro x hx P hP
      exact M.eval_eq_zero_of_mem_vanishingIdeal hP hx
    · exact M.isClosed_zeroLocus_vanishingIdeal S

end MultiProjectiveSpace

end PhilipponMultiplicity

namespace WeierstrassEllipticZeta
open PhilipponMultiplicity

end WeierstrassEllipticZeta
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponPointHilbert

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem blockWeight_apply (d : M.Variable →₀ ℕ) (i : M.FactorIndex) :
    (Finsupp.weight (Hilbert.blockWeight M.factorCount M.ambientDimension) d) i =
      ∑ j : Fin (M.ambientDimension i + 1), d ⟨i, j⟩ := by
  classical
  rw [Finsupp.weight_eq_sum, Fintype.sum_sigma]
  change (∑ b : M.FactorIndex,
    ∑ j : Fin (M.ambientDimension b + 1),
      d ⟨b, j⟩ • Hilbert.blockWeight M.factorCount M.ambientDimension ⟨b, j⟩) i = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Hilbert.blockWeight,
    Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b hb hbi
    simp [Ne.symm hbi]
  · simp

theorem degreePiece_iff (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) :
    P ∈ Hilbert.degreePiece K M.factorCount M.ambientDimension D ↔ M.IsHomogeneous P D := by
  change (∀ d, coeff d P ≠ 0 →
    Finsupp.weight (Hilbert.blockWeight M.factorCount M.ambientDimension) d = D) ↔ _
  simp only [← mem_support_iff]
  constructor
  · intro h d hd i
    exact (M.blockWeight_apply d i).symm.trans (congrFun (h d hd) i)
  · intro h d hd
    funext i
    rw [M.blockWeight_apply]
    exact h d hd i

theorem exists_form_nonzero_at (p : M.Point) (D : M.FactorIndex → ℕ) :
    ∃ Q : M.CoordinateRing, M.IsHomogeneous Q D ∧ M.eval Q p ≠ 0 := by
  classical
  have hj (i : M.FactorIndex) : ∃ j, (p i).rep j ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using
      (Projectivization.rep_nonzero (p i))
  choose j hj using hj
  let d : M.Variable →₀ ℕ := Finsupp.equivFunOnFinite.symm
    (fun v => if v.2 = j v.1 then D v.1 else 0)
  refine ⟨monomial d 1, ?_, ?_⟩
  · intro m hm i
    have hm' : m = d := Finset.mem_singleton.mp (support_monomial_subset hm)
    subst m
    simp [d]
  · change MvPolynomial.eval (M.coordinate p) (monomial d 1) ≠ 0
    rw [eval_monomial]
    simp only [one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    apply Finset.prod_ne_zero_iff.mpr
    intro v _
    dsimp [d]
    split_ifs with h
    · apply pow_ne_zero
      change (p v.1).rep v.2 ≠ 0
      rw [h]
      exact hj v.1
    · simp

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity
end PhilipponMultiplicity
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectiveContact

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity

theorem MultiProjectiveSpace.eval_block_scale {K : Type*} [Field K]
    (M : MultiProjectiveSpace K) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (v : M.Variable → K) (a : M.FactorIndex → K) :
    MvPolynomial.eval (fun j => a j.1 * v j) P = (∏ i, a i ^ D i) * MvPolynomial.eval v P := by
  classical
  rw [eval_eq', eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hscale : (∏ j : M.Variable, a j.1 ^ d j) = ∏ i, a i ^ D i := by
    rw [Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro i _
    change (∏ j : Fin (M.ambientDimension i + 1), a i ^ d ⟨i, j⟩) = a i ^ D i
    rw [Finset.prod_pow_eq_pow_sum, hP d hd i]
  simp only [mul_pow, Finset.prod_mul_distrib, hscale]
  ring

end PhilipponMultiplicity
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponAdditiveSubgroups

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity

theorem MultiProjectiveSpace.eval_eq_zero_iff_of_lift
    {K : Type*} [Field K] (M : MultiProjectiveSpace K) (p : M.Point)
    (v : M.Variable → K)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i, j⟩) h = p i)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D) :
    MvPolynomial.eval v P = 0 ↔ M.eval P p = 0 := by
  classical
  have ha (i : M.FactorIndex) : ∃ a : Kˣ,
      ∀ j, v ⟨i, j⟩ = (a : K) * (p i).rep j := by
    obtain ⟨h, he⟩ := hv i
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ h
      (Projectivization.rep_nonzero (p i))).mp
      (he.trans (Projectivization.mk_rep (p i)).symm)
    refine ⟨a, fun j => ?_⟩
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha j).symm
  choose a ha using ha
  have hv' : v = fun j => (a j.1 : K) * M.coordinate p j := by
    funext j
    exact ha j.1 j.2
  have hne : (∏ i, (a i : K) ^ D i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (a i).ne_zero)
  rw [hv', M.eval_block_scale P D hP (M.coordinate p) (fun i => (a i : K))]
  exact mul_eq_zero.trans (or_iff_right hne)

end PhilipponMultiplicity
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponHomogeneousOperations

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem isHomogeneous_X (v : M.Variable) :
    M.IsHomogeneous (MvPolynomial.X v) (fun i => if i = v.1 then 1 else 0) := by
  classical
  intro a ha i
  simp only [MvPolynomial.support_X, Finset.mem_singleton] at ha
  subst a
  rcases v with ⟨b, j⟩
  by_cases hi : i = b
  · subst i
    simp [Finsupp.single_apply, Sigma.mk.inj_iff]
  · have hn (k : Fin (M.ambientDimension i + 1)) :
        (⟨b, j⟩ : M.Variable) ≠ ⟨i, k⟩ := by
      intro h
      exact hi (congrArg Sigma.fst h).symm
    simp [Finsupp.single_apply, hi, hn]

theorem isHomogeneous_C (c : K) : M.IsHomogeneous (MvPolynomial.C c) 0 := by
  classical
  intro a ha i
  have ha0 : a = 0 := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ha)
  simp [ha0]

theorem IsHomogeneous.add {P Q : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q D) :
    M.IsHomogeneous (P + Q) D := by
  classical
  intro a ha i
  rcases Finset.mem_union.mp (MvPolynomial.support_add ha) with h | h
  · exact hP a h i
  · exact hQ a h i

theorem IsHomogeneous.neg {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) : M.IsHomogeneous (-P) D := by
  intro a ha i
  exact hP a (by simpa only [MvPolynomial.support_neg] using ha) i

theorem IsHomogeneous.sub {P Q : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q D) :
    M.IsHomogeneous (P - Q) D := by
  simpa only [sub_eq_add_neg] using hP.add M (hQ.neg M)

theorem IsHomogeneous.C_mul {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (c : K) : M.IsHomogeneous (MvPolynomial.C c * P) D := by
  simpa only [zero_add] using (M.isHomogeneous_C c).mul M hP

theorem IsHomogeneous.pow {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (n : ℕ) :
    M.IsHomogeneous (P ^ n) (fun i => n * D i) := by
  induction n with
  | zero =>
    convert M.isHomogeneous_one using 1
    · simp
    · funext i; simp
  | succ n ih =>
    convert ih.mul M hP using 1
    · exact pow_succ P n
    · funext i; simp [Nat.succ_mul]

end PhilipponMultiplicity.MultiProjectiveSpace
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponRegularMapTopology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open MvPolynomial Set
open scoped BigOperators Topology

namespace PhilipponMultiplicity.MultiProjectiveSpace
universe u
variable {K : Type u} [Field K]

theorem isHomogeneous_zero (M : MultiProjectiveSpace K) (D : M.FactorIndex → ℕ) :
    M.IsHomogeneous 0 D := by simp [IsHomogeneous]

theorem isHomogeneous_sum (M : MultiProjectiveSpace K) {ι : Type*}
    (s : Finset ι) (P : ι → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : ∀ i ∈ s, M.IsHomogeneous (P i) D) :
    M.IsHomogeneous (∑ i ∈ s, P i) D := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using M.isHomogeneous_zero D
  | @insert i s hi ih =>
    simp only [Finset.sum_insert, hi, not_false_eq_true]
    exact (hP i (by simp)).add M (ih (fun j hj => hP j (by simp [hj])))

theorem isHomogeneous_prod (M : MultiProjectiveSpace K) {ι : Type*}
    (s : Finset ι) (P : ι → M.CoordinateRing) (D : ι → M.FactorIndex → ℕ)
    (hP : ∀ i ∈ s, M.IsHomogeneous (P i) (D i)) :
    M.IsHomogeneous (∏ i ∈ s, P i) (∑ i ∈ s, D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using M.isHomogeneous_one
  | @insert i s hi ih =>
    simp only [Finset.prod_insert, Finset.sum_insert, hi, not_false_eq_true]
    exact (hP i (by simp)).mul M (ih (fun j hj => hP j (by simp [hj])))

theorem IsHomogeneous.eval₂_blocks (M N : MultiProjectiveSpace K)
    {Q : N.CoordinateRing} {D : N.FactorIndex → ℕ} (hQ : N.IsHomogeneous Q D)
    (P : N.Variable → M.CoordinateRing) (E : N.FactorIndex → M.FactorIndex → ℕ)
    (hP : ∀ j, M.IsHomogeneous (P j) (E j.1)) :
    M.IsHomogeneous (eval₂ C P Q) (fun i => ∑ b, D b * E b i) := by
  classical
  rw [eval₂_eq']
  apply M.isHomogeneous_sum
  intro d hd
  have hh := M.isHomogeneous_prod Finset.univ (fun j => P j ^ d j)
    (fun j i => d j * E j.1 i) (fun j _ => (hP j).pow M (d j))
  have he : (∑ j : N.Variable, fun i => d j * E j.1 i) =
      (fun i => ∑ b, D b * E b i) := by
    funext i
    simp only [Finset.sum_apply]
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro b _
    change (∑ y, d ⟨b, y⟩ * E b i) = D b * E b i
    rw [← Finset.sum_mul, hQ d hd b]
  rw [he] at hh
  exact hh.C_mul M _

theorem IsRegularAlong.continuous
    {X : Type u} (M N : MultiProjectiveSpace K)
    {e : X → M.Point} {f : X → N.Point} (hf : M.IsRegularAlong N e f) :
    @Continuous X N.Point (TopologicalSpace.induced e M.zariskiTopology)
      N.zariskiTopology f := by
  classical
  let := M.zariskiTopology
  let := TopologicalSpace.induced e M.zariskiTopology
  apply continuous_generateFrom_iff.mpr
  rintro _ ⟨R, D, hR, rfl⟩
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  choose U hU hxU E P hP hlift using hf x
  let pull := eval₂ C (fun j : N.Variable => P j.1 j.2) R
  have hpull : M.IsHomogeneous pull (fun i => ∑ b, D b * E b i) :=
    hR.eval₂_blocks M N _ E (fun j => hP j.1 j.2)
  have heval (y : X) : M.eval pull (e y) =
      MvPolynomial.eval (fun j : N.Variable => M.eval (P j.1 j.2) (e y)) R := by
    dsimp only [eval, pull]
    rw [← eval_assoc]
    rfl
  have hiff (y : X) (hy : ∀ b, e y ∈ U b) :
      M.eval pull (e y) = 0 ↔ N.eval R (f y) = 0 := by
    rw [heval]
    exact N.eval_eq_zero_iff_of_lift (f y) _ (fun b => hlift b y (hy b)) R D hR
  let W : Set M.Point := (⋂ b, U b) ∩ {p | M.eval pull p ≠ 0}
  have hW : IsOpen (e ⁻¹' W) :=
    ((isOpen_iInter_of_finite hU).inter (M.isOpen_basic _ _ hpull)).preimage
      continuous_induced_dom
  have hxW : x ∈ e ⁻¹' W := ⟨Set.mem_iInter.mpr hxU, (hiff x hxU).not.mpr hx⟩
  refine Filter.mem_of_superset (hW.mem_nhds hxW) ?_
  intro y hy
  exact (hiff y (Set.mem_iInter.mp hy.1)).not.mp hy.2

theorem IsRegularAlong.comp_domain
    {X Y : Type u} {M N : MultiProjectiveSpace K}
    {e : X → M.Point} {f : X → N.Point} (hf : M.IsRegularAlong N e f) (g : Y → X) :
    M.IsRegularAlong N (e ∘ g) (f ∘ g) := by
  intro y b
  obtain ⟨U, hU, hy, D, P, hP, hl⟩ := hf (g y) b
  exact ⟨U, hU, hy, D, P, hP, fun z hz => hl (g z) hz⟩

end PhilipponMultiplicity.MultiProjectiveSpace
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProductHilbert

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem homogeneous_total {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) : P.IsHomogeneous (∑ i, D i) := by
  intro a ha
  change (Finsupp.weight (fun _ : M.Variable => (1 : ℕ))) a = _
  rw [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum, Fintype.sum_sigma]
  exact Finset.sum_congr rfl (fun i _ => hP a (mem_support_iff.mpr ha) i)

instance degreePiece_finite (D : M.FactorIndex → ℕ) :
    Module.Finite K (Hilbert.degreePiece K M.factorCount M.ambientDimension D) := by
  let W := MvPolynomial.homogeneousSubmodule M.Variable K (∑ i, D i)
  letI : Module.Finite K W := Module.Finite.of_fg
    (MvPolynomial.homogeneousSubmodule_fg _ _ _)
  have hle : Hilbert.degreePiece K M.factorCount M.ambientDimension D ≤ W := by
    intro P hP
    exact M.homogeneous_total ((M.degreePiece_iff P D).mp hP)
  exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity
open SectionThree

end PhilipponMultiplicity

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponSegreVeronesePieces

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

def blockLinearSpace (i : M.FactorIndex) : Submodule K M.CoordinateRing :=
  Submodule.span K (Set.range (fun j : Fin (M.ambientDimension i + 1) => X ⟨i,j⟩))

def blockProductSpace (D : M.FactorIndex → ℕ) : Submodule K M.CoordinateRing :=
  ∏ i, M.blockLinearSpace i ^ D i

theorem blockProductSpace_add (D E : M.FactorIndex → ℕ) :
    M.blockProductSpace (D + E) = M.blockProductSpace D * M.blockProductSpace E := by
  simp [blockProductSpace, pow_add, Finset.prod_mul_distrib]

theorem blockProductSpace_single (i : M.FactorIndex) (n : ℕ) :
    M.blockProductSpace (Pi.single i n) = M.blockLinearSpace i ^ n := by
  classical
  simp [blockProductSpace, Pi.single_apply]

theorem monomial_mem_blockProductSpace (e : M.Variable →₀ ℕ) (c : K) :
    monomial e c ∈ M.blockProductSpace
      (Finsupp.weight (Hilbert.blockWeight M.factorCount M.ambientDimension) e) := by
  classical
  induction e using Finsupp.induction with
  | zero => simp [blockProductSpace]
  | single_add v n e hv hn ih =>
    rw [map_add, Finsupp.weight_single, blockProductSpace_add, monomial_single_add]
    have he : n • Hilbert.blockWeight M.factorCount M.ambientDimension v = Pi.single v.1 n := by
      ext i
      simp [Hilbert.blockWeight, Pi.single_apply]
    rw [he, blockProductSpace_single]
    exact Submodule.mul_mem_mul (Submodule.pow_mem_pow _
      (Submodule.subset_span (Set.mem_range_self v.2)) n) ih

theorem degreePiece_pow_le (D : M.FactorIndex → ℕ) (n : ℕ) :
    (Hilbert.degreePiece K M.factorCount M.ambientDimension D) ^ n ≤
      Hilbert.degreePiece K M.factorCount M.ambientDimension (n • D) := by
  induction n with
  | zero =>
    simp only [pow_zero, zero_nsmul]
    exact Submodule.one_le.mpr (MvPolynomial.isWeightedHomogeneous_one K _)
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact (mul_le_mul' ih le_rfl).trans
      (MvPolynomial.weightedHomogeneousSubmodule_mul _ _ _)

theorem blockProductSpace_le_degreePiece (D : M.FactorIndex → ℕ) :
    M.blockProductSpace D ≤ Hilbert.degreePiece K M.factorCount M.ambientDimension D := by
  classical
  have hblock (i : M.FactorIndex) : M.blockLinearSpace i ≤
      Hilbert.degreePiece K M.factorCount M.ambientDimension (Pi.single i 1) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    have he : (Pi.single i 1 : M.FactorIndex → ℕ) = fun k => if k = i then 1 else 0 := by
      ext k
      simp [Pi.single_apply]
    rw [he]
    exact (M.degreePiece_iff _ _).mpr (M.isHomogeneous_X ⟨i,j⟩)
  have hpow (i : M.FactorIndex) : M.blockLinearSpace i ^ D i ≤
      Hilbert.degreePiece K M.factorCount M.ambientDimension (Pi.single i (D i)) := by
    have h := (pow_le_pow_left' (hblock i) (D i)).trans (M.degreePiece_pow_le _ _)
    have he : D i • (Pi.single i 1 : M.FactorIndex → ℕ) = Pi.single i (D i) := by
      ext j
      simp [Pi.single_apply]
    rw [he] at h
    exact h
  have hprod (s : Finset M.FactorIndex) : (∏ i ∈ s, M.blockLinearSpace i ^ D i) ≤
      Hilbert.degreePiece K M.factorCount M.ambientDimension (∑ i ∈ s, Pi.single i (D i)) := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty]
      exact Submodule.one_le.mpr (MvPolynomial.isWeightedHomogeneous_one K _)
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      exact (mul_le_mul' (hpow i) ih).trans
        (MvPolynomial.weightedHomogeneousSubmodule_mul _ _ _)
  have hsum : (∑ i, Pi.single i (D i)) = D := by
    ext j
    simp [Pi.single_apply]
  simpa only [hsum, blockProductSpace] using hprod Finset.univ

theorem degreePiece_eq_blockProductSpace (D : M.FactorIndex → ℕ) :
    Hilbert.degreePiece K M.factorCount M.ambientDimension D = M.blockProductSpace D := by
  apply le_antisymm _ (M.blockProductSpace_le_degreePiece D)
  intro P hP
  rw [P.as_sum]
  apply Submodule.sum_mem
  intro e he
  have heD := hP (MvPolynomial.mem_support_iff.mp he)
  rw [← heD]
  exact M.monomial_mem_blockProductSpace e _

theorem degreePiece_diagonal_pow (D : M.FactorIndex → ℕ) (n : ℕ) :
    (Hilbert.degreePiece K M.factorCount M.ambientDimension D) ^ n =
      Hilbert.degreePiece K M.factorCount M.ambientDimension (fun i => n * D i) := by
  rw [M.degreePiece_eq_blockProductSpace, M.degreePiece_eq_blockProductSpace]
  change (∏ i, M.blockLinearSpace i ^ D i) ^ n = ∏ i, M.blockLinearSpace i ^ (n * D i)
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  rw [← pow_mul, mul_comm]

end PhilipponMultiplicity.MultiProjectiveSpace

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponFixedFactorHilbert

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace

variable {K : Type*} [Field K] (N : ℕ)

theorem projective_homogeneous_iff (P : (projectiveSpace K N).CoordinateRing) (n : ℕ) :
    (projectiveSpace K N).IsHomogeneous P (fun _ => n) ↔ P.IsHomogeneous n := by
  classical
  change (∀ d ∈ P.support, ∀ i : Fin 1, ∑ j : Fin (N + 1), d ⟨i, j⟩ = n) ↔ _
  constructor
  · intro h d hd
    rw [Finsupp.weight_eq_sum, Fintype.sum_sigma]
    change (∑ i : Fin 1, ∑ j : Fin (N + 1), d ⟨i, j⟩ • (1 : ℕ)) = n
    simpa [Fin.sum_univ_one] using h d (mem_support_iff.mpr hd) (0 : Fin 1)
  · intro h d hd i
    change Fin 1 at i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    have hh := h (mem_support_iff.mp hd)
    rw [Finsupp.weight_eq_sum, Fintype.sum_sigma] at hh
    change (∑ i : Fin 1, ∑ j : Fin (N + 1), d ⟨i, j⟩ • (1 : ℕ)) = n at hh
    simpa [Fin.sum_univ_one] using hh

end PhilipponMultiplicity.MultiProjectiveSpace

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponSegreVeroneseHilbert

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K]

theorem ordinary_degreePiece_eq (N n : ℕ) :
    degreePiece K 1 (fun _ => N) (fun _ => n) =
      homogeneousSubmodule (projectiveSpace K N).Variable K n := by
  ext P
  exact ((projectiveSpace K N).degreePiece_iff P _).trans
    (MultiProjectiveSpace.projective_homogeneous_iff N P n)

namespace SegreVeronese
variable (M : MultiProjectiveSpace K) (D : M.FactorIndex → ℕ) {N : ℕ}
  (b : Module.Basis (projectiveSpace K N).Variable K
    (degreePiece K M.factorCount M.ambientDimension D))

def substitution : (projectiveSpace K N).CoordinateRing →ₐ[K] M.CoordinateRing :=
  aeval (fun j => (b j).val)

theorem substitution_degreePiece (n : ℕ) :
    (degreePiece K 1 (fun _ => N) (fun _ => n)).map
      (substitution M D b).toLinearMap =
        degreePiece K M.factorCount M.ambientDimension (fun i => n * D i) := by
  rw [ordinary_degreePiece_eq, ← homogeneousSubmodule_one_pow,
    Submodule.map_pow, homogeneousSubmodule_one_eq_span_X, Submodule.map_span]
  have he : (substitution M D b).toLinearMap '' Set.range X = Set.range (fun j => (b j).val) := by
    rw [← Set.range_comp]
    congr 1
    funext j
    simp [substitution]
  rw [he]
  have hspan : Submodule.span K (Set.range (fun j => (b j).val)) =
      degreePiece K M.factorCount M.ambientDimension D := by
    change Submodule.span K (Set.range
      ((degreePiece K M.factorCount M.ambientDimension D).subtype ∘ b)) = _
    rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  rw [hspan, M.degreePiece_diagonal_pow]

theorem substitution_homogeneous (n : ℕ)
    (P : (projectiveSpace K N).CoordinateRing) (hP : P.IsHomogeneous n) :
    (substitution M D b P).IsWeightedHomogeneous
      (blockWeight M.factorCount M.ambientDimension) (fun i => n * D i) := by
  have hmem : P ∈ degreePiece K 1 (fun _ => N) (fun _ => n) := by
    rw [ordinary_degreePiece_eq]
    exact hP
  change substitution M D b P ∈ degreePiece K M.factorCount M.ambientDimension _
  rw [← substitution_degreePiece M D b n]
  exact Submodule.mem_map_of_mem hmem

def diagonalIdeal (I : Ideal M.CoordinateRing) :
    Ideal (projectiveSpace K N).CoordinateRing :=
  I.comap (substitution M D b).toRingHom

end SegreVeronese
end PhilipponMultiplicity.Hilbert

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponMonomialPartition

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.MonomialCells

variable (p : ℕ) (N : Fin p → ℕ)

abbrev Var := Sigma fun i : Fin p => Fin (N i + 1)

theorem weight_apply (e : Var p N →₀ ℕ) (i : Fin p) :
    Finsupp.weight (Hilbert.blockWeight p N) e i = ∑ j, e ⟨i, j⟩ := by
  classical
  rw [Finsupp.weight_eq_sum, Fintype.sum_sigma]
  change (∑ b : Fin p, ∑ j : Fin (N b + 1),
    e ⟨b,j⟩ • Hilbert.blockWeight p N ⟨b,j⟩) i = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Hilbert.blockWeight,
    Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b hb hbi
    simp [Ne.symm hbi]
  · simp

end PhilipponMultiplicity.MonomialCells

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponSegreVeroneseAlgebra

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K]

theorem ordinary_weight_eq (N : ℕ) (e : ((i : Fin 1) × Fin (N + 1)) →₀ ℕ) :
    Finsupp.weight (blockWeight 1 (fun _ => N)) e = fun _ => e.degree := by
  ext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  have hd : e.degree = ∑ j : Fin (N + 1), e ⟨(0 : Fin 1), j⟩ := by
    rw [Finsupp.degree_eq_sum, Fintype.sum_sigma]
    simp [Fin.sum_univ_one]
  exact (MonomialCells.weight_apply 1 (fun _ => N) e 0).trans hd.symm

theorem ordinary_component_eq (N : ℕ) (P : CoordinateRing K 1 (fun _ => N))
    (d : Fin 1 → ℕ) :
    weightedHomogeneousComponent (blockWeight 1 (fun _ => N)) d P =
      homogeneousComponent (d 0) P := by
  classical
  apply MvPolynomial.ext
  intro e
  have he : (fun _ : Fin 1 => e.degree) = d ↔ e.degree = d 0 := by
    constructor
    · exact fun h => congrFun h 0
    · intro h
      ext i
      simpa only [Subsingleton.elim i (0 : Fin 1)] using h
  calc
    _ = if Finsupp.weight (blockWeight 1 (fun _ => N)) e = d then coeff e P else 0 :=
      coeff_weightedHomogeneousComponent d P e
    _ = if e.degree = d 0 then coeff e P else 0 := by simp only [ordinary_weight_eq, he]
    _ = _ := (coeff_homogeneousComponent (d 0) P e).symm

namespace SegreVeronese
variable (M : MultiProjectiveSpace K) (D : M.FactorIndex → ℕ) {N : ℕ}
  (b : Module.Basis (projectiveSpace K N).Variable K
    (degreePiece K M.factorCount M.ambientDimension D))

theorem substitution_component (hD : ∀ i, 1 ≤ D i)
    (P : (projectiveSpace K N).CoordinateRing) (n : ℕ) :
    weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension)
      (fun i => n * D i) (substitution M D b P) =
        substitution M D b (homogeneousComponent n P) := by
  classical
  have hinj : Function.Injective (fun m : ℕ => fun i => m * D i) := by
    intro m n h
    let i : M.FactorIndex := ⟨0, M.positive⟩
    have hi := congrFun h i
    have hpos := hD i
    nlinarith
  rw [P.as_sum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hh := isHomogeneous_monomial (coeff e P) (rfl : e.degree = e.degree)
  have hs := substitution_homogeneous M D b e.degree _ hh
  rw [weightedHomogeneousComponent_of_mem hs, homogeneousComponent_of_mem hh]
  by_cases hn : n = e.degree
  · subst n
    simp only [ite_true]
  · rw [if_neg (fun h => hn (hinj h)), if_neg hn, map_zero]

theorem diagonalIdeal_homogeneous (hD : ∀ i, 1 ≤ D i)
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I) :
    IsMultihomogeneousIdeal (projectiveSpace K N) (diagonalIdeal M D b I) := by
  intro P hP d
  change Fin 1 → ℕ at d
  change substitution M D b
    (weightedHomogeneousComponent (blockWeight 1 (fun _ => N)) d P) ∈ I
  rw [ordinary_component_eq]
  exact (substitution_component M D b hD P (d 0)) ▸
    hI _ hP (fun i => d 0 * D i)

theorem degreePiece_finrank_pos :
    0 < Module.finrank K (degreePiece K M.factorCount M.ambientDimension D) := by
  classical
  let e : M.Variable →₀ ℕ := Finsupp.equivFunOnFinite.symm
    (fun v => if v.2 = 0 then D v.1 else 0)
  have hhom : M.IsHomogeneous (monomial e (1 : K)) D := by
    intro a ha i
    have he : a = e := Finset.mem_singleton.mp (support_monomial_subset ha)
    subst a
    change (∑ j : Fin (M.ambientDimension i + 1), e ⟨i, j⟩) = D i
    simp only [e, Finsupp.coe_equivFunOnFinite_symm]
    exact (Finset.sum_ite_eq' Finset.univ (0 : Fin (M.ambientDimension i + 1))
      (fun _ => D i)).trans (if_pos (Finset.mem_univ _))
  have hmem := (M.degreePiece_iff _ _).mpr hhom
  let x : degreePiece K M.factorCount M.ambientDimension D := ⟨monomial e 1, hmem⟩
  have hx : x ≠ 0 := by
    intro h
    have hz := congrArg Subtype.val h
    simpa only [x, ZeroMemClass.coe_zero, monomial_eq_zero, one_ne_zero] using hz
  letI : Nontrivial (degreePiece K M.factorCount M.ambientDimension D) :=
    ⟨⟨x, 0, hx⟩⟩
  exact Module.finrank_pos

theorem exists_coordinate_basis : ∃ N : ℕ,
    Nonempty (Module.Basis (projectiveSpace K N).Variable K
      (degreePiece K M.factorCount M.ambientDimension D)) := by
  classical
  let d := Module.finrank K (degreePiece K M.factorCount M.ambientDimension D)
  have hd : 0 < d := degreePiece_finrank_pos M D
  let N := d - 1
  have hc : Fintype.card (projectiveSpace K N).Variable = d := by
    simp [MultiProjectiveSpace.Variable, projectiveSpace, N, Nat.sub_add_cancel hd]
  let e := Fintype.equivFinOfCardEq hc
  exact ⟨N, ⟨(Module.finBasis K (degreePiece K M.factorCount M.ambientDimension D)).reindex e.symm⟩⟩

end SegreVeronese
end PhilipponMultiplicity.Hilbert

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectiveNullstellensatz

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem homogeneousIdeal_eq_span (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) : M.IsHomogeneousIdeal I := by
  classical
  apply le_antisymm
  · intro P hP
    let w := Hilbert.blockWeight M.factorCount M.ambientDimension
    rw [← sum_weightedHomogeneousComponent w P,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp (w := w) P)]
    apply Ideal.sum_mem
    intro D _
    exact Ideal.subset_span ⟨hI P hP D, D,
      (M.degreePiece_iff _ D).mp (weightedHomogeneousComponent_mem w P D)⟩
  · exact Ideal.span_le.mpr (fun _ h => h.1)

theorem mem_zeroLocus_iff_homogeneous (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (x : M.Point) :
    x ∈ M.zeroLocus I ↔
      ∀ P ∈ I, ∀ D, M.IsHomogeneous P D → M.eval P x = 0 := by
  constructor
  · exact fun h P hP _ _ => h P hP
  · intro h
    have hle : I ≤ RingHom.ker (MvPolynomial.eval (M.coordinate x)) := by
      rw [M.homogeneousIdeal_eq_span I hI]
      exact Ideal.span_le.mpr (by rintro P ⟨hP,D,hD⟩; exact h P hP D hD)
    exact fun P hP => hle hP

end PhilipponMultiplicity.MultiProjectiveSpace

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponPointConeLinear

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.PointConeLinear
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)
  (a : M.Variable → K) (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))

def equation (j : M.Variable) : M.CoordinateRing :=
  X j - C (a j / a ⟨j.1,b j.1⟩) * X ⟨j.1,b j.1⟩

def ideal : Ideal M.CoordinateRing := Ideal.span (Set.range (equation M a b))

theorem equation_homogeneous (j : M.Variable) :
    M.IsHomogeneous (equation M a b j) (Pi.single j.1 1) := by
  classical
  have hd : (fun i : M.FactorIndex => if i = j.1 then 1 else 0) = Pi.single j.1 1 := by
    funext i
    simp [Pi.single_apply]
  rw [← hd]
  exact
    (M.isHomogeneous_X j).sub M
      ((M.isHomogeneous_X ⟨j.1,b j.1⟩).C_mul M (a j / a ⟨j.1,b j.1⟩))

theorem equation_eval (hb : ∀ i, a ⟨i,b i⟩ ≠ 0) (j : M.Variable) :
    eval a (equation M a b j) = 0 := by
  simp [equation, div_mul_cancel₀ _ (hb j.1)]

theorem zeroLocus_eq_singleton (hb : ∀ i, a ⟨i,b i⟩ ≠ 0)
    (x : M.Point)
    (hrep : ∀ i, ∃ h : (fun j => a ⟨i,j⟩) ≠ 0,
      Projectivization.mk K (fun j => a ⟨i,j⟩) h = x i) :
    M.zeroLocus (ideal M a b) = {x} := by
  ext y
  constructor
  · intro hy
    apply Set.mem_singleton_iff.mpr
    funext i
    obtain ⟨ha,hax⟩ := hrep i
    rw [← hax, ← Projectivization.mk_rep (y i)]
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
    refine ⟨(y i).rep (b i) / a ⟨i,b i⟩, ?_⟩
    funext j
    have h := hy (equation M a b ⟨i,j⟩) (Ideal.subset_span ⟨⟨i,j⟩,rfl⟩)
    have h' : (y i).rep j = a ⟨i,j⟩ / a ⟨i,b i⟩ * (y i).rep (b i) := by
      simpa [equation, MultiProjectiveSpace.eval, MultiProjectiveSpace.coordinate,
        sub_eq_zero] using h
    simp only [Pi.smul_apply, smul_eq_mul, h']
    ring
  · intro hy
    have hyx := Set.mem_singleton_iff.mp hy
    subst y
    have hle : ideal M a b ≤ RingHom.ker (eval (M.coordinate x)) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨j,rfl⟩
      exact (M.eval_eq_zero_iff_of_lift x a hrep _ _ (equation_homogeneous M a b j)).mp
        (equation_eval M a b hb j)
    exact hle

end PhilipponMultiplicity.PointConeLinear
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponSegreVeronesePoints

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option synthInstance.maxHeartbeats 1500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.Hilbert.SegreVeronese

open MvPolynomial

variable {K : Type*} [Field K]
    (M : MultiProjectiveSpace K) (D : M.FactorIndex → ℕ) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (degreePiece K M.factorCount M.ambientDimension D))

theorem basis_evaluation_ne_zero (p : M.Point) :
    (fun j => M.eval (b j).val p) ≠ 0 := by
  intro hz
  let ev := (aeval (M.coordinate p) : M.CoordinateRing →ₐ[K] K).toLinearMap.domRestrict
    (degreePiece K M.factorCount M.ambientDimension D)
  have hev : ev = 0 := by
    apply b.ext
    intro j
    exact congrFun hz j
  obtain ⟨P, hP, hp⟩ := M.exists_form_nonzero_at p D
  exact hp (LinearMap.congr_fun hev ⟨P, (M.degreePiece_iff P D).mpr hP⟩)

def pointCoordinates (p : M.Point) : Fin (N + 1) → K :=
  fun j => M.eval (b ⟨(0 : Fin 1), j⟩).val p

theorem pointCoordinates_ne_zero (p : M.Point) : pointCoordinates M D b p ≠ 0 := by
  intro h
  apply basis_evaluation_ne_zero M D b p
  funext v
  obtain ⟨i, j⟩ := v
  have hi : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
  subst i
  exact congrFun h j

def pointMap (p : M.Point) : (projectiveSpace K N).Point :=
  fun _ => Projectivization.mk K (pointCoordinates M D b p) (pointCoordinates_ne_zero M D b p)

theorem pointMap_represents (p : M.Point) (i : (projectiveSpace K N).FactorIndex) :
    ∃ h : (fun j => M.eval (b ⟨i, j⟩).val p) ≠ 0,
      Projectivization.mk K (fun j => M.eval (b ⟨i, j⟩).val p) h = pointMap M D b p i := by
  have hi : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
  subst i
  exact ⟨pointCoordinates_ne_zero M D b p, rfl⟩

theorem eval_substitution (p : M.Point) (P : (projectiveSpace K N).CoordinateRing) :
    M.eval (substitution M D b P) p = aeval (fun j => M.eval (b j).val p) P := by
  change aeval (M.coordinate p) (aeval (fun j => (b j).val) P) = _
  rw [AffineClosedPoints.evaluate_substitution]
  rfl

theorem pointMap_eval_eq_zero_iff (p : M.Point) (P : (projectiveSpace K N).CoordinateRing)
    (E : (projectiveSpace K N).FactorIndex → ℕ) (hP : (projectiveSpace K N).IsHomogeneous P E) :
    (projectiveSpace K N).eval P (pointMap M D b p) = 0 ↔
      M.eval (substitution M D b P) p = 0 := by
  rw [eval_substitution]
  exact ((projectiveSpace K N).eval_eq_zero_iff_of_lift _ _
    (pointMap_represents M D b p) P E hP).symm

theorem pointMap_regular :
    M.IsRegularAlong (projectiveSpace K N) id (pointMap M D b) := by
  letI := M.zariskiTopology
  intro p i
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, D,
    fun j => (b ⟨i, j⟩).val, ?_, ?_⟩
  · intro j
    exact (M.degreePiece_iff _ D).mp (b ⟨i, j⟩).property
  · intro q _
    exact pointMap_represents M D b q i

theorem pointMap_mem_diagonal_zeroLocus (hD : ∀ i, 1 ≤ D i)
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (p : M.Point) (hp : p ∈ M.zeroLocus I) :
    pointMap M D b p ∈ (projectiveSpace K N).zeroLocus (diagonalIdeal M D b I) := by
  apply ((projectiveSpace K N).mem_zeroLocus_iff_homogeneous _
    (diagonalIdeal_homogeneous M D b hD I hI) _).mpr
  intro P hP E hE
  rw [pointMap_eval_eq_zero_iff M D b p P E hE]
  exact hp _ hP

theorem degree_evaluation_iff_of_pointMap_eq (p q : M.Point)
    (heq : pointMap M D b p = pointMap M D b q)
    (P : M.CoordinateRing) (hP : M.IsHomogeneous P D) :
    M.eval P p = 0 ↔ M.eval P q = 0 := by
  have hmem : P ∈ (degreePiece K 1 (fun _ => N) (fun _ => 1)).map
      (substitution M D b).toLinearMap := by
    rw [substitution_degreePiece]
    simpa only [one_mul] using (M.degreePiece_iff P D).mpr hP
  obtain ⟨F, hF, hFP⟩ := hmem
  change substitution M D b F = P at hFP
  rw [← hFP, ← pointMap_eval_eq_zero_iff M D b p F (fun _ => 1)
    (((projectiveSpace K N).degreePiece_iff F _).mp hF),
    ← pointMap_eval_eq_zero_iff M D b q F (fun _ => 1)
    (((projectiveSpace K N).degreePiece_iff F _).mp hF), heq]

theorem pointMap_injective (hD : ∀ i, 1 ≤ D i) : Function.Injective (pointMap M D b) := by
  classical
  intro p q hpq
  choose a ha using fun i => Function.ne_iff.mp (q i).rep_nonzero
  let v := M.coordinate q
  have hv (i) : v ⟨i, a i⟩ ≠ 0 := ha i
  have hlift (i) : ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i, j⟩) h = q i :=
    ⟨(q i).rep_nonzero, (q i).mk_rep⟩
  have hp : p ∈ M.zeroLocus (PointConeLinear.ideal M v a) := by
    have hker : PointConeLinear.ideal M v a ≤ RingHom.ker (MvPolynomial.eval (M.coordinate p)) := by
      apply Ideal.span_le.mpr
      rintro L ⟨j, rfl⟩
      let E : M.FactorIndex → ℕ := Pi.single j.1 1
      have hED : E ≤ D := by
        intro i
        by_cases hi : i = j.1
        · subst i
          simpa [E] using hD j.1
        · simp [E, Pi.single_apply, hi]
      obtain ⟨Q, hQ, hQp⟩ := M.exists_form_nonzero_at p (D - E)
      have hhom : M.IsHomogeneous (PointConeLinear.equation M v a j * Q) D := by
        have h := (PointConeLinear.equation_homogeneous M v a j).mul M hQ
        have hd : E + (D - E) = D := add_tsub_cancel_of_le hED
        exact hd ▸ h
      have hzeroq : M.eval (PointConeLinear.equation M v a j * Q) q = 0 := by
        change MvPolynomial.eval v (PointConeLinear.equation M v a j * Q) = 0
        rw [map_mul, PointConeLinear.equation_eval M v a hv, zero_mul]
      have hzerop := (degree_evaluation_iff_of_pointMap_eq M D b p q hpq _ hhom).mpr hzeroq
      change M.eval (PointConeLinear.equation M v a j) p = 0
      have hmul : M.eval (PointConeLinear.equation M v a j) p * M.eval Q p = 0 := by
        simpa only [MultiProjectiveSpace.eval, map_mul] using hzerop
      exact (mul_eq_zero.mp hmul).resolve_right hQp
    exact hker
  rw [PointConeLinear.zeroLocus_eq_singleton M v a hv q hlift] at hp
  exact Set.mem_singleton_iff.mp hp

end PhilipponMultiplicity.Hilbert.SegreVeronese

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponPrimeFiltration

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem prime_of_homogeneous_products (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (hne : I ≠ ⊤)
    (hmul : ∀ P Q : M.CoordinateRing, (∃ D, M.IsHomogeneous P D) →
      (∃ E, M.IsHomogeneous Q E) → P * Q ∈ I → P ∈ I ∨ Q ∈ I) : I.IsPrime := by
  classical
  let w : M.Variable → Lex (M.FactorIndex → ℕ) :=
    fun x => toLex (blockWeight M.factorCount M.ambientDimension x)
  letI : DecidableEq (Lex (M.FactorIndex → ℕ)) := LinearOrder.toDecidableEq
  letI := weightedGradedAlgebra K w
  have hIg : I.IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    intro d f hf
    change ((MvPolynomial.decompose' K w f) d : M.CoordinateRing) ∈ I
    rw [MvPolynomial.decompose'_apply]
    have heq : weightedHomogeneousComponent w d f =
        weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension) (ofLex d) f := by
      ext e
      simp only [coeff_weightedHomogeneousComponent]
      rfl
    rw [heq]
    exact hI f hf (ofLex d)
  apply hIg.isPrime_of_homogeneous_mem_or_mem hne
  rintro P Q ⟨D, hP⟩ ⟨E, hQ⟩ hPQ
  apply hmul P Q _ _ hPQ
  · exact ⟨ofLex D, (M.degreePiece_iff P (ofLex D)).mp hP⟩
  · exact ⟨ofLex E, (M.degreePiece_iff Q (ofLex E)).mp hQ⟩

end PhilipponMultiplicity.Hilbert

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponRelevantHilbert

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem variable_product_homogeneous (v : ∀ i, Fin (M.ambientDimension i + 1))
    (d : M.FactorIndex → ℕ) :
    M.IsHomogeneous (∏ i, (X ⟨i, v i⟩ : M.CoordinateRing) ^ d i) d := by
  classical
  apply (M.degreePiece_iff _ d).mp
  let w := blockWeight M.factorCount M.ambientDimension
  have hx (i : M.FactorIndex) : (X ⟨i, v i⟩ : M.CoordinateRing).IsWeightedHomogeneous w
      (w ⟨i, v i⟩) := isWeightedHomogeneous_X K w ⟨i, v i⟩
  have h := IsWeightedHomogeneous.prod (w := w) Finset.univ
    (fun i => (X ⟨i, v i⟩ : M.CoordinateRing) ^ d i)
    (fun i => d i • blockWeight M.factorCount M.ambientDimension ⟨i, v i⟩)
    (fun i _ => (hx i).pow (d i))
  have heq : (∑ i, d i • blockWeight M.factorCount M.ambientDimension ⟨i, v i⟩) = d := by
    funext i
    simp [blockWeight, Pi.single_apply, Finset.sum_apply, smul_eq_mul]
  rwa [heq] at h

end PhilipponMultiplicity.Hilbert

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponSegreLinearForms

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Pointwise
noncomputable section

namespace PhilipponMultiplicity.Hilbert.SegreVeronese
open MvPolynomial
variable {K : Type*} [Field K]
    (M : MultiProjectiveSpace K) (D : M.FactorIndex → ℕ) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (degreePiece K M.factorCount M.ambientDimension D))

def linearForm : degreePiece K M.factorCount M.ambientDimension D →ₗ[K]
    homogeneousSubmodule (projectiveSpace K N).Variable K 1 :=
  b.constr K (fun j => ⟨X j, isHomogeneous_X K j⟩)

@[simp] theorem linearForm_basis (j : (projectiveSpace K N).Variable) :
    (linearForm M D b (b j)).val = X j := by
  simp [linearForm]

theorem substitution_linearForm (P : degreePiece K M.factorCount M.ambientDimension D) :
    substitution M D b (linearForm M D b P).val = P.val := by
  have h : ((substitution M D b).toLinearMap.comp
      (homogeneousSubmodule (projectiveSpace K N).Variable K 1).subtype).comp
      (linearForm M D b) = (degreePiece K M.factorCount M.ambientDimension D).subtype := by
    apply b.ext
    intro j
    simp [substitution]
  exact LinearMap.congr_fun h P

variable (a : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))

def pureProduct : M.CoordinateRing := ∏ i, X ⟨i, a i⟩

theorem pureProduct_homogeneous : M.IsHomogeneous (pureProduct M a) (fun _ => 1) := by
  simpa only [pureProduct, pow_one] using variable_product_homogeneous M a (fun _ => 1)

def pureForm : degreePiece K M.factorCount M.ambientDimension (fun _ => 1) :=
  ⟨pureProduct M a, (M.degreePiece_iff _ _).mpr (pureProduct_homogeneous M a)⟩

theorem degree_one_span_pureProducts :
    degreePiece K M.factorCount M.ambientDimension (fun _ => 1) =
      Submodule.span K (Set.range (pureProduct M)) := by
  classical
  rw [M.degreePiece_eq_blockProductSpace]
  simp only [MultiProjectiveSpace.blockProductSpace, pow_one,
    MultiProjectiveSpace.blockLinearSpace, Submodule.prod_span]
  congr 1
  ext P
  rw [Set.mem_fintype_prod]
  constructor
  · rintro ⟨g, hg, hP⟩
    choose a ha using hg
    refine ⟨a, ?_⟩
    simpa only [pureProduct, ha] using hP
  · rintro ⟨a, rfl⟩
    exact ⟨fun i => X ⟨i, a i⟩, fun i => ⟨a i, rfl⟩, rfl⟩

theorem pureForms_span_top :
    Submodule.span K (Set.range (pureForm M)) = ⊤ := by
  apply (Submodule.map_injective_of_injective
    (f := (degreePiece K M.factorCount M.ambientDimension (fun _ => 1)).subtype)
    Subtype.val_injective)
  rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
  exact (degree_one_span_pureProducts M).symm

variable (b₁ : Module.Basis (projectiveSpace K N).Variable K
    (degreePiece K M.factorCount M.ambientDimension (fun _ => 1)))

theorem exists_pureForm_nonzero (p : (projectiveSpace K N).Point) :
    ∃ a, (projectiveSpace K N).eval
      (linearForm M (fun _ => 1) b₁ (pureForm M a)).val p ≠ 0 := by
  classical
  by_contra! h
  let ev := (aeval ((projectiveSpace K N).coordinate p) :
    (projectiveSpace K N).CoordinateRing →ₐ[K] K).toLinearMap.comp
    ((homogeneousSubmodule (projectiveSpace K N).Variable K 1).subtype.comp
      (linearForm M (fun _ => 1) b₁))
  have hker : Submodule.span K (Set.range (pureForm M)) ≤ LinearMap.ker ev := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact h a
  rw [pureForms_span_top] at hker
  have hz (j : (projectiveSpace K N).Variable) :
      (projectiveSpace K N).coordinate p j = 0 := by
    have hj := hker (Submodule.mem_top : b₁ j ∈ ⊤)
    change aeval ((projectiveSpace K N).coordinate p)
      (linearForm M (fun _ => 1) b₁ (b₁ j)).val = 0 at hj
    simpa only [linearForm_basis, aeval_X] using hj
  exact (p (0 : Fin 1)).rep_nonzero (funext (fun j => hz ⟨(0 : Fin 1), j⟩))

end PhilipponMultiplicity.Hilbert.SegreVeronese

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponNormalizedChartRadicalReuse
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section
namespace PhilipponMultiplicity.AffineChartDomain
universe u v
variable {K : Type u} [Field K] (M : MultiProjectiveSpace K)
theorem eval₂_block_scale {A : Type v} [CommRing A] (f : K →+* A)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (v : M.Variable → A) (a : M.FactorIndex → A) :
    eval₂Hom f (fun j => a j.1 * v j) P =
      (∏ i, a i ^ D i) * eval₂Hom f v P := by
  classical
  simp only [coe_eval₂Hom, eval₂_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hscale : (∏ j : M.Variable, a j.1 ^ d j) = ∏ i, a i ^ D i := by
    rw [Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro i _
    change (∏ j : Fin (M.ambientDimension i + 1), a i ^ d ⟨i,j⟩) = a i ^ D i
    rw [Finset.prod_pow_eq_pow_sum, hP d hd i]
  simp only [mul_pow, Finset.prod_mul_distrib, hscale]
  ring

end PhilipponMultiplicity.AffineChartDomain
namespace PhilipponMultiplicity.MixedFlag
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

end PhilipponMultiplicity.MixedFlag
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponSegreInverseEquations

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.Hilbert.SegreVeronese
open MvPolynomial
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (degreePiece K M.factorCount M.ambientDimension (fun _ => 1)))
    (a : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))

def omittedProduct (i : M.FactorIndex) : M.CoordinateRing :=
  ∏ k, X ⟨k, a k⟩ ^ (if k = i then 0 else 1)

theorem omittedProduct_homogeneous (i : M.FactorIndex) :
    M.IsHomogeneous (omittedProduct M a i) (fun k => if k = i then 0 else 1) :=
  variable_product_homogeneous M a _

theorem omittedProduct_mul_pivot (i : M.FactorIndex) :
    omittedProduct M a i * X ⟨i, a i⟩ = pureProduct M a := by
  classical
  calc
    _ = (∏ k, (X ⟨k, a k⟩ : M.CoordinateRing) ^ (if k = i then 0 else 1)) *
        (∏ k, (X ⟨k, a k⟩ : M.CoordinateRing) ^ (if k = i then 1 else 0)) := by
      simp [omittedProduct]
    _ = ∏ k, (X ⟨k, a k⟩ : M.CoordinateRing) ^ (if k = i then 0 else 1) *
        X ⟨k, a k⟩ ^ (if k = i then 1 else 0) := by rw [Finset.prod_mul_distrib]
    _ = pureProduct M a := by
      apply Finset.prod_congr rfl
      intro k _
      by_cases h : k = i <;> simp [h]

set_option maxHeartbeats 50000 in
theorem prod_omittedProducts :
    (∏ i, omittedProduct M a i) = pureProduct M a ^ (M.factorCount - 1) := by
  classical
  have hS : pureProduct M a ≠ 0 := by
    change (∏ i, (X ⟨i, a i⟩ : M.CoordinateRing)) ≠ 0
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => X_ne_zero (⟨i, a i⟩ : M.Variable))
  apply mul_right_cancel₀ hS
  calc
    _ = ∏ i, omittedProduct M a i * X ⟨i, a i⟩ := by
      rw [Finset.prod_mul_distrib]
      rfl
    _ = ∏ _i : M.FactorIndex, pureProduct M a := by
      apply Finset.prod_congr rfl
      intro i _
      exact omittedProduct_mul_pivot M a i
    _ = pureProduct M a ^ M.factorCount := by simp
    _ = pureProduct M a ^ (M.factorCount - 1) * pureProduct M a := by
      rw [← pow_succ, Nat.sub_add_cancel M.positive]

def replacementForm (v : M.Variable) :
    degreePiece K M.factorCount M.ambientDimension (fun _ => 1) :=
  ⟨omittedProduct M a v.1 * X v, by
    apply (M.degreePiece_iff _ _).mpr
    have h := (omittedProduct_homogeneous M a v.1).mul M (M.isHomogeneous_X v)
    convert h using 1
    ext i
    by_cases hi : i = v.1 <;> simp [hi]⟩

@[simp] theorem replacementForm_pivot (i : M.FactorIndex) :
    replacementForm M a ⟨i, a i⟩ = pureForm M a := by
  apply Subtype.ext
  exact omittedProduct_mul_pivot M a i

def inverseSubstitution : M.CoordinateRing →ₐ[K] (projectiveSpace K N).CoordinateRing :=
  aeval (fun v => (linearForm M (fun _ => 1) b (replacementForm M a v)).val)

theorem substitution_inverseSubstitution (P : M.CoordinateRing)
    (E : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P E) :
    substitution M (fun _ => 1) b (inverseSubstitution M b a P) =
      (∏ i, omittedProduct M a i ^ E i) * P := by
  have hcomp : (substitution M (fun _ => 1) b).comp (inverseSubstitution M b a) =
      aeval (fun v => omittedProduct M a v.1 * X v) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [AlgHom.comp_apply, inverseSubstitution, aeval_X,
      substitution_linearForm, replacementForm]
  change ((substitution M (fun _ => 1) b).comp (inverseSubstitution M b a)) P = _
  rw [hcomp]
  have h := AffineChartDomain.eval₂_block_scale M (C : K →+* M.CoordinateRing)
    P E hP (fun v => X v) (omittedProduct M a)
  change eval₂ C (fun v => omittedProduct M a v.1 * X v) P = _
  simpa only [coe_eval₂Hom, eval₂_eta] using h

theorem inverseSubstitution_mem_diagonal (I : Ideal M.CoordinateRing)
    (P : M.CoordinateRing) (hP : P ∈ I)
    (E : M.FactorIndex → ℕ) (hE : M.IsHomogeneous P E) :
    inverseSubstitution M b a P ∈ diagonalIdeal M (fun _ => 1) b I := by
  change substitution M (fun _ => 1) b (inverseSubstitution M b a P) ∈ I
  rw [substitution_inverseSubstitution M b a P E hE]
  exact I.mul_mem_left _ hP

theorem inverse_basis_relation (I : Ideal M.CoordinateRing)
    (j : (projectiveSpace K N).Variable) :
    inverseSubstitution M b a (b j).val -
      X j * (linearForm M (fun _ => 1) b (pureForm M a)).val ^ (M.factorCount - 1) ∈
        diagonalIdeal M (fun _ => 1) b I := by
  change substitution M (fun _ => 1) b _ ∈ I
  rw [map_sub, substitution_inverseSubstitution M b a _ (fun _ => 1)
    ((M.degreePiece_iff _ _).mp (b j).property)]
  simp only [pow_one, prod_omittedProducts, map_mul, map_pow,
    substitution_linearForm, pureForm]
  have hx : substitution M (fun _ => 1) b (X j) = (b j).val := by
    simp [substitution]
  rw [hx, mul_comm, sub_self]
  exact I.zero_mem

end PhilipponMultiplicity.Hilbert.SegreVeronese

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectiveNormalizedLift

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
open MvPolynomial
variable {K : Type*} [Field K] (N : ℕ)

theorem exists_lift_normalized_by_linear_form
    (J : Ideal (projectiveSpace K N).CoordinateRing)
    (hJ : IsMultihomogeneousIdeal (projectiveSpace K N) J)
    (p : (projectiveSpace K N).Point) (hp : p ∈ (projectiveSpace K N).zeroLocus J)
    (F : (projectiveSpace K N).CoordinateRing) (hF : F.IsHomogeneous 1)
    (hn : (projectiveSpace K N).eval F p ≠ 0) :
    ∃ z : (projectiveSpace K N).Variable → K,
      (∀ P ∈ J, aeval z P = 0) ∧ aeval z F = 1 ∧
      (∀ i : (projectiveSpace K N).FactorIndex,
        ∃ h : (fun j => z ⟨i, j⟩) ≠ 0,
          Projectivization.mk K (fun j => z ⟨i, j⟩) h = p i) := by
  classical
  let Q := projectiveSpace K N
  let c := (Q.eval F p)⁻¹
  let z : Q.Variable → K := fun v => c * Q.coordinate p v
  have hc : c ≠ 0 := inv_ne_zero hn
  have heval (P : Q.CoordinateRing) (E : Q.FactorIndex → ℕ)
      (hP : Q.IsHomogeneous P E) : aeval z P = c ^ E (0 : Fin 1) * Q.eval P p := by
    have h := Q.eval_block_scale P E hP (Q.coordinate p) (fun _ => c)
    have hprod : (∏ i : Q.FactorIndex, c ^ E i) = c ^ E (0 : Fin 1) :=
      Fin.prod_univ_one _
    rw [hprod] at h
    exact h
  have hker : J ≤ RingHom.ker (aeval z : Q.CoordinateRing →ₐ[K] K).toRingHom := by
    rw [Q.homogeneousIdeal_eq_span J hJ]
    apply Ideal.span_le.mpr
    rintro P ⟨hP, E, hE⟩
    change aeval z P = 0
    rw [heval P E hE, hp P hP, mul_zero]
  refine ⟨z, fun P hP => hker hP, ?_, ?_⟩
  · rw [heval F (fun _ => 1) ((projective_homogeneous_iff N F 1).mpr hF)]
    simpa only [pow_one, c] using inv_mul_cancel₀ hn
  · intro i
    have hz : (fun j => z ⟨i, j⟩) ≠ 0 := by
      intro h
      apply (p i).rep_nonzero
      funext j
      have hj : c * (p i).rep j = 0 := congrFun h j
      exact (mul_eq_zero.mp hj).resolve_left hc
    refine ⟨hz, ?_⟩
    rw [← (p i).mk_rep]
    exact (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨c, rfl⟩

end PhilipponMultiplicity.MultiProjectiveSpace

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponRegularMapComposition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open Set MvPolynomial
open scoped BigOperators Topology

namespace PhilipponMultiplicity.MultiProjectiveSpace
universe u
variable {K : Type u} [Field K]

theorem homogeneous_tuple_lift {ι : Type*} (M : MultiProjectiveSpace K)
    (p : M.Point) (v : M.Variable → K)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i, j⟩) h = p i)
    (P : ι → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : ∀ j, M.IsHomogeneous (P j) D)
    (hn : (fun j => M.eval (P j) p) ≠ 0) :
    ∃ h : (fun j => MvPolynomial.eval v (P j)) ≠ 0,
      Projectivization.mk K (fun j => MvPolynomial.eval v (P j)) h =
        Projectivization.mk K (fun j => M.eval (P j) p) hn := by
  classical
  have ha (i : M.FactorIndex) : ∃ a : Kˣ,
      ∀ j, v ⟨i, j⟩ = (a : K) * (p i).rep j := by
    obtain ⟨h, he⟩ := hv i
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ h
      (Projectivization.rep_nonzero (p i))).mp
      (he.trans (Projectivization.mk_rep (p i)).symm)
    refine ⟨a, fun j => ?_⟩
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha j).symm
  choose a ha using ha
  have hv' : v = fun j => (a j.1 : K) * M.coordinate p j := by
    funext j
    exact ha j.1 j.2
  let b : K := ∏ i, (a i : K) ^ D i
  have hb : b ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => pow_ne_zero _ (a i).ne_zero)
  have heval : (fun j => MvPolynomial.eval v (P j)) = b • (fun j => M.eval (P j) p) := by
    funext j
    rw [hv', M.eval_block_scale (P j) D (hP j) (M.coordinate p) (fun i => (a i : K))]
    rfl
  have hn' : (fun j => MvPolynomial.eval v (P j)) ≠ 0 := by
    rw [heval]
    exact smul_ne_zero hb hn
  exact ⟨hn', (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨b, heval.symm⟩⟩

theorem IsRegularAlong.comp {X : Type u} {M N Q : MultiProjectiveSpace K}
    {e : X → M.Point} {f : X → N.Point} {g : X → Q.Point}
    (hf : M.IsRegularAlong N e f) (hg : N.IsRegularAlong Q f g) :
    M.IsRegularAlong Q e g := by
  classical
  let := M.zariskiTopology
  let := N.zariskiTopology
  let := TopologicalSpace.induced e M.zariskiTopology
  intro x b
  obtain ⟨U, hU, hxU, D, P, hP, hPlift⟩ := hg x b
  obtain ⟨V, hV, hVeq⟩ := isOpen_induced_iff.mp (hU.preimage hf.continuous)
  choose W hW hxW E R hR hRlift using hf x
  let pull (j : Fin (Q.ambientDimension b + 1)) :=
    eval₂ C (fun t : N.Variable => R t.1 t.2) (P j)
  refine ⟨V ∩ ⋂ a, W a, hV.inter (isOpen_iInter_of_finite hW),
    ⟨?_, mem_iInter.mpr hxW⟩, (fun i => ∑ a, D a * E a i), pull, ?_, ?_⟩
  · have hx : x ∈ f ⁻¹' U := hxU
    rwa [← hVeq] at hx
  · intro j
    exact (hP j).eval₂_blocks M N _ E (fun t => hR t.1 t.2)
  · intro y hy
    have hyU : f y ∈ U := by
      change y ∈ f ⁻¹' U
      rw [← hVeq]
      exact hy.1
    obtain ⟨hn, heq⟩ := hPlift y hyU
    have hlift (a : N.FactorIndex) := hRlift a y (mem_iInter.mp hy.2 a)
    obtain ⟨hn', heq'⟩ := N.homogeneous_tuple_lift (f y)
      (fun t : N.Variable => M.eval (R t.1 t.2) (e y)) hlift P D hP hn
    have heval (j) : M.eval (pull j) (e y) =
        MvPolynomial.eval (fun t : N.Variable => M.eval (R t.1 t.2) (e y)) (P j) := by
      dsimp only [eval, pull]
      rw [← eval_assoc]
      rfl
    simpa only [heval] using ⟨hn', heq'.trans heq⟩

end PhilipponMultiplicity.MultiProjectiveSpace
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponSegreLocusSurjectivity

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.Hilbert.SegreVeronese
open MvPolynomial
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (degreePiece K M.factorCount M.ambientDimension (fun _ => 1)))

theorem pointMap_represents_of_lift (p : M.Point) (w : M.Variable → K)
    (hw : ∀ i, ∃ h : (fun j => w ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => w ⟨i, j⟩) h = p i)
    (i : (projectiveSpace K N).FactorIndex) :
    ∃ h : (fun j => aeval w (b ⟨i, j⟩).val) ≠ 0,
      Projectivization.mk K (fun j => aeval w (b ⟨i, j⟩).val) h =
        pointMap M (fun _ => 1) b p i := by
  obtain ⟨hn, he⟩ := pointMap_represents M (fun _ => 1) b p i
  obtain ⟨hn', he'⟩ := M.homogeneous_tuple_lift p w hw (fun j => (b ⟨i, j⟩).val)
    (fun _ => 1) (fun j => (M.degreePiece_iff _ _).mp (b ⟨i, j⟩).property) hn
  exact ⟨hn', he'.trans he⟩

theorem exists_inverse_on_pivot
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (p : (projectiveSpace K N).Point)
    (hp : p ∈ (projectiveSpace K N).zeroLocus (diagonalIdeal M (fun _ => 1) b I))
    (a : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))
    (ha : (projectiveSpace K N).eval
      (linearForm M (fun _ => 1) b (pureForm M a)).val p ≠ 0) :
    ∃ q : M.Point, q ∈ M.zeroLocus I ∧ pointMap M (fun _ => 1) b q = p ∧
      ∀ i : M.FactorIndex,
        ∃ h : (fun j => (projectiveSpace K N).eval
          (linearForm M (fun _ => 1) b (replacementForm M a ⟨i, j⟩)).val p) ≠ 0,
          Projectivization.mk K (fun j => (projectiveSpace K N).eval
            (linearForm M (fun _ => 1) b (replacementForm M a ⟨i, j⟩)).val p) h = q i := by
  classical
  let Q := projectiveSpace K N
  obtain ⟨z, hz, hzS, hzrep⟩ := MultiProjectiveSpace.exists_lift_normalized_by_linear_form N
    (diagonalIdeal M (fun _ => 1) b I)
    (diagonalIdeal_homogeneous M (fun _ => 1) b (fun _ => le_rfl) I hI)
    p hp (linearForm M (fun _ => 1) b (pureForm M a)).val
    (linearForm M (fun _ => 1) b (pureForm M a)).property ha
  let w : M.Variable → K := fun v =>
    aeval z (linearForm M (fun _ => 1) b (replacementForm M a v)).val
  have hw_pivot (i : M.FactorIndex) : w ⟨i, a i⟩ = 1 := by
    simpa only [w, replacementForm_pivot] using hzS
  have hw (i : M.FactorIndex) : (fun j => w ⟨i, j⟩) ≠ 0 := by
    intro h
    have hz0 : w ⟨i, a i⟩ = 0 := congrFun h (a i)
    exact one_ne_zero ((hw_pivot i).symm.trans hz0)
  let q : M.Point := fun i => Projectivization.mk K (fun j => w ⟨i, j⟩) (hw i)
  have hqrep (i : M.FactorIndex) : ∃ h : (fun j => w ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => w ⟨i, j⟩) h = q i := ⟨hw i, rfl⟩
  have heval (P : M.CoordinateRing) :
      aeval w P = aeval z (inverseSubstitution M b a P) :=
    (AffineClosedPoints.evaluate_substitution _ z P).symm
  have hbasis (j : Q.Variable) : aeval w (b j).val = z j := by
    have h := hz _ (inverse_basis_relation M b a I j)
    rw [map_sub, map_mul, map_pow, aeval_X, hzS, one_pow, mul_one] at h
    exact (heval _).trans (sub_eq_zero.mp h)
  refine ⟨q, ?_, ?_, ?_⟩
  · apply (M.mem_zeroLocus_iff_homogeneous I hI q).mpr
    intro P hP E hE
    apply (M.eval_eq_zero_iff_of_lift q w hqrep P E hE).mp
    change aeval w P = 0
    rw [heval]
    exact hz _ (inverseSubstitution_mem_diagonal M b a I P hP E hE)
  · funext i
    obtain ⟨hn, he⟩ := pointMap_represents_of_lift M b q w hqrep i
    obtain ⟨hznon, hzpoint⟩ := hzrep i
    have hcoords : (fun j => aeval w (b ⟨i, j⟩).val) = (fun j => z ⟨i, j⟩) :=
      funext (fun j => hbasis ⟨i, j⟩)
    have hmk : Projectivization.mk K (fun j => aeval w (b ⟨i, j⟩).val) hn = p i := by
      simpa only [hcoords] using hzpoint
    exact he.symm.trans hmk
  · intro i
    let F : Fin (M.ambientDimension i + 1) → Q.CoordinateRing :=
      fun j => (linearForm M (fun _ => 1) b (replacementForm M a ⟨i, j⟩)).val
    have hF (j) : Q.IsHomogeneous (F j) (fun _ => 1) :=
      (MultiProjectiveSpace.projective_homogeneous_iff N (F j) 1).mpr
        (linearForm M (fun _ => 1) b (replacementForm M a ⟨i, j⟩)).property
    have hn : (fun j => Q.eval (F j) p) ≠ 0 := by
      intro h
      have hzero : Q.eval (F (a i)) p = 0 := congrFun h (a i)
      exact ha (by simpa only [F, replacementForm_pivot] using hzero)
    obtain ⟨hn', he⟩ := Q.homogeneous_tuple_lift p z hzrep F (fun _ => 1) hF hn
    exact ⟨hn, he.symm⟩

theorem pointMap_surjective_on_locus
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (p : (projectiveSpace K N).Point)
    (hp : p ∈ (projectiveSpace K N).zeroLocus (diagonalIdeal M (fun _ => 1) b I)) :
    ∃ q ∈ M.zeroLocus I, pointMap M (fun _ => 1) b q = p := by
  obtain ⟨a, ha⟩ := exists_pureForm_nonzero M b p
  obtain ⟨q, hq, he, _⟩ := exists_inverse_on_pivot M b I hI p hp a ha
  exact ⟨q, hq, he⟩

end PhilipponMultiplicity.Hilbert.SegreVeronese

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponSegreLocusEquivalence

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option synthInstance.maxHeartbeats 1500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.Hilbert.SegreVeronese
open MvPolynomial
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (degreePiece K M.factorCount M.ambientDimension (fun _ => 1)))
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)

def locusMap : M.zeroLocus I →
    (projectiveSpace K N).zeroLocus (diagonalIdeal M (fun _ => 1) b I) :=
  fun x => ⟨pointMap M (fun _ => 1) b x.val,
    pointMap_mem_diagonal_zeroLocus M (fun _ => 1) b (fun _ => le_rfl) I hI x.val x.property⟩

theorem locusMap_bijective : Function.Bijective (locusMap M b I hI) := by
  constructor
  · intro x y h
    apply Subtype.ext
    exact pointMap_injective M (fun _ => 1) b (fun _ => le_rfl) (congrArg Subtype.val h)
  · intro y
    obtain ⟨x, hx, he⟩ := pointMap_surjective_on_locus M b I hI y.val y.property
    exact ⟨⟨x, hx⟩, Subtype.ext he⟩

def locusEquiv : M.zeroLocus I ≃
    (projectiveSpace K N).zeroLocus (diagonalIdeal M (fun _ => 1) b I) :=
  Equiv.ofBijective (locusMap M b I hI) (locusMap_bijective M b I hI)

theorem locusEquiv_regular : M.IsRegularAlong (projectiveSpace K N)
    Subtype.val (fun x => (locusEquiv M b I hI x).val) :=
  (pointMap_regular M (fun _ => 1) b).comp_domain Subtype.val

theorem locusEquiv_inverse_regular : (projectiveSpace K N).IsRegularAlong M
    Subtype.val (fun x => ((locusEquiv M b I hI).symm x).val) := by
  intro x i
  obtain ⟨a, ha⟩ := exists_pureForm_nonzero M b x.val
  let S := (linearForm M (fun _ => 1) b (pureForm M a)).val
  have hS : (projectiveSpace K N).IsHomogeneous S (fun _ => 1) :=
    (MultiProjectiveSpace.projective_homogeneous_iff N S 1).mpr
      (linearForm M (fun _ => 1) b (pureForm M a)).property
  refine ⟨{p | (projectiveSpace K N).eval S p ≠ 0},
    (projectiveSpace K N).isOpen_basic S (fun _ => 1) hS, ha, fun _ => 1,
    fun j => (linearForm M (fun _ => 1) b (replacementForm M a ⟨i, j⟩)).val,
    ?_, ?_⟩
  · intro j
    exact (MultiProjectiveSpace.projective_homogeneous_iff N _ 1).mpr
      (linearForm M (fun _ => 1) b (replacementForm M a ⟨i, j⟩)).property
  · intro y hy
    obtain ⟨q, hq, he, hlift⟩ := exists_inverse_on_pivot M b I hI y.val y.property a hy
    have heq : locusEquiv M b I hI ⟨q, hq⟩ = y := Subtype.ext he
    have hq' : (⟨q, hq⟩ : M.zeroLocus I) = (locusEquiv M b I hI).symm y := by
      rw [← heq, Equiv.symm_apply_apply]
    have hval : q = ((locusEquiv M b I hI).symm y).val := congrArg Subtype.val hq'
    obtain ⟨hn, hpoint⟩ := hlift i
    exact ⟨hn, hpoint.trans (congrFun hval i)⟩

def locusHomeomorph :
    letI := M.zariskiTopology
    letI := (projectiveSpace K N).zariskiTopology
    M.zeroLocus I ≃ₜ (projectiveSpace K N).zeroLocus (diagonalIdeal M (fun _ => 1) b I) := by
  letI := M.zariskiTopology
  letI := (projectiveSpace K N).zariskiTopology
  exact
    { toEquiv := locusEquiv M b I hI
      continuous_toFun := (locusEquiv_regular M b I hI).continuous.subtype_mk _
      continuous_invFun := (locusEquiv_inverse_regular M b I hI).continuous.subtype_mk _ }

end PhilipponMultiplicity.Hilbert.SegreVeronese

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponAffineMapFractions

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MvPolynomial Set
open scoped BigOperators Topology

namespace PhilipponMultiplicity.MultiProjectiveSpace
universe u
variable {K : Type u} [Field K]

theorem eval_ratio_of_lift (M : MultiProjectiveSpace K)
    (p : M.Point) (v : M.Variable → K)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i, j⟩) h = p i)
    (P Q : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q D) :
    MvPolynomial.eval v P / MvPolynomial.eval v Q = M.eval P p / M.eval Q p := by
  classical
  have ha (i : M.FactorIndex) : ∃ a : Kˣ,
      ∀ j, v ⟨i, j⟩ = (a : K) * (p i).rep j := by
    obtain ⟨h, he⟩ := hv i
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ h (p i).rep_nonzero).mp
      (he.trans (p i).mk_rep.symm)
    refine ⟨a, fun j => ?_⟩
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha j).symm
  choose a ha using ha
  have hv' : v = fun j => (a j.1 : K) * M.coordinate p j := by
    funext j
    exact ha j.1 j.2
  have hne : (∏ i, (a i : K) ^ D i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (a i).ne_zero)
  rw [hv', M.eval_block_scale P D hP (M.coordinate p) (fun i => (a i : K)),
    M.eval_block_scale Q D hQ (M.coordinate p) (fun i => (a i : K))]
  exact mul_div_mul_left _ _ hne

theorem IsRegularAlong.local_polynomial_lift
    {X : Type u} {M N : MultiProjectiveSpace K}
    {e : X → M.Point} {f : X → N.Point}
    (hf : M.IsRegularAlong N e f) (S : Set X) {σ : Type*}
    (a : S → σ → K) (L : M.Variable → MvPolynomial σ K)
    (hL : ∀ w : S, ∀ b, ∃ h : (fun i => aeval (a w) (L ⟨b, i⟩)) ≠ 0,
      Projectivization.mk K (fun i => aeval (a w) (L ⟨b, i⟩)) h = e w.val b)
    (z : S) :
    letI : TopologicalSpace X := TopologicalSpace.induced e M.zariskiTopology
    ∃ U : Set S, IsOpen U ∧ z ∈ U ∧
      ∃ R : N.Variable → MvPolynomial σ K,
        ∀ w ∈ U, ∀ b, ∃ h : (fun i => aeval (a w) (R ⟨b, i⟩)) ≠ 0,
          Projectivization.mk K (fun i => aeval (a w) (R ⟨b, i⟩)) h = f w.val b := by
  classical
  letI := M.zariskiTopology
  letI : TopologicalSpace X := TopologicalSpace.induced e M.zariskiTopology
  choose U hU hzU D P hP hrep using hf z.val
  let V : Set S := ⋂ b, (fun w : S => e w.val) ⁻¹' U b
  let R : N.Variable → MvPolynomial σ K := fun t => eval₂ C L (P t.1 t.2)
  refine ⟨V, isOpen_iInter_of_finite (fun b =>
    (hU b).preimage (continuous_induced_dom.comp continuous_subtype_val)),
    mem_iInter.mpr hzU, R, ?_⟩
  intro w hw b
  obtain ⟨hn, he⟩ := hrep b w.val (mem_iInter.mp hw b)
  obtain ⟨hn', he'⟩ := M.homogeneous_tuple_lift (e w.val)
    (fun v => aeval (a w) (L v)) (hL w) (P b) (D b) (hP b) hn
  have heval (i) : aeval (a w) (R ⟨b, i⟩) =
      MvPolynomial.eval (fun v => aeval (a w) (L v)) (P b i) := by
    change MvPolynomial.eval (a w) (eval₂ C L (P b i)) = _
    rw [← eval_assoc]
    rfl
  simpa only [heval] using ⟨hn', he'.trans he⟩

theorem IsRegularAlong.local_fraction_of_target_ratio
    {X : Type u} {M N : MultiProjectiveSpace K}
    {e : X → M.Point} {f : X → N.Point}
    (hf : M.IsRegularAlong N e f) (S : Set X) {σ : Type*}
    (a : S → σ → K) (L : M.Variable → MvPolynomial σ K)
    (hL : ∀ w : S, ∀ b, ∃ h : (fun i => aeval (a w) (L ⟨b, i⟩)) ≠ 0,
      Projectivization.mk K (fun i => aeval (a w) (L ⟨b, i⟩)) h = e w.val b)
    (P Q : N.CoordinateRing) (D : N.FactorIndex → ℕ)
    (hP : N.IsHomogeneous P D) (hQ : N.IsHomogeneous Q D)
    (hQne : ∀ w : S, N.eval Q (f w.val) ≠ 0) (z : S) :
    letI : TopologicalSpace X := TopologicalSpace.induced e M.zariskiTopology
    ∃ U : Set S, IsOpen U ∧ z ∈ U ∧ ∃ A B : MvPolynomial σ K,
      ∀ w ∈ U, aeval (a w) B ≠ 0 ∧
        N.eval P (f w.val) / N.eval Q (f w.val) =
          aeval (a w) A / aeval (a w) B := by
  classical
  letI : TopologicalSpace X := TopologicalSpace.induced e M.zariskiTopology
  obtain ⟨U, hU, hzU, R, hR⟩ := hf.local_polynomial_lift S a L hL z
  refine ⟨U, hU, hzU, eval₂ C R P, eval₂ C R Q, ?_⟩
  intro w hw
  have heval (F : N.CoordinateRing) : aeval (a w) (eval₂ C R F) =
      MvPolynomial.eval (fun v => aeval (a w) (R v)) F := by
    change MvPolynomial.eval (a w) (eval₂ C R F) = _
    rw [← eval_assoc]
    rfl
  simp only [heval]
  exact ⟨(N.eval_eq_zero_iff_of_lift _ _ (hR w hw) Q D hQ).not.mpr (hQne w),
    (N.eval_ratio_of_lift _ _ (hR w hw) P Q D hP hQ).symm⟩

end PhilipponMultiplicity.MultiProjectiveSpace

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponMultihomogenization

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem exists_multihomogenization_on_chart
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (j : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))
    (hbound : ∀ m ∈ P.support, ∀ i,
      (∑ k : Fin (M.ambientDimension i + 1), m ⟨i,k⟩) ≤ D i) :
    ∃ H : M.CoordinateRing, M.IsHomogeneous H D ∧
      ∀ v : M.Variable → K, (∀ i, v ⟨i,j i⟩ = 1) →
        MvPolynomial.eval v H = MvPolynomial.eval v P := by
  classical
  let a (m : M.Variable →₀ ℕ) (i : M.FactorIndex) :=
    ∑ k : Fin (M.ambientDimension i + 1), m ⟨i,k⟩
  let T (m : M.Variable →₀ ℕ) : M.CoordinateRing :=
    monomial m (coeff m P) * ∏ i, X (⟨i,j i⟩ : M.Variable) ^ (D i - a m i)
  refine ⟨∑ m ∈ P.support, T m,?_,?_⟩
  · apply M.isHomogeneous_sum
    intro m hm
    have hmon : M.IsHomogeneous (monomial m (coeff m P)) (a m) := by
      intro n hn i
      have hn' : n = m := Finset.mem_singleton.mp (support_monomial_subset hn)
      subst n
      rfl
    have hpowers := M.isHomogeneous_prod Finset.univ
      (fun i => X (⟨i,j i⟩ : M.Variable) ^ (D i - a m i))
      (fun i k => (D i - a m i) * (if k = i then 1 else 0))
      (fun i _ => (M.isHomogeneous_X ⟨i,j i⟩).pow M (D i - a m i))
    have hdeg : a m + (∑ i : M.FactorIndex,
        fun k => (D i - a m i) * (if k = i then 1 else 0)) = D := by
      funext i
      simp only [Pi.add_apply,Finset.sum_apply,mul_ite,mul_one,mul_zero]
      simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
      exact Nat.add_sub_of_le (hbound m hm i)
    rw [← hdeg]
    exact hmon.mul M hpowers
  · intro v hv
    rw [map_sum]
    calc
      ∑ m ∈ P.support, MvPolynomial.eval v (T m) =
          ∑ m ∈ P.support, MvPolynomial.eval v (monomial m (coeff m P)) := by
        apply Finset.sum_congr rfl
        intro m hm
        simp [T,map_prod,hv]
      _ = MvPolynomial.eval v P := by
        rw [← map_sum,support_sum_monomial_coeff]

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity
variable {K : Type*} [Field K]

end PhilipponMultiplicity

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponStandardAffineChart

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MvPolynomial Set
open scoped BigOperators Topology

namespace PhilipponMultiplicity.StandardAffineChart
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))

def domain : Set M.Point := {x | ∀ i, (x i).rep (b i) ≠ 0}

def equations : Ideal M.CoordinateRing :=
  Ideal.span (Set.range (fun i : M.FactorIndex => X (⟨i, b i⟩ : M.Variable) - 1))

def ideal : Ideal M.CoordinateRing := (equations M b).radical

theorem mem_locus (v : M.Variable → K) :
    v ∈ zeroLocus K (ideal M b) ↔ ∀ i, v ⟨i, b i⟩ = 1 := by
  constructor
  · intro hv i
    have h := hv _ (Ideal.le_radical (Ideal.subset_span (Set.mem_range_self i)))
    simpa only [map_sub, aeval_X, map_one, sub_eq_zero] using h
  · intro hv
    have hI : equations M b ≤ RingHom.ker (aeval v).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change aeval v (X (⟨i, b i⟩ : M.Variable) - 1) = 0
      simp [hv i]
    intro P hP
    exact radical_le_vanishingIdeal_zeroLocus (K := K) (equations M b) hP v
      (fun F hF => hI hF)

def normalize (x : domain M b) : zeroLocus K (ideal M b) :=
  ⟨fun v => (x.val v.1).rep v.2 / (x.val v.1).rep (b v.1),
    (mem_locus M b _).mpr (fun i => div_self (x.property i))⟩

theorem block_ne_zero (v : zeroLocus K (ideal M b)) (i : M.FactorIndex) :
    (fun j => v.val ⟨i, j⟩) ≠ 0 := by
  intro h
  have h0 := congrFun h (b i)
  have h1 := (mem_locus M b v.val).mp v.property i
  exact one_ne_zero (h1.symm.trans h0)

def projectivePoint (v : zeroLocus K (ideal M b)) : M.Point :=
  fun i => Projectivization.mk K (fun j => v.val ⟨i, j⟩) (block_ne_zero M b v i)

theorem projectivePoint_mem (v : zeroLocus K (ideal M b)) :
    projectivePoint M b v ∈ domain M b := by
  intro i hz
  have hlift (k : M.FactorIndex) : ∃ h : (fun j => v.val ⟨k, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v.val ⟨k, j⟩) h = projectivePoint M b v k :=
    ⟨block_ne_zero M b v k, rfl⟩
  have hn := (M.eval_eq_zero_iff_of_lift _ v.val hlift (X ⟨i, b i⟩) _
    (M.isHomogeneous_X _)).mpr (by
      simpa only [MultiProjectiveSpace.eval, eval_X, MultiProjectiveSpace.coordinate] using hz)
  have h1 := (mem_locus M b v.val).mp v.property i
  exact one_ne_zero (h1.symm.trans (by simpa using hn))

def denormalize (v : zeroLocus K (ideal M b)) : domain M b :=
  ⟨projectivePoint M b v, projectivePoint_mem M b v⟩

theorem normalize_denormalize (v : zeroLocus K (ideal M b)) :
    normalize M b (denormalize M b v) = v := by
  apply Subtype.ext
  funext t
  have hlift (i : M.FactorIndex) : ∃ h : (fun j => v.val ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v.val ⟨i, j⟩) h = projectivePoint M b v i :=
    ⟨block_ne_zero M b v i, rfl⟩
  have h := M.eval_ratio_of_lift _ v.val hlift (X t) (X ⟨t.1, b t.1⟩) _
    (M.isHomogeneous_X t) (M.isHomogeneous_X ⟨t.1, b t.1⟩)
  have h1 := (mem_locus M b v.val).mp v.property t.1
  simpa only [normalize, denormalize, MultiProjectiveSpace.eval, MultiProjectiveSpace.coordinate,
    eval_X, h1, div_one] using h.symm

theorem denormalize_normalize (x : domain M b) :
    denormalize M b (normalize M b x) = x := by
  apply Subtype.ext
  funext i
  apply Eq.trans ?_ (x.val i).mk_rep
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
  refine ⟨((x.val i).rep (b i))⁻¹, ?_⟩
  funext j
  change ((x.val i).rep (b i))⁻¹ * (x.val i).rep j =
    (x.val i).rep j / (x.val i).rep (b i)
  simp only [div_eq_mul_inv, mul_comm]

theorem domain_isOpen : @IsOpen M.Point M.zariskiTopology (domain M b) := by
  letI := M.zariskiTopology
  change IsOpen {x : M.Point | ∀ i, (x i).rep (b i) ≠ 0}
  rw [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  simpa only [MultiProjectiveSpace.eval, eval_X, MultiProjectiveSpace.coordinate] using
    M.isOpen_basic (X ⟨i, b i⟩) _ (M.isHomogeneous_X _)

theorem normalize_represents (x : domain M b) (i : M.FactorIndex) :
    ∃ h : (fun j => (normalize M b x).val ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => (normalize M b x).val ⟨i, j⟩) h = x.val i := by
  refine ⟨block_ne_zero M b (normalize M b x) i, ?_⟩
  exact congrFun (congrArg Subtype.val (denormalize_normalize M b x)) i

theorem normalize_continuous :
    letI := M.zariskiTopology
    letI := AffineClosedPoints.locusTopology (ideal M b)
    Continuous (normalize M b) := by
  classical
  letI := M.zariskiTopology
  letI := AffineClosedPoints.locusTopology (ideal M b)
  apply (AffineClosedPoints.nonzero_sets_basis (ideal M b)).continuous_iff.mpr
  rintro _ ⟨P, rfl⟩
  let D : M.FactorIndex → ℕ := fun i =>
    ∑ m ∈ P.support, ∑ j : Fin (M.ambientDimension i + 1), m ⟨i, j⟩
  obtain ⟨H, hH, heval⟩ := M.exists_multihomogenization_on_chart P D b (by
    intro m hm i
    dsimp only [D]
    exact Finset.single_le_sum
      (f := fun m : M.Variable →₀ ℕ => ∑ j : Fin (M.ambientDimension i + 1), m ⟨i, j⟩)
      (fun _ _ => Nat.zero_le _) hm)
  have hset : (normalize M b) ⁻¹' {v | aeval v.val P ≠ 0} =
      {x : domain M b | M.eval H x.val ≠ 0} := by
    ext x
    have hn := heval (normalize M b x).val
      ((mem_locus M b _).mp (normalize M b x).property)
    have hiff := M.eval_eq_zero_iff_of_lift x.val (normalize M b x).val
      (normalize_represents M b x) H D hH
    rw [hn] at hiff
    exact hiff.not
  rw [hset]
  exact (M.isOpen_basic H D hH).preimage continuous_subtype_val

theorem denormalize_continuous :
    letI := M.zariskiTopology
    letI := AffineClosedPoints.locusTopology (ideal M b)
    Continuous (denormalize M b) := by
  classical
  letI := M.zariskiTopology
  letI := AffineClosedPoints.locusTopology (ideal M b)
  apply Continuous.subtype_mk
  change Continuous (projectivePoint M b)
  apply continuous_generateFrom_iff.mpr
  rintro _ ⟨P, D, hP, rfl⟩
  have hset : (projectivePoint M b) ⁻¹' {p | M.eval P p ≠ 0} =
      {v : zeroLocus K (ideal M b) | aeval v.val P ≠ 0} := by
    ext v
    have hlift (i : M.FactorIndex) : ∃ h : (fun j => v.val ⟨i, j⟩) ≠ 0,
        Projectivization.mk K (fun j => v.val ⟨i, j⟩) h = projectivePoint M b v i :=
      ⟨block_ne_zero M b v i, rfl⟩
    exact (M.eval_eq_zero_iff_of_lift _ v.val hlift P D hP).not.symm
  rw [hset]
  exact (AffineClosedPoints.nonzero_sets_basis (ideal M b)).isOpen (Set.mem_range_self P)

end PhilipponMultiplicity.StandardAffineChart

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectiveSchemePoints

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity.ProjectiveCoordinateScheme

open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped Topology

universe u
variable {K : Type u} [Field K] {σ : Type}

attribute [local instance] MvPolynomial.gradedAlgebra

def chartRationalPoint (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (j : σ)
    (x : zeroLocus K (chartIdeal I j)) : Spec (.of K) ⟶ scheme I hI :=
  Spec.map (CommRingCat.ofHom (AffineClosedPoints.evaluation (chartIdeal I j) x).toRingHom) ≫
    chartImmersion I hI j

theorem chartRationalPoint_over (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (j : σ)
    (x : zeroLocus K (chartIdeal I j)) :
    chartRationalPoint I hI j x ≫ structureMap I hI = 𝟙 (Spec (.of K)) := by
  unfold chartRationalPoint
  rw [Category.assoc, chartImmersion_over]
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  have he : CommRingCat.ofHom (algebraMap K (MvPolynomial σ K ⧸ chartIdeal I j)) ≫
      CommRingCat.ofHom (AffineClosedPoints.evaluation (chartIdeal I j) x).toRingHom =
        𝟙 (CommRingCat.of K) := by
    apply CommRingCat.hom_ext
    ext a
    exact (AffineClosedPoints.evaluation (chartIdeal I j) x).commutes a
  rw [he, Spec.map_id]

theorem chartRationalPoint_value (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (j : σ)
    (x : zeroLocus K (chartIdeal I j)) :
    chartRationalPoint I hI j x (IsLocalRing.closedPoint K) =
      chartImmersion I hI j (AffineClosedPoints.point (chartIdeal I j) x).toPrimeSpectrum := by
  change chartImmersion I hI j
    (Spec.map (CommRingCat.ofHom (AffineClosedPoints.evaluation (chartIdeal I j) x).toRingHom)
      (IsLocalRing.closedPoint K)) = _
  congr 1
  rw [Subsingleton.elim (IsLocalRing.closedPoint K) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)]
  rfl

theorem chartPoint_isClosed (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (j : σ)
    (x : zeroLocus K (chartIdeal I j)) :
    IsClosed {chartImmersion I hI j (AffineClosedPoints.point (chartIdeal I j) x).toPrimeSpectrum} := by
  letI : IsClosedImmersion (chartRationalPoint I hI j x) :=
    isClosedImmersion_of_comp_eq_id _ _ (chartRationalPoint_over I hI j x)
  have h := (chartRationalPoint I hI j x).isClosedEmbedding.isClosed_range
  have he : Set.range (chartRationalPoint I hI j x) =
      {chartRationalPoint I hI j x (IsLocalRing.closedPoint K)} := by
    apply Set.range_eq_singleton
    exact fun y => congrArg _ (Subsingleton.elim y _)
  rwa [he, chartRationalPoint_value] at h

theorem closed_points_covered [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    (x : scheme I hI) (hx : IsClosed {x}) :
    ∃ (j : σ) (y : zeroLocus K (chartIdeal I j)),
      chartImmersion I hI j (AffineClosedPoints.point (chartIdeal I j) y).toPrimeSpectrum = x := by
  have hxcover : x ∈ ⨆ j, chartOpen I hI j := by rw [iSup_chartOpen]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hxcover
  letI := chartImmersion_isOpenImmersion I hI j
  have hxr : x ∈ (chartImmersion I hI j).opensRange := by
    rw [chartImmersion_opensRange]
    exact hj
  obtain ⟨a, ha⟩ := hxr
  have hpre : (chartImmersion I hI j) ⁻¹' {x} = {a} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [← ha, (chartImmersion I hI j).isOpenEmbedding.injective.eq_iff]
  have hac : IsClosed ({a} : Set (PrimeSpectrum (MvPolynomial σ K ⧸ chartIdeal I j))) := by
    rw [← hpre]
    exact hx.preimage (chartImmersion I hI j).continuous
  have ham := (PrimeSpectrum.isClosed_singleton_iff_isMaximal a).mp hac
  obtain ⟨y, hy⟩ := AffineClosedPoints.point_surjective (chartIdeal I j) ⟨a.asIdeal, ham⟩
  refine ⟨j, y, ?_⟩
  have hy' : (AffineClosedPoints.point (chartIdeal I j) y).toPrimeSpectrum = a :=
    PrimeSpectrum.ext (congrArg MaximalSpectrum.asIdeal hy)
  rw [hy']
  exact ha

end PhilipponMultiplicity.ProjectiveCoordinateScheme

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectiveHilbertExistence

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity
open SectionThree

theorem vanishingIdeal_multihomogeneous (K : Type*) [Field K]
    (M : MultiProjectiveSpace K) (S : Set M.Point) :
    IsMultihomogeneousIdeal M (M.vanishingIdeal S) := by
  classical
  let w := Hilbert.blockWeight M.factorCount M.ambientDimension
  letI := MvPolynomial.weightedGradedAlgebra K w
  have hh : (M.vanishingIdeal S).IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    apply Ideal.homogeneous_span
    intro P hP
    obtain ⟨D, hD⟩ := hP.1
    refine ⟨D, ?_⟩
    intro e he
    funext i
    rw [MonomialCells.weight_apply]
    exact hD e (mem_support_iff.mpr he) i
  intro P hP d
  exact weightedHomogeneousComponent_mem_of_mem K w hh hP d

end PhilipponMultiplicity

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponGroupReduced

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem Hilbert.radical_multihomogeneous (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) : IsMultihomogeneousIdeal M I.radical := by
  classical
  let w : M.Variable → Lex (M.FactorIndex → ℕ) :=
    fun x => toLex (Hilbert.blockWeight M.factorCount M.ambientDimension x)
  letI : DecidableEq (Lex (M.FactorIndex → ℕ)) := LinearOrder.toDecidableEq
  letI := weightedGradedAlgebra K w
  have hproj (f : M.CoordinateRing) (d : Lex (M.FactorIndex → ℕ)) :
      weightedHomogeneousComponent w d f =
        weightedHomogeneousComponent (Hilbert.blockWeight M.factorCount M.ambientDimension)
          (ofLex d) f := by
    ext e
    simp only [coeff_weightedHomogeneousComponent]
    rfl
  have hIg : I.IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    intro d f hf
    change ((MvPolynomial.decompose' K w f) d : M.CoordinateRing) ∈ I
    rw [MvPolynomial.decompose'_apply, hproj]
    exact hI f hf (ofLex d)
  intro f hf d
  have h := weightedHomogeneousComponent_mem_of_mem K w hIg.radical hf (toLex d)
  rwa [hproj] at h

theorem MultiProjectiveSpace.vanishingIdeal_isRadical (S : Set M.Point) :
    (M.vanishingIdeal S).IsRadical := by
  apply Ideal.radical_eq_iff.mp
  apply le_antisymm ?_ Ideal.le_radical
  rw [M.homogeneousIdeal_eq_span _
    (Hilbert.radical_multihomogeneous M _ (vanishingIdeal_multihomogeneous K M S))]
  apply Ideal.span_le.mpr
  rintro P ⟨hP, D, hD⟩
  obtain ⟨n, hn⟩ := hP
  refine Ideal.subset_span ⟨⟨D, hD⟩, ?_⟩
  intro x hx
  have h := M.eval_eq_zero_of_mem_vanishingIdeal hn hx
  change MvPolynomial.eval (M.coordinate x) (P ^ n) = 0 at h
  rw [map_pow] at h
  exact eq_zero_of_pow_eq_zero h

end PhilipponMultiplicity

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponSegreVeroneseScheme

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity.Hilbert.SegreVeronese

open AlgebraicGeometry CategoryTheory MvPolynomial

universe u
variable {K : Type u} [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ordinaryIdeal_isHomogeneous (N : ℕ) (I : Ideal (projectiveSpace K N).CoordinateRing)
    (hI : IsMultihomogeneousIdeal (projectiveSpace K N) I) :
    I.IsHomogeneous (homogeneousSubmodule (projectiveSpace K N).Variable K) := by
  intro n P hP
  have h := hI P hP (fun _ => n)
  change weightedHomogeneousComponent (blockWeight 1 (fun _ => N)) (fun _ => n) P ∈ I at h
  rw [ordinary_component_eq] at h
  change ((MvPolynomial.decompose' K (1 : (projectiveSpace K N).Variable → ℕ) P) n :
    (projectiveSpace K N).CoordinateRing) ∈ I
  rw [MvPolynomial.decompose'_apply]
  exact h

variable (M : MultiProjectiveSpace K) (D : M.FactorIndex → ℕ) {N : ℕ}
  (b : Module.Basis (projectiveSpace K N).Variable K
    (degreePiece K M.factorCount M.ambientDimension D))

def scheme (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (hD : ∀ i, 1 ≤ D i) : Scheme.{u} :=
  ProjectiveCoordinateScheme.scheme (diagonalIdeal M D b I)
    (ordinaryIdeal_isHomogeneous N _ (diagonalIdeal_homogeneous M D b hD I hI))

def structureMap (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (hD : ∀ i, 1 ≤ D i) : scheme M D b I hI hD ⟶ Spec (.of K) :=
  ProjectiveCoordinateScheme.structureMap (diagonalIdeal M D b I)
    (ordinaryIdeal_isHomogeneous N _ (diagonalIdeal_homogeneous M D b hD I hI))

theorem structureMap_isProper (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (hD : ∀ i, 1 ≤ D i) :
    IsProper (structureMap M D b I hI hD) :=
  ProjectiveCoordinateScheme.structureMap_isProper _ _

end PhilipponMultiplicity.Hilbert.SegreVeronese

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponNormalizedProjectiveLocus

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.StandardAffineChart

open MvPolynomial
open scoped Topology

variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))

def normalizedIdeal : Ideal M.CoordinateRing := I ⊔ equations M b

theorem mem_normalized_locus (v : M.Variable → K) :
    v ∈ zeroLocus K (normalizedIdeal M I b) ↔
      v ∈ zeroLocus K I ∧ ∀ i, v ⟨i, b i⟩ = 1 := by
  constructor
  · intro hv
    refine ⟨fun P hP => hv P ((le_sup_left : I ≤ normalizedIdeal M I b) hP), fun i => ?_⟩
    have h := hv _ ((le_sup_right : equations M b ≤ normalizedIdeal M I b)
      (Ideal.subset_span (Set.mem_range_self i)))
    simpa only [map_sub, aeval_X, map_one, sub_eq_zero] using h
  · rintro ⟨hI, hb⟩
    have hker : normalizedIdeal M I b ≤ RingHom.ker (aeval v).toRingHom := by
      refine sup_le hI (Ideal.span_le.mpr ?_)
      rintro _ ⟨i, rfl⟩
      change aeval v (X (⟨i, b i⟩ : M.Variable) - 1) = 0
      simp [hb i]
    exact fun P hP => hker hP

theorem normalize_mem_iff (hI : IsMultihomogeneousIdeal M I)
    (x : domain M b) :
    (normalize M b x).val ∈ zeroLocus K I ↔ x.val ∈ M.zeroLocus I := by
  constructor
  · intro hx
    apply (M.mem_zeroLocus_iff_homogeneous I hI x.val).mpr
    intro P hP D hD
    exact (M.eval_eq_zero_iff_of_lift _ _ (normalize_represents M b x) P D hD).mp
      (hx P hP)
  · intro hx
    have hker : I ≤ RingHom.ker (aeval (normalize M b x).val).toRingHom := by
      rw [M.homogeneousIdeal_eq_span I hI]
      apply Ideal.span_le.mpr
      rintro P ⟨hP, D, hD⟩
      exact (M.eval_eq_zero_iff_of_lift _ _ (normalize_represents M b x) P D hD).mpr
        (hx P hP)
    exact fun P hP => hker hP

def locus : Set (domain M b) := {x | x.val ∈ M.zeroLocus I}

def normalizeLocus (hI : IsMultihomogeneousIdeal M I)
    (x : locus M I b) : zeroLocus K (normalizedIdeal M I b) :=
  ⟨(normalize M b x.val).val, (mem_normalized_locus M I b _).mpr
    ⟨(normalize_mem_iff M I b hI x.val).mpr x.property,
      (mem_locus M b _).mp (normalize M b x.val).property⟩⟩

def normalizedRestriction (x : zeroLocus K (normalizedIdeal M I b)) :
    zeroLocus K (ideal M b) :=
  ⟨x.val, (mem_locus M b _).mpr ((mem_normalized_locus M I b _).mp x.property).2⟩

def denormalizeLocus (hI : IsMultihomogeneousIdeal M I)
    (x : zeroLocus K (normalizedIdeal M I b)) : locus M I b := by
  refine ⟨denormalize M b (normalizedRestriction M I b x), ?_⟩
  apply (normalize_mem_iff M I b hI _).mp
  rw [normalize_denormalize]
  exact ((mem_normalized_locus M I b _).mp x.property).1

theorem denormalizeLocus_normalizeLocus (hI : IsMultihomogeneousIdeal M I)
    (x : locus M I b) :
    denormalizeLocus M I b hI (normalizeLocus M I b hI x) = x := by
  apply Subtype.ext
  exact denormalize_normalize M b x.val

theorem normalizeLocus_denormalizeLocus (hI : IsMultihomogeneousIdeal M I)
    (x : zeroLocus K (normalizedIdeal M I b)) :
    normalizeLocus M I b hI (denormalizeLocus M I b hI x) = x := by
  apply Subtype.ext
  change (normalize M b (denormalize M b (normalizedRestriction M I b x))).val = x.val
  exact congrArg Subtype.val (normalize_denormalize M b (normalizedRestriction M I b x))

def locusEquiv (hI : IsMultihomogeneousIdeal M I) :
    locus M I b ≃ zeroLocus K (normalizedIdeal M I b) where
  toFun := normalizeLocus M I b hI
  invFun := denormalizeLocus M I b hI
  left_inv := denormalizeLocus_normalizeLocus M I b hI
  right_inv := normalizeLocus_denormalizeLocus M I b hI

def locusHomeomorph (hI : IsMultihomogeneousIdeal M I) :
    letI := M.zariskiTopology
    letI := AffineClosedPoints.locusTopology (normalizedIdeal M I b)
    locus M I b ≃ₜ zeroLocus K (normalizedIdeal M I b) := by
  letI := M.zariskiTopology
  letI := AffineClosedPoints.locusTopology (normalizedIdeal M I b)
  refine { locusEquiv M I b hI with continuous_toFun := ?_, continuous_invFun := ?_ }
  · apply (AffineClosedPoints.nonzero_sets_basis (normalizedIdeal M I b)).continuous_iff.mpr
    rintro _ ⟨P, rfl⟩
    letI := AffineClosedPoints.locusTopology (ideal M b)
    exact ((AffineClosedPoints.nonzero_sets_basis (ideal M b)).isOpen
      (Set.mem_range_self P)).preimage ((normalize_continuous M b).comp continuous_subtype_val)
  · apply Continuous.subtype_mk
    letI := AffineClosedPoints.locusTopology (ideal M b)
    apply (denormalize_continuous M b).comp
    apply (AffineClosedPoints.nonzero_sets_basis (ideal M b)).continuous_iff.mpr
    rintro _ ⟨P, rfl⟩
    exact (AffineClosedPoints.nonzero_sets_basis (normalizedIdeal M I b)).isOpen
      (Set.mem_range_self P)

end PhilipponMultiplicity.StandardAffineChart

namespace PhilipponMultiplicity.ProjectiveCoordinateScheme

open MvPolynomial

variable {K : Type*} [Field K] (N : ℕ)
    (I : Ideal (projectiveSpace K N).CoordinateRing) (j : Fin (N + 1))

theorem normalizedIdeal_single :
    StandardAffineChart.normalizedIdeal (projectiveSpace K N) I (fun _ => j) =
      chartIdeal I ⟨(0 : Fin 1), j⟩ := by
  letI : Nonempty (projectiveSpace K N).FactorIndex := ⟨(0 : Fin 1)⟩
  unfold StandardAffineChart.normalizedIdeal StandardAffineChart.equations
    chartIdeal HomogeneousQuotientGrading.normalizedIdeal
  congr 2
  apply Set.range_eq_singleton
  intro i
  congr 2
  cases Subsingleton.elim (α := Fin 1) i (0 : Fin 1)
  rfl

end PhilipponMultiplicity.ProjectiveCoordinateScheme

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectiveChartEvaluations

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ProjectiveCoordinateScheme

open MvPolynomial AlgebraicGeometry CategoryTheory

universe u
variable {K : Type u} [Field K] {σ : Type}

attribute [local instance] MvPolynomial.gradedAlgebra

attribute [local instance] zeroAlgebra zeroSMul

def polynomialOpen (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (P : MvPolynomial σ K) :
    (scheme I hI).Opens := by
  letI := HomogeneousQuotientGrading.gradedAlgebra (homogeneousSubmodule σ K) I hI
  exact Proj.basicOpen (grading I) (Ideal.Quotient.mk I P)

theorem chartPoint_mem_polynomialOpen (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (j : σ)
    (x : zeroLocus K (chartIdeal I j)) (P : MvPolynomial σ K)
    (n : ℕ) (hP : P.IsHomogeneous n) (hn : 0 < n) :
    chartImmersion I hI j (AffineClosedPoints.point (chartIdeal I j) x).toPrimeSpectrum ∈
      polynomialOpen I hI P ↔ aeval x.val P ≠ 0 := by
  letI := HomogeneousQuotientGrading.gradedAlgebra (homogeneousSubmodule σ K) I hI
  let e := HomogeneousQuotientGrading.normalizedRingEquiv
    (homogeneousSubmodule σ K) I (isHomogeneous_X K j)
  let hf := HomogeneousQuotientGrading.quotient_mem_piece
    (homogeneousSubmodule σ K) I (isHomogeneous_X K j)
  let hg := HomogeneousQuotientGrading.quotient_mem_piece
    (homogeneousSubmodule σ K) I hP
  have himm : chartImmersion I hI j =
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        Proj.awayι (grading I) (Ideal.Quotient.mk I (X j)) hf (by decide) := rfl
  rw [himm]
  change PrimeSpectrum.comap e.toRingHom
      (AffineClosedPoints.point (chartIdeal I j) x).toPrimeSpectrum ∈
    (Proj.awayι (grading I) (Ideal.Quotient.mk I (X j)) hf (by decide)) ⁻¹ᵁ
      Proj.basicOpen (grading I) (Ideal.Quotient.mk I P) ↔ _
  rw [Proj.awayι_preimage_basicOpen (grading I) hf (by decide) hg hn]
  change e (HomogeneousLocalization.Away.isLocalizationElem hf hg) ∉
      (AffineClosedPoints.point (chartIdeal I j) x).asIdeal ↔ _
  have he : e (HomogeneousLocalization.Away.isLocalizationElem hf hg) =
      Ideal.Quotient.mk (chartIdeal I j) P := by
    convert HomogeneousQuotientGrading.normalizedRingEquiv_mk
      (homogeneousSubmodule σ K) I (isHomogeneous_X K j) n P hP using 1 <;> try rfl
    congr 1
    apply HomogeneousLocalization.val_injective
    simp only [HomogeneousLocalization.Away.val_mk, pow_one]
  rw [he]
  rfl

theorem point_ext_positive (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    {x y : scheme I hI}
    (h : ∀ n : ℕ, 0 < n → ∀ P : MvPolynomial σ K, P.IsHomogeneous n →
      (x ∈ polynomialOpen I hI P ↔ y ∈ polynomialOpen I hI P)) : x = y := by
  letI := HomogeneousQuotientGrading.gradedAlgebra (homogeneousSubmodule σ K) I hI
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro n a ha
  obtain ⟨P, hP, rfl⟩ := ha
  by_cases hn : n = 0
  · subst n
    have hC : P = C (P.coeff 0) :=
      (homogeneousComponent_of_mem hP).symm.trans (homogeneousComponent_zero _)
    rw [hC]
    by_cases hc : P.coeff 0 = 0
    · simp [hc]
    · have hu : IsUnit (Ideal.Quotient.mk I (C (P.coeff 0))) :=
        ((isUnit_iff_ne_zero.mpr hc).map C).map (Ideal.Quotient.mk I)
      exact iff_of_false (Ideal.notMem_of_isUnit _ hu) (Ideal.notMem_of_isUnit _ hu)
  · exact not_iff_not.mp (h n (Nat.pos_of_ne_zero hn) P hP)

end PhilipponMultiplicity.ProjectiveCoordinateScheme

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectivePointSeparation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MvPolynomial
namespace PhilipponMultiplicity.MultiProjectiveSpace

theorem point_eq_of_homogeneous_implication {K : Type*} [Field K]
    (M : MultiProjectiveSpace K) (x y : M.Point)
    (h : ∀ (P : M.CoordinateRing) (D : M.FactorIndex → ℕ),
      M.IsHomogeneous P D → M.eval P y = 0 → M.eval P x = 0) : x = y := by
  classical
  funext i
  obtain ⟨k, hk⟩ := Function.ne_iff.mp (Projectivization.rep_nonzero (y i))
  change (y i).rep k ≠ 0 at hk
  have heq (j : Fin (M.ambientDimension i + 1)) :
      (y i).rep k * (x i).rep j - (y i).rep j * (x i).rep k = 0 := by
    have hP := (M.isHomogeneous_X ⟨i, j⟩).C_mul M ((y i).rep k)
    have hQ := (M.isHomogeneous_X ⟨i, k⟩).C_mul M ((y i).rep j)
    have hh := h _ _ (hP.sub M hQ) (by simp [eval, coordinate, mul_comm])
    simpa [eval, coordinate] using hh
  rw [← Projectivization.mk_rep (x i), ← Projectivization.mk_rep (y i)]
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
  exact ⟨(x i).rep k / (y i).rep k, by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div]
    apply (div_eq_iff hk).mpr
    simpa only [mul_comm] using (sub_eq_zero.mp (heq j)).symm⟩

end PhilipponMultiplicity.MultiProjectiveSpace

namespace WeierstrassEllipticZeta.PhilipponApplication.Model
open PhilipponMultiplicity

end WeierstrassEllipticZeta.PhilipponApplication.Model
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectivePointComparison

set_option autoImplicit false
set_option maxHeartbeats 150000
set_option synthInstance.maxHeartbeats 1000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ProjectivePointComparison

open MvPolynomial AlgebraicGeometry CategoryTheory
open StandardAffineChart

universe u
variable {K : Type u} [Field K] (N : ℕ)
    (I : Ideal (projectiveSpace K N).CoordinateRing)
    (hI : IsMultihomogeneousIdeal (projectiveSpace K N) I)

abbrev ordinaryHomogeneous := Hilbert.SegreVeronese.ordinaryIdeal_isHomogeneous N I hI

abbrev scheme := ProjectiveCoordinateScheme.scheme I (ordinaryHomogeneous N I hI)

def coordinates (j : Fin (N + 1)) :
    locus (projectiveSpace K N) I (fun _ => j) ≃
      zeroLocus K (ProjectiveCoordinateScheme.chartIdeal I ⟨(0 : Fin 1), j⟩) :=
  (locusEquiv (projectiveSpace K N) I (fun _ => j) hI).trans
    (Equiv.setCongr (congrArg (zeroLocus K)
      (ProjectiveCoordinateScheme.normalizedIdeal_single N I j)))

theorem coordinates_val (j : Fin (N + 1))
    (x : locus (projectiveSpace K N) I (fun _ => j)) :
    (coordinates N I hI j x).val =
      (normalize (projectiveSpace K N) (fun _ => j) x.val).val := rfl

def pointInChart (j : Fin (N + 1))
    (x : locus (projectiveSpace K N) I (fun _ => j)) : scheme N I hI :=
  ProjectiveCoordinateScheme.chartImmersion I (ordinaryHomogeneous N I hI) ⟨(0 : Fin 1), j⟩
    (AffineClosedPoints.point _ (coordinates N I hI j x)).toPrimeSpectrum

theorem pointInChart_mem_polynomialOpen (j : Fin (N + 1))
    (x : locus (projectiveSpace K N) I (fun _ => j))
    (P : (projectiveSpace K N).CoordinateRing) (n : ℕ) (hP : P.IsHomogeneous n)
    (hn : 0 < n) :
    pointInChart N I hI j x ∈
      ProjectiveCoordinateScheme.polynomialOpen I (ordinaryHomogeneous N I hI) P ↔
      (projectiveSpace K N).eval P x.val.val ≠ 0 := by
  rw [pointInChart, ProjectiveCoordinateScheme.chartPoint_mem_polynomialOpen
    I (ordinaryHomogeneous N I hI) _ _ P n hP hn, coordinates_val]
  exact ((projectiveSpace K N).eval_eq_zero_iff_of_lift _ _
    (normalize_represents (projectiveSpace K N) (fun _ => j) x.val) P (fun _ => n)
    ((MultiProjectiveSpace.projective_homogeneous_iff N P n).mpr hP)).not

theorem pointInChart_eq (j k : Fin (N + 1))
    (x : locus (projectiveSpace K N) I (fun _ => j))
    (y : locus (projectiveSpace K N) I (fun _ => k)) (hxy : x.val.val = y.val.val) :
    pointInChart N I hI j x = pointInChart N I hI k y := by
  apply ProjectiveCoordinateScheme.point_ext_positive
  intro n hn P hP
  rw [pointInChart_mem_polynomialOpen N I hI j x P n hP hn,
    pointInChart_mem_polynomialOpen N I hI k y P n hP hn, hxy]

def pivot (x : (projectiveSpace K N).zeroLocus I) : Fin (N + 1) :=
  (Function.ne_iff.mp (x.val (0 : Fin 1)).rep_nonzero).choose

def onChart (x : (projectiveSpace K N).zeroLocus I) :
    locus (projectiveSpace K N) I (fun _ => pivot N I x) := by
  refine ⟨⟨x.val, ?_⟩, x.property⟩
  intro i
  have hi : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
  subst i
  exact (Function.ne_iff.mp (x.val (0 : Fin 1)).rep_nonzero).choose_spec

def point (x : (projectiveSpace K N).zeroLocus I) : scheme N I hI :=
  pointInChart N I hI (pivot N I x) (onChart N I x)

theorem point_eq_pointInChart (j : Fin (N + 1))
    (x : locus (projectiveSpace K N) I (fun _ => j)) :
    point N I hI ⟨x.val.val, x.property⟩ = pointInChart N I hI j x :=
  pointInChart_eq N I hI _ _ _ _ rfl

theorem point_mem_polynomialOpen (x : (projectiveSpace K N).zeroLocus I)
    (P : (projectiveSpace K N).CoordinateRing) (n : ℕ) (hP : P.IsHomogeneous n)
    (hn : 0 < n) :
    point N I hI x ∈
      ProjectiveCoordinateScheme.polynomialOpen I (ordinaryHomogeneous N I hI) P ↔
      (projectiveSpace K N).eval P x.val ≠ 0 :=
  pointInChart_mem_polynomialOpen N I hI _ _ P n hP hn

theorem point_isClosed (x : (projectiveSpace K N).zeroLocus I) :
    IsClosed {point N I hI x} :=
  ProjectiveCoordinateScheme.chartPoint_isClosed I (ordinaryHomogeneous N I hI) _ _

theorem point_injective : Function.Injective (point N I hI) := by
  intro x y hxy
  apply Subtype.ext
  apply (projectiveSpace K N).point_eq_of_homogeneous_implication
  intro P D hP hy
  have hD : D = fun _ => D (0 : Fin 1) :=
    funext (fun i => congrArg D (Subsingleton.elim (α := Fin 1) i (0 : Fin 1)))
  rw [hD] at hP
  have hp := (MultiProjectiveSpace.projective_homogeneous_iff N P (D (0 : Fin 1))).mp hP
  by_cases hn : D (0 : Fin 1) = 0
  · rw [hn] at hp
    have hC : P = C (P.coeff 0) :=
      (homogeneousComponent_of_mem hp).symm.trans (homogeneousComponent_zero _)
    rw [hC] at hy ⊢
    simpa only [MultiProjectiveSpace.eval, eval_C] using hy
  · have he := (point_mem_polynomialOpen N I hI x P _ hp (Nat.pos_of_ne_zero hn)).symm.trans
      (hxy ▸ point_mem_polynomialOpen N I hI y P _ hp (Nat.pos_of_ne_zero hn))
    exact not_iff_not.mp he |>.mpr hy

theorem closed_points_surjective [IsAlgClosed K] (z : scheme N I hI) (hz : IsClosed {z}) :
    ∃ x, point N I hI x = z := by
  obtain ⟨⟨i, j⟩, y, hy⟩ := ProjectiveCoordinateScheme.closed_points_covered
    I (ordinaryHomogeneous N I hI) z hz
  have hi : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
  subst i
  let x := (coordinates N I hI j).symm y
  refine ⟨⟨x.val.val, x.property⟩, ?_⟩
  rw [point_eq_pointInChart]
  change ProjectiveCoordinateScheme.chartImmersion I _ _
      (AffineClosedPoints.point _ (coordinates N I hI j x)).toPrimeSpectrum = z
  rw [show coordinates N I hI j x = y from (coordinates N I hI j).apply_symm_apply y]
  exact hy

def closedPointEquiv [IsAlgClosed K] :
    (projectiveSpace K N).zeroLocus I ≃ {z : scheme N I hI // IsClosed {z}} :=
  Equiv.ofBijective (fun x => ⟨point N I hI x, point_isClosed N I hI x⟩)
    ⟨fun _ _ h => point_injective N I hI (congrArg Subtype.val h), by
      rintro ⟨z, hz⟩
      obtain ⟨x, hx⟩ := closed_points_surjective N I hI z hz
      exact ⟨x, Subtype.ext hx⟩⟩

end PhilipponMultiplicity.ProjectivePointComparison

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectivePolynomialBasis

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 1000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ProjectiveCoordinateScheme

open MvPolynomial AlgebraicGeometry CategoryTheory
open scoped Topology

universe u
variable {K : Type u} [Field K] {σ : Type}

attribute [local instance] MvPolynomial.gradedAlgebra zeroAlgebra zeroSMul

theorem mem_polynomialOpen_C (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (x : scheme I hI) (c : K) :
    x ∈ polynomialOpen I hI (C c) ↔ c ≠ 0 := by
  letI := HomogeneousQuotientGrading.gradedAlgebra (homogeneousSubmodule σ K) I hI
  change Ideal.Quotient.mk I (C c) ∉ x.asHomogeneousIdeal ↔ c ≠ 0
  by_cases hc : c = 0
  · simp [hc]
  · have hu : IsUnit (Ideal.Quotient.mk I (C c)) :=
      ((isUnit_iff_ne_zero.mpr hc).map C).map (Ideal.Quotient.mk I)
    exact iff_of_true (Ideal.notMem_of_isUnit _ hu) hc

theorem homogeneous_polynomial_basis (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) :
    TopologicalSpace.IsTopologicalBasis
      {U : Set (scheme I hI) | ∃ n : ℕ, ∃ P : MvPolynomial σ K,
        P.IsHomogeneous n ∧ U = polynomialOpen I hI P} := by
  letI := HomogeneousQuotientGrading.gradedAlgebra (homogeneousSubmodule σ K) I hI
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro _ ⟨n, P, hP, rfl⟩
    exact (polynomialOpen I hI P).isOpen
  · intro x U hx hU
    obtain ⟨_, ⟨a, rfl⟩, hxa, haU⟩ :=
      (ProjectiveSpectrum.isTopologicalBasis_basic_opens (grading I)).exists_subset_of_mem_open hx hU
    have hxproj : x ∈ ⨆ n, Proj.basicOpen (grading I) (GradedRing.proj (grading I) n a) := by
      rw [← Proj.basicOpen_eq_iSup_proj]
      exact hxa
    obtain ⟨n, hn⟩ := TopologicalSpace.Opens.mem_iSup.mp hxproj
    have hpiece : GradedRing.proj (grading I) n a ∈ grading I n :=
      (DirectSum.decompose (grading I) a n).property
    obtain ⟨P, hP, hPa⟩ := hpiece
    change Ideal.Quotient.mk I P = GradedRing.proj (grading I) n a at hPa
    refine ⟨polynomialOpen I hI P, ⟨n, P, hP, rfl⟩, ?_, ?_⟩
    · change x ∈ Proj.basicOpen (grading I) (Ideal.Quotient.mk I P)
      rw [hPa]
      exact hn
    · intro y hy
      apply haU
      change y ∈ Proj.basicOpen (grading I) a
      rw [Proj.basicOpen_eq_iSup_proj]
      apply TopologicalSpace.Opens.mem_iSup.mpr
      refine ⟨n, ?_⟩
      change y ∈ Proj.basicOpen (grading I) (Ideal.Quotient.mk I P) at hy
      rwa [hPa] at hy

end PhilipponMultiplicity.ProjectiveCoordinateScheme

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectivePointTopology

set_option autoImplicit false
set_option maxHeartbeats 150000
set_option synthInstance.maxHeartbeats 1000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ProjectivePointComparison

open MvPolynomial AlgebraicGeometry CategoryTheory Topology
open scoped Topology

universe u
variable {K : Type u} [Field K] (N : ℕ)
    (I : Ideal (projectiveSpace K N).CoordinateRing)
    (hI : IsMultihomogeneousIdeal (projectiveSpace K N) I)

theorem point_mem_homogeneousOpen (x : (projectiveSpace K N).zeroLocus I)
    (P : (projectiveSpace K N).CoordinateRing) (n : ℕ) (hP : P.IsHomogeneous n) :
    point N I hI x ∈
      ProjectiveCoordinateScheme.polynomialOpen I (ordinaryHomogeneous N I hI) P ↔
      (projectiveSpace K N).eval P x.val ≠ 0 := by
  by_cases hn : n = 0
  · subst n
    have hC : P = C (P.coeff 0) :=
      (homogeneousComponent_of_mem hP).symm.trans (homogeneousComponent_zero _)
    rw [hC, ProjectiveCoordinateScheme.mem_polynomialOpen_C]
    simp only [MultiProjectiveSpace.eval, eval_C]
  · exact point_mem_polynomialOpen N I hI x P n hP (Nat.pos_of_ne_zero hn)

theorem point_continuous :
    letI := (projectiveSpace K N).zariskiTopology
    Continuous (point N I hI) := by
  letI := (projectiveSpace K N).zariskiTopology
  apply (ProjectiveCoordinateScheme.homogeneous_polynomial_basis
    I (ordinaryHomogeneous N I hI)).continuous_iff.mpr
  rintro _ ⟨n, P, hP, rfl⟩
  have he : (point N I hI) ⁻¹'
      (ProjectiveCoordinateScheme.polynomialOpen I (ordinaryHomogeneous N I hI) P) =
      {x | (projectiveSpace K N).eval P x.val ≠ 0} :=
    Set.ext (fun x => point_mem_homogeneousOpen N I hI x P n hP)
  rw [he]
  exact ((projectiveSpace K N).isOpen_basic P (fun _ => n)
    ((MultiProjectiveSpace.projective_homogeneous_iff N P n).mpr hP)).preimage
      continuous_subtype_val

theorem point_isInducing :
    letI := (projectiveSpace K N).zariskiTopology
    IsInducing (point N I hI) := by
  letI := (projectiveSpace K N).zariskiTopology
  refine ⟨le_antisymm (point_continuous N I hI).le_induced ?_⟩
  change TopologicalSpace.induced (point N I hI) inferInstance ≤
    TopologicalSpace.induced Subtype.val (projectiveSpace K N).zariskiTopology
  apply continuous_iff_le_induced.mp
  letI := TopologicalSpace.induced (point N I hI) inferInstance
  apply continuous_generateFrom_iff.mpr
  rintro _ ⟨P, D, hP, rfl⟩
  have hD : D = fun _ => D (0 : Fin 1) :=
    funext (fun i => congrArg D (Subsingleton.elim (α := Fin 1) i (0 : Fin 1)))
  rw [hD] at hP
  have hp := (MultiProjectiveSpace.projective_homogeneous_iff N P (D (0 : Fin 1))).mp hP
  have he : Subtype.val ⁻¹' {x | (projectiveSpace K N).eval P x ≠ 0} =
      (point N I hI) ⁻¹'
        (ProjectiveCoordinateScheme.polynomialOpen I (ordinaryHomogeneous N I hI) P) :=
    Set.ext (fun x => (point_mem_homogeneousOpen N I hI x P _ hp).symm)
  rw [he]
  exact (ProjectiveCoordinateScheme.polynomialOpen I (ordinaryHomogeneous N I hI) P).isOpen.preimage
    continuous_induced_dom

def closedPointHomeomorph [IsAlgClosed K] :
    letI := (projectiveSpace K N).zariskiTopology
    (projectiveSpace K N).zeroLocus I ≃ₜ {z : scheme N I hI // IsClosed {z}} := by
  letI := (projectiveSpace K N).zariskiTopology
  apply (closedPointEquiv N I hI).toHomeomorphOfIsInducing
  apply IsInducing.subtypeVal.of_comp_iff.mp
  exact point_isInducing N I hI

end PhilipponMultiplicity.ProjectivePointComparison

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponAffinePrincipalGraph
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MvPolynomial Set Topology

namespace PhilipponMultiplicity.AffinePrincipalGraph
variable {K : Type*} [Field K] {σ : Type*}

theorem inverse_substitution_fraction (Q : MvPolynomial σ K)
    (P : MvPolynomial (Option σ) K) :
    ∃ A : MvPolynomial σ K, ∃ n : ℕ, ∀ v : σ → K, aeval v Q ≠ 0 →
      aeval (fun t => t.elim ((aeval v Q)⁻¹) v) P = aeval v A / (aeval v Q)^n := by
  induction P using MvPolynomial.induction_on with
  | C c => exact ⟨C c, 0, by simp⟩
  | add P R hP hR =>
    obtain ⟨A, n, hA⟩ := hP
    obtain ⟨B, m, hB⟩ := hR
    refine ⟨A * Q^m + B * Q^n, n + m, ?_⟩
    intro v hv
    simp only [map_add, map_mul, map_pow, hA v hv, hB v hv, pow_add]
    simpa only [mul_comm] using div_add_div (aeval v A) (aeval v B)
      (pow_ne_zero n hv) (pow_ne_zero m hv)
  | mul_X P i hP =>
    obtain ⟨A, n, hA⟩ := hP
    cases i with
    | none =>
      refine ⟨A, n + 1, ?_⟩
      intro v hv
      simp only [map_mul, aeval_X, Option.elim_none, hA v hv, pow_succ]
      rw [div_mul_eq_div_mul_one_div, one_div]
    | some i =>
      refine ⟨A * X i, n, ?_⟩
      intro v hv
      simp only [map_mul, aeval_X, Option.elim_some, hA v hv]
      exact div_mul_eq_mul_div _ _ _

def equations (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K) :
    Ideal (MvPolynomial (Option σ) K) :=
  Ideal.span (rename (Option.some : σ → Option σ) '' (I : Set (MvPolynomial σ K)) ∪
    {X none * rename (Option.some : σ → Option σ) Q - 1})

def ideal (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K) :
    Ideal (MvPolynomial (Option σ) K) := (equations I Q).radical

theorem ideal_isRadical (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K) :
    (ideal I Q).IsRadical := Ideal.radical_isRadical _

theorem mem_locus (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K)
    (v : Option σ → K) :
    v ∈ zeroLocus K (ideal I Q) ↔
      (fun t => v (some t)) ∈ zeroLocus K I ∧
        v none * aeval (fun t => v (some t)) Q = 1 := by
  constructor
  · intro hv
    constructor
    · intro P hP
      have h := hv _ (Ideal.le_radical (Ideal.subset_span
        (Set.mem_union_left _ ⟨P, hP, rfl⟩)))
      simpa only [aeval_rename, Function.comp_def] using h
    · have h := hv _ (Ideal.le_radical (Ideal.subset_span
        (Set.mem_union_right _ (Set.mem_singleton _))))
      simpa only [map_sub, map_mul, aeval_X, aeval_rename, Function.comp_def,
        map_one, sub_eq_zero] using h
  · rintro ⟨hI, hQ⟩
    have hker : equations I Q ≤ RingHom.ker (aeval v).toRingHom := by
      apply Ideal.span_le.mpr
      rintro P (⟨F, hF, rfl⟩ | rfl)
      · change aeval v (rename some F) = 0
        simpa only [aeval_rename, Function.comp_def] using hI F hF
      · change aeval v (X none * rename some Q - 1) = 0
        simpa only [map_sub, map_mul, aeval_X, aeval_rename, Function.comp_def,
          map_one, sub_eq_zero] using hQ
    intro P hP
    exact radical_le_vanishingIdeal_zeroLocus (K := K) (equations I Q) hP v
      (fun F hF => hker hF)

def domain (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K) :
    Set (zeroLocus K I) := {x | aeval x.val Q ≠ 0}

def graph (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K)
    (x : domain I Q) : zeroLocus K (ideal I Q) :=
  ⟨fun t => t.elim ((aeval x.val.val Q)⁻¹) x.val.val,
    (mem_locus I Q _).mpr ⟨x.val.property, inv_mul_cancel₀ x.property⟩⟩

theorem denominator_ne_zero (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K)
    (v : zeroLocus K (ideal I Q)) : aeval (fun t => v.val (some t)) Q ≠ 0 := by
  intro h
  have hh := ((mem_locus I Q v.val).mp v.property).2
  rw [h, mul_zero] at hh
  exact zero_ne_one hh

def project (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K)
    (v : zeroLocus K (ideal I Q)) : domain I Q :=
  ⟨⟨fun t => v.val (some t), ((mem_locus I Q v.val).mp v.property).1⟩,
    denominator_ne_zero I Q v⟩

theorem project_graph (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K)
    (x : domain I Q) : project I Q (graph I Q x) = x := rfl

theorem graph_project (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K)
    (v : zeroLocus K (ideal I Q)) : graph I Q (project I Q v) = v := by
  apply Subtype.ext
  funext t
  cases t with
  | some t => rfl
  | none =>
    change (aeval (fun t => v.val (some t)) Q)⁻¹ = v.val none
    symm
    rw [← one_div]
    exact (eq_div_iff (denominator_ne_zero I Q v)).mpr
      ((mem_locus I Q v.val).mp v.property).2

end PhilipponMultiplicity.AffinePrincipalGraph

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponPrincipalGraphScheme

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity.AffinePrincipalGraph

open MvPolynomial AlgebraicGeometry CategoryTheory AffineClosedPoints

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] {σ : Type} [Finite σ]
variable (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K)

def baseHom : (MvPolynomial σ K ⧸ I) →ₐ[K]
    (MvPolynomial (Option σ) K ⧸ ideal I Q) :=
  quotientMap I (ideal I Q) (ideal_isRadical I Q)
    (fun x => (project I Q x).val) (fun j => X (some j)) (by
      intro x j
      simp [project])

@[simp] theorem evaluation_baseHom (x : zeroLocus K (ideal I Q))
    (a : MvPolynomial σ K ⧸ I) :
    evaluation (ideal I Q) x (baseHom I Q a) = evaluation I (project I Q x).val a := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [baseHom, quotientMap_mk, evaluation_mk, evaluate_substitution, evaluation_mk]
  simp only [aeval_X, project]

theorem baseHom_Q_isUnit : IsUnit (baseHom I Q (Ideal.Quotient.mk I Q)) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨Ideal.Quotient.mk (ideal I Q) (X none), ?_⟩
  apply evaluation_ext (ideal I Q) (ideal_isRadical I Q)
  intro x
  simp only [map_mul, evaluation_baseHom, evaluation_mk, aeval_X, map_one]
  exact (mul_comm _ _).trans ((mem_locus I Q x.val).mp x.property).2

theorem exists_fraction (b : MvPolynomial (Option σ) K ⧸ ideal I Q) :
    ∃ n : ℕ, ∃ a : MvPolynomial σ K ⧸ I,
      b * baseHom I Q (Ideal.Quotient.mk I Q) ^ n = baseHom I Q a := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨A, n, hA⟩ := inverse_substitution_fraction Q P
  refine ⟨n, Ideal.Quotient.mk I A, ?_⟩
  apply evaluation_ext (ideal I Q) (ideal_isRadical I Q)
  intro x
  simp only [map_mul, map_pow, evaluation_baseHom, evaluation_mk]
  have h := hA (project I Q x).val.val (project I Q x).property
  have hx : (fun t => t.elim ((aeval (project I Q x).val.val Q)⁻¹)
      (project I Q x).val.val) = x.val :=
    congrArg Subtype.val (graph_project I Q x)
  rw [hx] at h
  exact (eq_div_iff (pow_ne_zero n (project I Q x).property)).mp h

theorem clear_baseHom_equality (hI : I.IsRadical)
    (a b : MvPolynomial σ K ⧸ I) (hab : baseHom I Q a = baseHom I Q b) :
    Ideal.Quotient.mk I Q * a = Ideal.Quotient.mk I Q * b := by
  apply evaluation_ext I hI
  intro x
  simp only [map_mul, evaluation_mk]
  by_cases hx : aeval x.val Q = 0
  · simp [hx]
  · have h := congrArg (evaluation (ideal I Q) (graph I Q ⟨x, hx⟩)) hab
    simp only [evaluation_baseHom, project_graph] at h
    rw [h]

theorem coordinateRing_isLocalization (hI : I.IsRadical) :
    letI : Algebra (MvPolynomial σ K ⧸ I)
        (MvPolynomial (Option σ) K ⧸ ideal I Q) := (baseHom I Q).toRingHom.toAlgebra
    IsLocalization.Away (Ideal.Quotient.mk I Q)
      (MvPolynomial (Option σ) K ⧸ ideal I Q) := by
  letI : Algebra (MvPolynomial σ K ⧸ I)
      (MvPolynomial (Option σ) K ⧸ ideal I Q) := (baseHom I Q).toRingHom.toAlgebra
  apply IsLocalization.Away.mk (Ideal.Quotient.mk I Q) (baseHom_Q_isUnit I Q)
  · exact exists_fraction I Q
  · intro a b hab
    exact ⟨1, by simpa only [pow_one] using clear_baseHom_equality I Q hI a b hab⟩

def schemeProjection : affineScheme (ideal I Q) ⟶ affineScheme I :=
  schemeMap I (ideal I Q) (baseHom I Q)

theorem schemeProjection_isOpenImmersion (hI : I.IsRadical) :
    IsOpenImmersion (schemeProjection I Q) := by
  letI : Algebra (MvPolynomial σ K ⧸ I)
      (MvPolynomial (Option σ) K ⧸ ideal I Q) := (baseHom I Q).toRingHom.toAlgebra
  letI := coordinateRing_isLocalization I Q hI
  exact IsOpenImmersion.of_isLocalization (Ideal.Quotient.mk I Q)

theorem schemeProjection_point (x : zeroLocus K (ideal I Q)) :
    schemeProjection I Q (point (ideal I Q) x).toPrimeSpectrum =
      (point I (project I Q x).val).toPrimeSpectrum := by
  rw [schemeProjection, schemeMap_point]
  congr 2
  apply Subtype.ext
  funext j
  simp only [pointMap_coordinate, evaluation_baseHom, evaluation_mk, aeval_X]

end PhilipponMultiplicity.AffinePrincipalGraph

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectivePrincipalCharts

set_option autoImplicit false
set_option maxHeartbeats 180000
set_option synthInstance.maxHeartbeats 1000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.AffineClosedPoints
open MvPolynomial
variable {K : Type*} [Field K] {σ : Type*}

def idealHomeomorph (I J : Ideal (MvPolynomial σ K)) (h : I = J) :
    @Homeomorph (zeroLocus K I) (zeroLocus K J) (locusTopology I) (locusTopology J) := by
  letI := locusTopology I
  letI := locusTopology J
  exact { toEquiv := Equiv.setCongr (congrArg (zeroLocus K) h)
          continuous_toFun := by subst J; exact continuous_id
          continuous_invFun := by subst J; exact continuous_id }

end PhilipponMultiplicity.AffineClosedPoints

namespace PhilipponMultiplicity.ProjectivePointComparison

open MvPolynomial AlgebraicGeometry CategoryTheory
open scoped Topology

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] (N : ℕ)
    (I : Ideal (projectiveSpace K N).CoordinateRing)
    (hI : IsMultihomogeneousIdeal (projectiveSpace K N) I)

def coordinatesHomeomorph (j : Fin (N + 1)) :
    letI := (projectiveSpace K N).zariskiTopology
    letI := AffineClosedPoints.locusTopology (ProjectiveCoordinateScheme.chartIdeal I ⟨(0 : Fin 1), j⟩)
    StandardAffineChart.locus (projectiveSpace K N) I (fun _ => j) ≃ₜ
      zeroLocus K (ProjectiveCoordinateScheme.chartIdeal I ⟨(0 : Fin 1), j⟩) := by
  letI := (projectiveSpace K N).zariskiTopology
  letI := AffineClosedPoints.locusTopology
    (StandardAffineChart.normalizedIdeal (projectiveSpace K N) I (fun _ => j))
  letI := AffineClosedPoints.locusTopology (ProjectiveCoordinateScheme.chartIdeal I ⟨(0 : Fin 1), j⟩)
  exact (StandardAffineChart.locusHomeomorph (projectiveSpace K N) I (fun _ => j) hI).trans
    (AffineClosedPoints.idealHomeomorph _ _ (ProjectiveCoordinateScheme.normalizedIdeal_single N I j))

def chartOriginalPoint (j : Fin (N + 1))
    (y : zeroLocus K (ProjectiveCoordinateScheme.chartIdeal I ⟨(0 : Fin 1), j⟩)) :
    (projectiveSpace K N).zeroLocus I :=
  ⟨((coordinates N I hI j).symm y).val.val, ((coordinates N I hI j).symm y).property⟩

theorem chartOriginalPoint_continuous (j : Fin (N + 1)) :
    letI := (projectiveSpace K N).zariskiTopology
    letI := AffineClosedPoints.locusTopology (ProjectiveCoordinateScheme.chartIdeal I ⟨(0 : Fin 1), j⟩)
    Continuous (chartOriginalPoint N I hI j) := by
  letI := (projectiveSpace K N).zariskiTopology
  letI := AffineClosedPoints.locusTopology (ProjectiveCoordinateScheme.chartIdeal I ⟨(0 : Fin 1), j⟩)
  apply Continuous.subtype_mk
  exact continuous_subtype_val.comp
    (continuous_subtype_val.comp (coordinatesHomeomorph N I hI j).symm.continuous)

def principalIdeal (j : Fin (N + 1)) (Q : (projectiveSpace K N).CoordinateRing) :
    Ideal (MvPolynomial (Option (projectiveSpace K N).Variable) K) :=
  AffinePrincipalGraph.ideal (ProjectiveCoordinateScheme.chartIdeal I ⟨(0 : Fin 1), j⟩) Q

def principalPoint (j : Fin (N + 1)) (Q : (projectiveSpace K N).CoordinateRing)
    (z : zeroLocus K (principalIdeal N I j Q)) : (projectiveSpace K N).zeroLocus I :=
  chartOriginalPoint N I hI j (AffinePrincipalGraph.project _ Q z).val

def principalImmersion (j : Fin (N + 1)) (Q : (projectiveSpace K N).CoordinateRing) :
    AffineClosedPoints.affineScheme (principalIdeal N I j Q) ⟶ scheme N I hI :=
  AffinePrincipalGraph.schemeProjection _ Q ≫
    ProjectiveCoordinateScheme.chartImmersion I (ordinaryHomogeneous N I hI) ⟨(0 : Fin 1), j⟩

theorem principalImmersion_isOpenImmersion (hred : I.IsRadical)
    (j : Fin (N + 1)) (Q : (projectiveSpace K N).CoordinateRing) :
    IsOpenImmersion (principalImmersion N I hI j Q) := by
  letI := AffinePrincipalGraph.schemeProjection_isOpenImmersion
    (ProjectiveCoordinateScheme.chartIdeal I ⟨(0 : Fin 1), j⟩) Q
    (ProjectiveCoordinateScheme.chartIdeal_isRadical I (ordinaryHomogeneous N I hI) hred _)
  letI := ProjectiveCoordinateScheme.chartImmersion_isOpenImmersion I (ordinaryHomogeneous N I hI)
    ⟨(0 : Fin 1), j⟩
  change IsOpenImmersion (_ ≫ _)
  infer_instance

theorem principalImmersion_over (j : Fin (N + 1)) (Q : (projectiveSpace K N).CoordinateRing) :
    principalImmersion N I hI j Q ≫
      ProjectiveCoordinateScheme.structureMap I (ordinaryHomogeneous N I hI) =
        AffineClosedPoints.structureMap (principalIdeal N I j Q) := by
  rw [principalImmersion, Category.assoc, ProjectiveCoordinateScheme.chartImmersion_over]
  exact AffineClosedPoints.schemeMap_over _ _ _

theorem principalImmersion_point (j : Fin (N + 1)) (Q : (projectiveSpace K N).CoordinateRing)
    (z : zeroLocus K (principalIdeal N I j Q)) :
    principalImmersion N I hI j Q (AffineClosedPoints.point _ z).toPrimeSpectrum =
      point N I hI (principalPoint N I hI j Q z) := by
  change ProjectiveCoordinateScheme.chartImmersion I _ _
    (AffinePrincipalGraph.schemeProjection _ Q (AffineClosedPoints.point _ z).toPrimeSpectrum) = _
  dsimp only [principalIdeal] at z ⊢
  rw [AffinePrincipalGraph.schemeProjection_point]
  unfold principalPoint chartOriginalPoint
  rw [point_eq_pointInChart, pointInChart, Equiv.apply_symm_apply]

def principalLift : (projectiveSpace K N).Variable →
    MvPolynomial (Option (projectiveSpace K N).Variable) K := fun v => X (some v)

theorem principalPoint_polynomial_lift (j : Fin (N + 1))
    (Q : (projectiveSpace K N).CoordinateRing)
    (z : zeroLocus K (principalIdeal N I j Q)) (i : (projectiveSpace K N).FactorIndex) :
    ∃ h : (fun k => aeval z.val (principalLift N ⟨i, k⟩)) ≠ 0,
      Projectivization.mk K
        (fun k => aeval z.val (principalLift N ⟨i, k⟩)) h =
          (principalPoint N I hI j Q z).val i := by
  let y := (AffinePrincipalGraph.project
    (ProjectiveCoordinateScheme.chartIdeal I ⟨(0 : Fin 1), j⟩) Q z).val
  let x := (coordinates N I hI j).symm y
  have hx : (StandardAffineChart.normalize (projectiveSpace K N) (fun _ => j) x.val).val =
      y.val := (coordinates_val N I hI j x).symm.trans
        (congrArg Subtype.val ((coordinates N I hI j).apply_symm_apply y))
  have hrep := StandardAffineChart.normalize_represents (projectiveSpace K N) (fun _ => j) x.val i
  rw [hx] at hrep
  simpa only [principalLift, aeval_X, principalPoint, chartOriginalPoint,
    x, y, AffinePrincipalGraph.project] using hrep

theorem exists_principal_chart_in_open
    (x : (projectiveSpace K N).zeroLocus I) (W : Set ((projectiveSpace K N).zeroLocus I))
    (hW : letI := (projectiveSpace K N).zariskiTopology; IsOpen W) (hxW : x ∈ W) :
    ∃ (j : Fin (N + 1)) (Q : (projectiveSpace K N).CoordinateRing)
      (z : zeroLocus K (principalIdeal N I j Q)),
      principalPoint N I hI j Q z = x ∧ ∀ w, principalPoint N I hI j Q w ∈ W := by
  letI := (projectiveSpace K N).zariskiTopology
  let j := pivot N I x
  let J := ProjectiveCoordinateScheme.chartIdeal I ⟨(0 : Fin 1), j⟩
  letI := AffineClosedPoints.locusTopology J
  let y := coordinates N I hI j (onChart N I x)
  have hy : chartOriginalPoint N I hI j y = x := by
    apply Subtype.ext
    change ((coordinates N I hI j).symm (coordinates N I hI j (onChart N I x))).val.val = x.val
    rw [Equiv.symm_apply_apply]
    rfl
  obtain ⟨_, ⟨Q, rfl⟩, hyQ, hQW⟩ := (AffineClosedPoints.nonzero_sets_basis J).exists_subset_of_mem_open
    (show y ∈ (chartOriginalPoint N I hI j) ⁻¹' W by rwa [Set.mem_preimage, hy])
    (hW.preimage (chartOriginalPoint_continuous N I hI j))
  refine ⟨j, Q, AffinePrincipalGraph.graph J Q ⟨y, hyQ⟩, ?_, ?_⟩
  · exact hy
  · intro w
    exact hQW (AffinePrincipalGraph.project J Q w).property

end PhilipponMultiplicity.ProjectivePointComparison

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponRegularNormalizedSchemeMaps

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 1500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity

open MvPolynomial AlgebraicGeometry CategoryTheory
open scoped Topology

universe u
variable {K : Type u} [Field K] {σ : Type} [Finite σ]

theorem continuous_of_polynomial_projective_lift
    (J : Ideal (MvPolynomial σ K)) (M : MultiProjectiveSpace K)
    (e : zeroLocus K J → M.Point) (L : M.Variable → MvPolynomial σ K)
    (hL : ∀ (z : zeroLocus K J) (b : M.FactorIndex),
      ∃ h : (fun i => aeval z.val (L ⟨b, i⟩)) ≠ 0,
      Projectivization.mk K (fun i => aeval z.val (L ⟨b, i⟩)) h = e z b) :
    @Continuous _ _ (AffineClosedPoints.locusTopology J) M.zariskiTopology e := by
  letI := AffineClosedPoints.locusTopology J
  apply continuous_generateFrom_iff.mpr
  rintro _ ⟨P, D, hP, rfl⟩
  have he : e ⁻¹' {x | M.eval P x ≠ 0} =
      {z | aeval z.val ((aeval L) P) ≠ 0} := by
    ext z
    have hv := (M.eval_eq_zero_iff_of_lift (e z) (fun v => aeval z.val (L v)) (hL z) P D hP).not
    change M.eval P (e z) ≠ 0 ↔ aeval z.val (aeval L P) ≠ 0
    rw [AffineClosedPoints.evaluate_substitution, aeval_eq_eval]
    exact hv.symm
  rw [he]
  exact (AffineClosedPoints.nonzero_sets_basis J).isOpen (Set.mem_range_self ((aeval L) P))

namespace StandardAffineChart

variable (N : MultiProjectiveSpace K) (I : Ideal N.CoordinateRing)
    (hI : IsMultihomogeneousIdeal N I)
    (b : ∀ i : N.FactorIndex, Fin (N.ambientDimension i + 1))

def normalizeMap {A : Type*} (f : A → N.zeroLocus I)
    (hb : ∀ z, (f z).val ∈ domain N b) :
    A → zeroLocus K (normalizedIdeal N I b) :=
  fun z => normalizeLocus N I b hI ⟨⟨(f z).val, hb z⟩, (f z).property⟩

@[simp] theorem normalizeMap_coordinate {A : Type*} (f : A → N.zeroLocus I)
    (hb : ∀ z, (f z).val ∈ domain N b) (z : A) (v : N.Variable) :
    (normalizeMap N I hI b f hb z).val v =
      N.eval (X v) (f z).val / N.eval (X ⟨v.1, b v.1⟩) (f z).val := by
  simp only [normalizeMap, normalizeLocus, normalize, MultiProjectiveSpace.eval,
    eval_X, MultiProjectiveSpace.coordinate]

end StandardAffineChart

theorem regular_normalized_map_isLocallyRational
    (J : Ideal (MvPolynomial σ K)) (M N : MultiProjectiveSpace K)
    (I : Ideal N.CoordinateRing) (hI : IsMultihomogeneousIdeal N I)
    (e : zeroLocus K J → M.Point) (L : M.Variable → MvPolynomial σ K)
    (hL : ∀ (z : zeroLocus K J) (b : M.FactorIndex),
      ∃ h : (fun i => aeval z.val (L ⟨b, i⟩)) ≠ 0,
      Projectivization.mk K (fun i => aeval z.val (L ⟨b, i⟩)) h = e z b)
    (f : zeroLocus K J → N.zeroLocus I)
    (hf : M.IsRegularAlong N e (fun z => (f z).val))
    (b : ∀ i : N.FactorIndex, Fin (N.ambientDimension i + 1))
    (hb : ∀ z, (f z).val ∈ StandardAffineChart.domain N b) :
    AffineClosedPoints.IsLocallyRationalMap (StandardAffineChart.normalizedIdeal N I b) J
      (StandardAffineChart.normalizeMap N I hI b f hb) := by
  letI := AffineClosedPoints.locusTopology J
  have he := continuous_of_polynomial_projective_lift J M e L hL
  intro z v
  let t : zeroLocus K J → (Set.univ : Set (zeroLocus K J)) := fun w => ⟨w, Set.mem_univ _⟩
  letI : TopologicalSpace (Set.univ : Set (zeroLocus K J)) :=
    TopologicalSpace.induced Subtype.val (TopologicalSpace.induced e M.zariskiTopology)
  have ht : Continuous t := by
    apply continuous_induced_rng.mpr
    exact continuous_induced_rng.mpr he
  obtain ⟨U, hU, hzU, A, B, hAB⟩ := hf.local_fraction_of_target_ratio Set.univ
    (fun w => w.val.val) L (fun w => hL w.val)
    (X v) (X ⟨v.1, b v.1⟩) _ (N.isHomogeneous_X v) (N.isHomogeneous_X ⟨v.1, b v.1⟩)
    (fun w => by simpa only [MultiProjectiveSpace.eval, eval_X,
      MultiProjectiveSpace.coordinate] using hb w.val v.1) (t z)
  refine ⟨t ⁻¹' U, hU.preimage ht, hzU, A, B, ?_⟩
  intro w hw
  exact ⟨(hAB (t w) hw).1, (StandardAffineChart.normalizeMap_coordinate N I hI b f hb w v).trans
    (hAB (t w) hw).2⟩

end PhilipponMultiplicity

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponClosedPointSchemeGluing

set_option autoImplicit false
set_option maxHeartbeats 150000
set_option synthInstance.maxHeartbeats 1000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Topology

universe u v
variable {K : Type u} [Field K] [IsAlgClosed K]
    {X Y : Scheme.{u}} (πX : X ⟶ Spec (.of K)) (πY : Y ⟶ Spec (.of K))
    [IsReduced X] [LocallyOfFiniteType πX] [LocallyOfFiniteType πY] [IsSeparated πY]

theorem scheme_maps_agree_on_overlaps
    (U : X.OpenCover.{v}) (F : ∀ i, U.X i ⟶ Y)
    (hbase : ∀ i, F i ≫ πY = U.f i ≫ πX)
    (hpoints : ∀ i j (x : U.X i) (y : U.X j), IsClosed {U.f i x} →
      U.f i x = U.f j y → F i x = F j y) :
    ∀ i j, pullback.fst (U.f i) (U.f j) ≫ F i =
      pullback.snd (U.f i) (U.f j) ≫ F j := by
  intro i j
  let p := pullback.fst (U.f i) (U.f j) ≫ U.f i
  letI : IsOpenImmersion p := inferInstance
  letI := isReduced_of_isOpenImmersion p
  letI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace πX
  have hb : (pullback.fst (U.f i) (U.f j) ≫ F i) ≫ πY = p ≫ πX := by
    simp only [Category.assoc, hbase, p]
  letI : LocallyOfFiniteType ((pullback.fst (U.f i) (U.f j) ≫ F i) ≫ πY) := by
    rw [hb]
    infer_instance
  apply AlgebraicGeometry.ext_of_apply_eq πY Set.univ isOpen_univ.isLocallyClosed dense_univ
  · intro z _ hz
    have hzc : IsClosed {p z} := by
      change z ∈ p ⁻¹' closedPoints X
      rw [p.isOpenEmbedding.preimage_closedPoints]
      exact hz
    exact hpoints i j (pullback.fst (U.f i) (U.f j) z)
      (pullback.snd (U.f i) (U.f j) z) hzc
      (congrArg (fun g : pullback (U.f i) (U.f j) ⟶ X => g z) pullback.condition)
  · simp only [Category.assoc, hbase]
    simpa only [Category.assoc] using
      congrArg (fun g : pullback (U.f i) (U.f j) ⟶ X => g ≫ πX) pullback.condition

theorem existsUnique_schemeMap_of_closedPoint_agreement
    (U : X.OpenCover.{v}) (F : ∀ i, U.X i ⟶ Y)
    (hbase : ∀ i, F i ≫ πY = U.f i ≫ πX)
    (hpoints : ∀ i j (x : U.X i) (y : U.X j), IsClosed {U.f i x} →
      U.f i x = U.f j y → F i x = F j y) :
    ∃! f : X ⟶ Y, f ≫ πY = πX ∧ ∀ i, U.f i ≫ f = F i := by
  let hcompat := scheme_maps_agree_on_overlaps πX πY U F hbase hpoints
  let f := U.glueMorphisms F hcompat
  have hf : ∀ i, U.f i ≫ f = F i := U.ι_glueMorphisms F hcompat
  refine ⟨f, ⟨?_, hf⟩, ?_⟩
  · apply U.hom_ext
    intro i
    rw [← Category.assoc, hf, hbase]
  · intro g hg
    apply U.hom_ext
    intro i
    rw [hg.2, hf]

end PhilipponMultiplicity

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponSchemeClosedPointCover

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity

open AlgebraicGeometry CategoryTheory MvPolynomial

universe u v

namespace AffineClosedPoints
variable {K : Type u} [Field K] [IsAlgClosed K] {σ : Type} [Finite σ]

theorem closed_point_surjective (I : Ideal (MvPolynomial σ K))
    (z : affineScheme I) (hz : IsClosed {z}) :
    ∃ x : zeroLocus K I, (point I x).toPrimeSpectrum = z := by
  have hm := (PrimeSpectrum.isClosed_singleton_iff_isMaximal z).mp hz
  obtain ⟨x, hx⟩ := point_surjective I ⟨z.asIdeal, hm⟩
  exact ⟨x, PrimeSpectrum.ext (congrArg MaximalSpectrum.asIdeal hx)⟩

end AffineClosedPoints

theorem covers_of_covers_closed_points (X : Scheme.{u}) [JacobsonSpace X]
    {ι : Type v} (U : ι → Scheme.{u}) (f : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (h : ∀ x : X, IsClosed {x} → ∃ i y, f i y = x) :
    ∀ x : X, ∃ i y, f i y = x := by
  let V : Set X := ⋃ i, Set.range (f i)
  have hV : IsOpen V := isOpen_iUnion (fun i => (f i).isOpenEmbedding.isOpen_range)
  have htop : V = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_contra hx
    obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints
      (show Vᶜ.Nonempty from ⟨x, hx⟩) hV.isClosed_compl.isLocallyClosed
    obtain ⟨i, y, rfl⟩ := h z hzc
    exact hz (Set.mem_iUnion.mpr ⟨i, Set.mem_range_self y⟩)
  intro x
  have hx : x ∈ V := by rw [htop]; trivial
  exact Set.mem_iUnion.mp hx

def openCoverOfClosedPoints (X : Scheme.{u}) [JacobsonSpace X]
    {ι : Type v} (U : ι → Scheme.{u}) (f : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (h : ∀ x : X, IsClosed {x} → ∃ i y, f i y = x) : X.OpenCover.{v} where
  I₀ := ι
  X := U
  f := f
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨covers_of_covers_closed_points X U f h, fun i => inferInstance⟩

end PhilipponMultiplicity

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectiveRegularSchemeMap

set_option autoImplicit false
set_option maxHeartbeats 220000
set_option synthInstance.maxHeartbeats 1500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ProjectivePointComparison

open MvPolynomial AlgebraicGeometry CategoryTheory

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]

theorem affine_source_to_projective_chart {σ : Type} [Finite σ]
    (J : Ideal (MvPolynomial σ K)) (hJ : J.IsRadical) (M : MultiProjectiveSpace K)
    (N : ℕ) (I : Ideal (projectiveSpace K N).CoordinateRing)
    (hI : IsMultihomogeneousIdeal (projectiveSpace K N) I)
    (e : zeroLocus K J → M.Point) (L : M.Variable → MvPolynomial σ K)
    (hL : ∀ (z : zeroLocus K J) (b : M.FactorIndex),
      ∃ h : (fun i => aeval z.val (L ⟨b, i⟩)) ≠ 0,
      Projectivization.mk K (fun i => aeval z.val (L ⟨b, i⟩)) h = e z b)
    (f : zeroLocus K J → (projectiveSpace K N).zeroLocus I)
    (hf : M.IsRegularAlong (projectiveSpace K N) e (fun z => (f z).val))
    (k : Fin (N + 1))
    (hb : ∀ z, (f z).val ∈ StandardAffineChart.domain (projectiveSpace K N) (fun _ => k)) :
    ∃ F : AffineClosedPoints.affineScheme J ⟶ scheme N I hI,
      F ≫ ProjectiveCoordinateScheme.structureMap I (ordinaryHomogeneous N I hI) =
        AffineClosedPoints.structureMap J ∧
      ∀ z, F (AffineClosedPoints.point J z).toPrimeSpectrum = point N I hI (f z) := by
  let T := ProjectiveCoordinateScheme.chartIdeal I ⟨(0 : Fin 1), k⟩
  let g : zeroLocus K J → zeroLocus K T := fun z =>
    coordinates N I hI k ⟨⟨(f z).val, hb z⟩, (f z).property⟩
  have hrat : AffineClosedPoints.IsLocallyRationalMap T J g := by
    letI := AffineClosedPoints.locusTopology J
    have h := regular_normalized_map_isLocallyRational J M (projectiveSpace K N) I hI
      e L hL f hf (fun _ => k) hb
    intro z v
    obtain ⟨U, hU, hzU, A, B, hAB⟩ := h z v
    exact ⟨U, hU, hzU, A, B, hAB⟩
  obtain ⟨F, hF, _⟩ := AffineClosedPoints.existsUnique_schemeRealization T J hJ g hrat
  refine ⟨F ≫ ProjectiveCoordinateScheme.chartImmersion I (ordinaryHomogeneous N I hI)
    ⟨(0 : Fin 1), k⟩, ?_, ?_⟩
  · rw [Category.assoc, ProjectiveCoordinateScheme.chartImmersion_over]
    exact hF.1
  · intro z
    change ProjectiveCoordinateScheme.chartImmersion I _ _
      (F (AffineClosedPoints.point J z).toPrimeSpectrum) = _
    rw [hF.2]
    exact (point_eq_pointInChart N I hI k ⟨⟨(f z).val, hb z⟩, (f z).property⟩).symm

theorem regular_map_local_schemeMap
    (M N : ℕ) (I : Ideal (projectiveSpace K M).CoordinateRing)
    (hI : IsMultihomogeneousIdeal (projectiveSpace K M) I)
    (J : Ideal (projectiveSpace K N).CoordinateRing)
    (hJ : IsMultihomogeneousIdeal (projectiveSpace K N) J)
    (f : (projectiveSpace K M).zeroLocus I → (projectiveSpace K N).zeroLocus J)
    (hf : (projectiveSpace K M).IsRegularAlong (projectiveSpace K N)
      Subtype.val (fun z => (f z).val)) (x : (projectiveSpace K M).zeroLocus I) :
    ∃ (j : Fin (M + 1)) (Q : (projectiveSpace K M).CoordinateRing)
      (z : zeroLocus K (principalIdeal M I j Q))
      (F : AffineClosedPoints.affineScheme (principalIdeal M I j Q) ⟶ scheme N J hJ),
      principalPoint M I hI j Q z = x ∧
      F ≫ ProjectiveCoordinateScheme.structureMap J (ordinaryHomogeneous N J hJ) =
        AffineClosedPoints.structureMap (principalIdeal M I j Q) ∧
      ∀ w, F (AffineClosedPoints.point _ w).toPrimeSpectrum =
        point N J hJ (f (principalPoint M I hI j Q w)) := by
  letI := (projectiveSpace K M).zariskiTopology
  letI := (projectiveSpace K N).zariskiTopology
  have hfc : Continuous f := continuous_induced_rng.mpr hf.continuous
  let k := pivot N J (f x)
  let W := {y : (projectiveSpace K M).zeroLocus I |
    (f y).val ∈ StandardAffineChart.domain (projectiveSpace K N) (fun _ => k)}
  have hW : IsOpen W := (StandardAffineChart.domain_isOpen (projectiveSpace K N) (fun _ => k)).preimage
    (continuous_subtype_val.comp hfc)
  have hxW : x ∈ W := (onChart N J (f x)).val.property
  obtain ⟨j, Q, z, hz, hall⟩ := exists_principal_chart_in_open M I hI x W hW hxW
  obtain ⟨F, hF, hFp⟩ := affine_source_to_projective_chart (principalIdeal M I j Q)
    (AffinePrincipalGraph.ideal_isRadical _ Q) (projectiveSpace K M) N J hJ
    (fun w => (principalPoint M I hI j Q w).val) (principalLift M)
    (principalPoint_polynomial_lift M I hI j Q)
    (fun w => f (principalPoint M I hI j Q w))
    (hf.comp_domain (principalPoint M I hI j Q)) k hall
  exact ⟨j, Q, z, F, hz, hF, hFp⟩

end PhilipponMultiplicity.ProjectivePointComparison

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectiveRegularGluing

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option synthInstance.maxHeartbeats 1500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ProjectivePointComparison

open MvPolynomial AlgebraicGeometry CategoryTheory
open scoped Topology

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]

theorem existsUnique_regular_schemeMap
    (M N : ℕ) (I : Ideal (projectiveSpace K M).CoordinateRing)
    (hI : IsMultihomogeneousIdeal (projectiveSpace K M) I) (hred : I.IsRadical)
    (J : Ideal (projectiveSpace K N).CoordinateRing)
    (hJ : IsMultihomogeneousIdeal (projectiveSpace K N) J)
    (f : (projectiveSpace K M).zeroLocus I → (projectiveSpace K N).zeroLocus J)
    (hf : (projectiveSpace K M).IsRegularAlong (projectiveSpace K N)
      Subtype.val (fun z => (f z).val)) :
    ∃! F : scheme M I hI ⟶ scheme N J hJ,
      F ≫ ProjectiveCoordinateScheme.structureMap J (ordinaryHomogeneous N J hJ) =
        ProjectiveCoordinateScheme.structureMap I (ordinaryHomogeneous M I hI) ∧
      ∀ x, F (point M I hI x) = point N J hJ (f x) := by
  classical
  let πX := ProjectiveCoordinateScheme.structureMap I (ordinaryHomogeneous M I hI)
  let πY := ProjectiveCoordinateScheme.structureMap J (ordinaryHomogeneous N J hJ)
  letI : IsProper πX := ProjectiveCoordinateScheme.structureMap_isProper I _
  letI : IsProper πY := ProjectiveCoordinateScheme.structureMap_isProper J _
  letI : IsReduced (scheme M I hI) :=
    ProjectiveCoordinateScheme.scheme_isReduced I (ordinaryHomogeneous M I hI) hred
  letI : JacobsonSpace (scheme M I hI) := LocallyOfFiniteType.jacobsonSpace πX
  choose j Q z F hz hF hFp using regular_map_local_schemeMap M N I hI J hJ f hf
  let A (x : (projectiveSpace K M).zeroLocus I) :=
    AffineClosedPoints.affineScheme (principalIdeal M I (j x) (Q x))
  let inc (x : (projectiveSpace K M).zeroLocus I) : A x ⟶ scheme M I hI :=
    principalImmersion M I hI (j x) (Q x)
  letI (x : (projectiveSpace K M).zeroLocus I) : IsOpenImmersion (inc x) :=
    principalImmersion_isOpenImmersion M I hI hred (j x) (Q x)
  have hcover : ∀ a : scheme M I hI, IsClosed {a} → ∃ i y, inc i y = a := by
    intro a ha
    obtain ⟨x, rfl⟩ := closed_points_surjective M I hI a ha
    refine ⟨x, (AffineClosedPoints.point _ (z x)).toPrimeSpectrum, ?_⟩
    change principalImmersion M I hI (j x) (Q x) _ = _
    rw [principalImmersion_point, hz]
  let U := openCoverOfClosedPoints (scheme M I hI) A inc hcover
  have hbase : ∀ i, F i ≫ πY = U.f i ≫ πX := by
    intro i
    exact (hF i).trans (principalImmersion_over M I hI (j i) (Q i)).symm
  have hagree : ∀ i k (a : U.X i) (b : U.X k), IsClosed {U.f i a} →
      U.f i a = U.f k b → F i a = F k b := by
    intro i k a b ha hab
    have hac : IsClosed {a} :=
      (preimage_closedPoints_subset (U.f i).isOpenEmbedding.injective (U.f i).continuous) ha
    have hb : IsClosed {U.f k b} := hab ▸ ha
    have hbc : IsClosed {b} :=
      (preimage_closedPoints_subset (U.f k).isOpenEmbedding.injective (U.f k).continuous) hb
    obtain ⟨a', rfl⟩ := AffineClosedPoints.closed_point_surjective _ a hac
    obtain ⟨b', rfl⟩ := AffineClosedPoints.closed_point_surjective _ b hbc
    rw [hFp i a', hFp k b']
    apply congrArg (fun x => point N J hJ (f x))
    apply point_injective M I hI
    change principalImmersion M I hI (j i) (Q i) _ =
      principalImmersion M I hI (j k) (Q k) _ at hab
    rwa [principalImmersion_point, principalImmersion_point] at hab
  obtain ⟨φ, ⟨hφbase, hφrestr⟩, _⟩ :=
    existsUnique_schemeMap_of_closedPoint_agreement πX πY U F hbase hagree
  have hφpoints : ∀ x, φ (point M I hI x) = point N J hJ (f x) := by
    intro x
    have he := congrArg (fun g : A x ⟶ scheme N J hJ =>
      g (AffineClosedPoints.point _ (z x)).toPrimeSpectrum) (hφrestr x)
    change φ (principalImmersion M I hI (j x) (Q x)
      (AffineClosedPoints.point _ (z x)).toPrimeSpectrum) = _ at he
    rwa [principalImmersion_point, hFp, hz] at he
  refine ⟨φ, ⟨hφbase, hφpoints⟩, ?_⟩
  intro ψ hψ
  letI : LocallyOfFiniteType (ψ ≫ πY) := by
    rw [hψ.1]
    exact inferInstanceAs (LocallyOfFiniteType πX)
  apply AlgebraicGeometry.ext_of_apply_eq πY Set.univ isOpen_univ.isLocallyClosed dense_univ
  · intro a _ ha
    obtain ⟨x, rfl⟩ := closed_points_surjective M I hI a ha
    exact (hψ.2 x).trans (hφpoints x).symm
  · exact hψ.1.trans hφbase.symm

end PhilipponMultiplicity.ProjectivePointComparison

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectiveSchemeAction

set_option autoImplicit false
set_option maxHeartbeats 150000
set_option synthInstance.maxHeartbeats 1500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ProjectivePointComparison

open MvPolynomial AlgebraicGeometry CategoryTheory

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]

theorem exists_scheme_action
    (N : ℕ) (I : Ideal (projectiveSpace K N).CoordinateRing)
    (hI : IsMultihomogeneousIdeal (projectiveSpace K N) I) (hred : I.IsRadical)
    (B : Type u) [AddGroup B]
    (τ : B → ((projectiveSpace K N).zeroLocus I ≃ (projectiveSpace K N).zeroLocus I))
    (hzero : τ 0 = Equiv.refl _)
    (hadd : ∀ g h, τ (g + h) = (τ h).trans (τ g))
    (hregular : ∀ g, (projectiveSpace K N).IsRegularAlong (projectiveSpace K N)
      Subtype.val (fun x => (τ g x).val)) :
    ∃ T : B → (scheme N I hI ≅ scheme N I hI),
      (∀ g, (T g).hom ≫ ProjectiveCoordinateScheme.structureMap I (ordinaryHomogeneous N I hI) =
        ProjectiveCoordinateScheme.structureMap I (ordinaryHomogeneous N I hI)) ∧
      (∀ g x, (T g).hom (point N I hI x) = point N I hI (τ g x)) ∧
      T 0 = Iso.refl _ ∧ ∀ g h, T (g + h) = T h ≪≫ T g := by
  classical
  choose A hA huniq using fun g =>
    existsUnique_regular_schemeMap N N I hI hred I hI (τ g) (hregular g)
  have hA0 : A 0 = 𝟙 (scheme N I hI) := by
    symm
    apply huniq 0
    refine ⟨Category.id_comp _, fun x => ?_⟩
    rw [hzero]
    rfl
  have hcomp : ∀ g h, A h ≫ A g = A (g + h) := by
    intro g h
    apply huniq (g + h)
    refine ⟨?_, fun x => ?_⟩
    · rw [Category.assoc, (hA g).1, (hA h).1]
    · change A g (A h (point N I hI x)) = _
      rw [(hA h).2, (hA g).2]
      exact congrArg (point N I hI) (congrArg (fun e => e x) (hadd g h)).symm
  let T (g : B) : scheme N I hI ≅ scheme N I hI :=
    { hom := A g
      inv := A (-g)
      hom_inv_id := by rw [hcomp, neg_add_cancel, hA0]
      inv_hom_id := by rw [hcomp, add_neg_cancel, hA0] }
  refine ⟨T, fun g => (hA g).1, fun g => (hA g).2, ?_, ?_⟩
  · apply Iso.ext
    exact hA0
  · intro g h
    apply Iso.ext
    exact (hcomp g h).symm

end PhilipponMultiplicity.ProjectivePointComparison

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponMultiprojectiveSchemeAction

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option synthInstance.maxHeartbeats 1500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.Hilbert.SegreVeronese
open MvPolynomial AlgebraicGeometry CategoryTheory
universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
    (M : MultiProjectiveSpace K) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (degreePiece K M.factorCount M.ambientDimension (fun _ => 1)))
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)

def schemePoint (x : M.zeroLocus I) : scheme M (fun _ => 1) b I hI (fun _ => le_rfl) :=
  ProjectivePointComparison.point N (diagonalIdeal M (fun _ => 1) b I)
    (diagonalIdeal_homogeneous M (fun _ => 1) b (fun _ => le_rfl) I hI)
    (locusEquiv M b I hI x)

def closedPointHomeomorph :
    letI := M.zariskiTopology
    M.zeroLocus I ≃ₜ {x : scheme M (fun _ => 1) b I hI (fun _ => le_rfl) | IsClosed {x}} := by
  letI := M.zariskiTopology
  letI := (projectiveSpace K N).zariskiTopology
  exact (locusHomeomorph M b I hI).trans
    (ProjectivePointComparison.closedPointHomeomorph N _
      (diagonalIdeal_homogeneous M (fun _ => 1) b (fun _ => le_rfl) I hI))

theorem exists_multiprojective_scheme_action (hred : I.IsRadical)
    (B : Type u) [AddGroup B] (τ : B → (M.zeroLocus I ≃ M.zeroLocus I))
    (hzero : τ 0 = Equiv.refl _)
    (hadd : ∀ g h, τ (g + h) = (τ h).trans (τ g))
    (hregular : ∀ g, M.IsRegularAlong M Subtype.val (fun x => (τ g x).val)) :
    ∃ T : B → (scheme M (fun _ => 1) b I hI (fun _ => le_rfl) ≅
        scheme M (fun _ => 1) b I hI (fun _ => le_rfl)),
      (∀ g, (T g).hom ≫ structureMap M (fun _ => 1) b I hI (fun _ => le_rfl) =
        structureMap M (fun _ => 1) b I hI (fun _ => le_rfl)) ∧
      (∀ g x, (T g).hom (schemePoint M b I hI x) = schemePoint M b I hI (τ g x)) ∧
      T 0 = Iso.refl _ ∧ ∀ g h, T (g + h) = T h ≪≫ T g := by
  classical
  let e := locusEquiv M b I hI
  let τ' (g : B) := (e.symm.trans (τ g)).trans e
  have hzero' : τ' 0 = Equiv.refl _ := by
    ext x
    simp [τ', hzero]
  have hadd' (g h : B) : τ' (g + h) = (τ' h).trans (τ' g) := by
    ext x
    simp [τ', hadd]
  have hregular' (g : B) : (projectiveSpace K N).IsRegularAlong (projectiveSpace K N)
      Subtype.val (fun x => (τ' g x).val) := by
    have h₁ := locusEquiv_inverse_regular M b I hI
    have h₂ := (hregular g).comp_domain e.symm
    have h₃ := (locusEquiv_regular M b I hI).comp_domain (fun x => τ g (e.symm x))
    exact h₁.comp (h₂.comp h₃)
  obtain ⟨T, hT, hpoint, hTzero, hTadd⟩ :=
    ProjectivePointComparison.exists_scheme_action N (diagonalIdeal M (fun _ => 1) b I)
      (diagonalIdeal_homogeneous M (fun _ => 1) b (fun _ => le_rfl) I hI)
      (hred.comap (substitution M (fun _ => 1) b).toRingHom)
      B τ' hzero' hadd' hregular'
  refine ⟨T, hT, ?_, hTzero, hTadd⟩
  intro g x
  have h := hpoint g (e x)
  simp only [τ', Equiv.trans_apply, Equiv.symm_apply_apply] at h
  exact h

end PhilipponMultiplicity.Hilbert.SegreVeronese

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponGroupClosureScheme

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ClosureScheme
open MvPolynomial AlgebraicGeometry CategoryTheory
open Hilbert.SegreVeronese
universe u
variable {K : Type u} [Field K] (G : EmbeddedGroupProduct K)

def ideal : Ideal G.ambient.CoordinateRing := G.ambient.vanishingIdeal (Set.range G.embedding)

theorem ideal_homogeneous : IsMultihomogeneousIdeal G.ambient (ideal G) :=
  vanishingIdeal_multihomogeneous K G.ambient (Set.range G.embedding)

theorem ideal_radical : (ideal G).IsRadical :=
  G.ambient.vanishingIdeal_isRadical (Set.range G.embedding)

theorem zeroLocus_eq : G.ambient.zeroLocus (ideal G) = groupProjectiveClosure G :=
  G.ambient.zeroLocus_vanishingIdeal_eq_closure (Set.range G.embedding)

def locusEquiv : groupProjectiveClosure G ≃ G.ambient.zeroLocus (ideal G) :=
  Equiv.setCongr (zeroLocus_eq G).symm

def locusHomeomorph : letI := G.ambient.zariskiTopology
    groupProjectiveClosure G ≃ₜ G.ambient.zeroLocus (ideal G) := by
  letI := G.ambient.zariskiTopology
  exact Homeomorph.setCongr (zeroLocus_eq G).symm

variable {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension (fun _ => 1)))

def scheme : Scheme.{u} :=
  Hilbert.SegreVeronese.scheme G.ambient (fun _ => 1) b (ideal G)
    (ideal_homogeneous G) (fun _ => le_rfl)

def structureMap : scheme G b ⟶ Spec (.of K) :=
  Hilbert.SegreVeronese.structureMap G.ambient (fun _ => 1) b (ideal G)
    (ideal_homogeneous G) (fun _ => le_rfl)

theorem isProper : IsProper (structureMap G b) :=
  structureMap_isProper G.ambient (fun _ => 1) b _ _ _

def point (x : groupProjectiveClosure G) : scheme G b :=
  schemePoint G.ambient b (ideal G) (ideal_homogeneous G) (locusEquiv G x)

variable [IsAlgClosed K]

def closedPointHomeomorph : letI := G.ambient.zariskiTopology
    groupProjectiveClosure G ≃ₜ {x : scheme G b | IsClosed {x}} := by
  letI := G.ambient.zariskiTopology
  exact (locusHomeomorph G).trans
    (Hilbert.SegreVeronese.closedPointHomeomorph G.ambient b (ideal G) (ideal_homogeneous G))

theorem exists_action
    (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
    (hzero : τ 0 = Equiv.refl _)
    (hadd : ∀ g h, τ (g + h) = (τ h).trans (τ g))
    (hregular : ∀ g, G.ambient.IsRegularAlong G.ambient
      Subtype.val (fun x => (τ g x).val)) :
    ∃ T : G.Point → (scheme G b ≅ scheme G b),
      (∀ g, (T g).hom ≫ structureMap G b = structureMap G b) ∧
      (∀ g x, (T g).hom (point G b x) = point G b (τ g x)) ∧
      T 0 = Iso.refl _ ∧ ∀ g h, T (g + h) = T h ≪≫ T g := by
  classical
  let e := locusEquiv G
  let τ' (g : G.Point) := (e.symm.trans (τ g)).trans e
  have hzero' : τ' 0 = Equiv.refl _ := by
    ext x
    simp [τ', hzero]
  have hadd' (g h : G.Point) : τ' (g + h) = (τ' h).trans (τ' g) := by
    ext x
    simp [τ', hadd]
  have hregular' (g : G.Point) : G.ambient.IsRegularAlong G.ambient
      Subtype.val (fun x => (τ' g x).val) :=
    (hregular g).comp_domain e.symm
  obtain ⟨T, hT, hpoint, hTzero, hTadd⟩ := exists_multiprojective_scheme_action
    G.ambient b (ideal G) (ideal_homogeneous G) (ideal_radical G)
    G.Point τ' hzero' hadd' hregular'
  refine ⟨T, hT, ?_, hTzero, hTadd⟩
  intro g x
  have h := hpoint g (e x)
  simp only [τ', Equiv.trans_apply, Equiv.symm_apply_apply] at h
  exact h

end PhilipponMultiplicity.ClosureScheme

namespace PhilipponMultiplicity
open AlgebraicGeometry CategoryTheory
universe u

end PhilipponMultiplicity

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponClosureClosedSubschemes

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 1500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity
open AlgebraicGeometry CategoryTheory Topology

theorem reduced_subscheme_of_closed_set {X : Scheme} (Z : TopologicalSpace.Closeds X) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have hred (U : X.affineOpens) :
      IsReduced (I.subschemeCover.openCover.X U) := by
    have hrad : (I.ideal U).IsRadical := by
      change (PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' (Z : Set X))).IsRadical
      exact PrimeSpectrum.isRadical_vanishingIdeal _
    letI : _root_.IsReduced (Γ(X, U) ⧸ I.ideal U) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp hrad
    change IsReduced (Spec (.of (Γ(X, U) ⧸ I.ideal U)))
    infer_instance
  letI := hred
  exact IsReduced.of_openCover _ I.subschemeCover.openCover

namespace ClosureScheme
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] (G : EmbeddedGroupProduct K) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension (fun _ => 1)))

theorem point_isInducing : letI := G.ambient.zariskiTopology
    IsInducing (point G b) := by
  letI := G.ambient.zariskiTopology
  exact IsInducing.subtypeVal.comp (closedPointHomeomorph G b).isInducing

def closedLocus (V : Set (groupProjectiveClosure G)) : TopologicalSpace.Closeds (scheme G b) :=
  .closure (point G b '' V)

theorem preimage_closedLocus (V : Set (groupProjectiveClosure G))
    (hV : letI := G.ambient.zariskiTopology; IsClosed V) :
    point G b ⁻¹' (closedLocus G b V : Set (scheme G b)) = V := by
  letI := G.ambient.zariskiTopology
  exact ((point_isInducing G b).closure_eq_preimage_closure_image V).symm.trans hV.closure_eq

def closedSubscheme (V : Set (groupProjectiveClosure G)) : Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal (closedLocus G b V)).subscheme

def closedSubschemeι (V : Set (groupProjectiveClosure G)) : closedSubscheme G b V ⟶ scheme G b :=
  (Scheme.IdealSheafData.vanishingIdeal (closedLocus G b V)).subschemeι

omit [IsAlgClosed K] in
theorem closedSubschemeι_isClosedImmersion (V : Set (groupProjectiveClosure G)) :
    IsClosedImmersion (closedSubschemeι G b V) := by
  dsimp only [closedSubschemeι]
  infer_instance

omit [IsAlgClosed K] in
theorem closedSubscheme_isReduced (V : Set (groupProjectiveClosure G)) :
    IsReduced (closedSubscheme G b V) :=
  reduced_subscheme_of_closed_set (closedLocus G b V)

theorem closedSubscheme_isProper (V : Set (groupProjectiveClosure G)) :
    IsProper (closedSubschemeι G b V ≫ structureMap G b) := by
  letI := closedSubschemeι_isClosedImmersion G b V
  letI := isProper G b
  infer_instance

theorem closedSubscheme_original_points (V : Set (groupProjectiveClosure G))
    (hV : letI := G.ambient.zariskiTopology; IsClosed V) :
    point G b ⁻¹' Set.range (closedSubschemeι G b V) = V := by
  have hrange : Set.range (closedSubschemeι G b V) =
      (closedLocus G b V : Set (scheme G b)) :=
    (Scheme.IdealSheafData.range_subschemeι
      (Scheme.IdealSheafData.vanishingIdeal (closedLocus G b V))).trans
        (Scheme.IdealSheafData.coe_support_vanishingIdeal _)
  rw [hrange]
  exact preimage_closedLocus G b V hV

end ClosureScheme
end PhilipponMultiplicity

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponClosureProjectiveEmbedding

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section

namespace PhilipponMultiplicity.ProjectiveCoordinateScheme
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousIdeal
universe u
variable {K : Type u} [Field K] {σ τ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

def renameGraded (e : σ ≃ τ) : homogeneousSubmodule σ K →+*ᵍ homogeneousSubmodule τ K where
  __ := (MvPolynomial.rename e : MvPolynomial σ K →ₐ[K] MvPolynomial τ K).toRingHom
  map_mem h := MvPolynomial.IsHomogeneous.rename_isHomogeneous h

theorem renameGraded_irrelevant (e : σ ≃ τ) :
    (homogeneousSubmodule τ K)₊ ≤ (homogeneousSubmodule σ K)₊.map (renameGraded e) := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro n hn P hP
  have heq : renameGraded (K := K) e (rename e.symm P) = P := by
    simp [renameGraded, rename_rename]
  rw [← heq]
  exact Ideal.mem_map_of_mem _
    (HomogeneousIdeal.mem_irrelevant_of_mem _ hn hP.rename_isHomogeneous)

theorem renameGraded_comp_symm (e : σ ≃ τ) :
    (renameGraded (K := K) e).comp (renameGraded e.symm) =
      GradedRingHom.id (homogeneousSubmodule τ K) := by
  ext P
  simp [renameGraded, rename_rename]

def renameProjIso (e : σ ≃ τ) :
    Proj (homogeneousSubmodule σ K) ≅ Proj (homogeneousSubmodule τ K) where
  hom := Proj.map (renameGraded e.symm) (renameGraded_irrelevant e.symm)
  inv := Proj.map (renameGraded e) (renameGraded_irrelevant e)
  hom_inv_id := by
    rw [← Proj.map_comp]
    have hc : (renameGraded (K := K) e.symm).comp (renameGraded e) =
        GradedRingHom.id (homogeneousSubmodule σ K) := by
      simpa only [Equiv.symm_symm] using renameGraded_comp_symm (K := K) e.symm
    simp only [hc, Proj.map_id]
  inv_hom_id := by
    rw [← Proj.map_comp]
    simp only [renameGraded_comp_symm, Proj.map_id]

theorem renameProjMap_over (e : σ ≃ τ) :
    Proj.map (renameGraded (K := K) e) (renameGraded_irrelevant e) ≫
      polynomialStructureMap = polynomialStructureMap := by
  let f := renameGraded (K := K) e
  let hf := renameGraded_irrelevant (K := K) e
  apply (Proj.mapAffineOpenCover f hf).openCover.hom_ext
  intro s
  change Proj.awayι (homogeneousSubmodule τ K) (f s.2) _ _ ≫
      (Proj.map f hf ≫ (Proj.toSpecZero (homogeneousSubmodule σ K) ≫ _)) =
    Proj.awayι (homogeneousSubmodule τ K) (f s.2) _ _ ≫
      (Proj.toSpecZero (homogeneousSubmodule τ K) ≫ _)
  rw [Proj.awayι_comp_map_assoc f hf s.1.2 _ s.2.2,
    ← Category.assoc (Proj.awayι _ _ _ _), Proj.awayι_toSpecZero,
    ← Category.assoc (Proj.awayι _ _ _ _), Proj.awayι_toSpecZero,
    ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext a
  simp [HomogeneousLocalization.Away.map, HomogeneousLocalization.map_mk,
    HomogeneousLocalization.fromZeroRingHom, f, renameGraded]

theorem renameProjIso_hom_over (e : σ ≃ τ) :
    (renameProjIso (K := K) e).hom ≫ polynomialStructureMap = polynomialStructureMap :=
  renameProjMap_over e.symm

end PhilipponMultiplicity.ProjectiveCoordinateScheme

namespace PhilipponMultiplicity.ClosureScheme
open AlgebraicGeometry CategoryTheory MvPolynomial ProjectiveCoordinateScheme
universe u
variable {K : Type u} [Field K] (G : EmbeddedGroupProduct K) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension (fun _ => 1)))
attribute [local instance] MvPolynomial.gradedAlgebra

def singleVariableEquiv (N : ℕ) : (projectiveSpace K N).Variable ≃ Fin (N + 1) where
  toFun v := v.2
  invFun j := ⟨(0 : Fin 1), j⟩
  left_inv v := by
    rcases v with ⟨i, j⟩
    have hi : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
    subst i
    rfl
  right_inv _ := rfl

end PhilipponMultiplicity.ClosureScheme

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectivePolynomialSections

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ProjectiveSections
open AlgebraicGeometry CategoryTheory MvPolynomial
universe u
variable {K : Type u} [Field K] {N : ℕ} {X : Scheme.{u}}
attribute [local instance] MvPolynomial.gradedAlgebra

def fraction (i : Fin (N + 1)) (d : ℕ)
    (F : homogeneousSubmodule (Fin (N + 1)) K d) :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin (N + 1)) K) (MvPolynomial.X i) :=
  HomogeneousLocalization.mk
    { deg := d
      num := F
      den := ⟨MvPolynomial.X i ^ d, isHomogeneous_X_pow i d⟩
      den_mem := ⟨d, rfl⟩ }

variable (φ : X ⟶ Proj (homogeneousSubmodule (Fin (N + 1)) K))

def polynomialSectionMap (d : ℕ) : homogeneousSubmodule (Fin (N + 1)) K d →ₗ[K]
    ProjSpace.twistObj (φ ≫ ProjSpace.π K N) φ d ⊤ :=
  Classical.choose (ProjSpace.exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq φ d)

theorem polynomialSectionMap_val (d : ℕ)
    (F : homogeneousSubmodule (Fin (N + 1)) K d) (i : Fin (N + 1)) :
    (polynomialSectionMap φ d F).val i =
      ProjSpace.restrictFun inf_le_right
        (φ.app (Proj.basicOpen _ (MvPolynomial.X i))
          (Proj.awayToSection _ (MvPolynomial.X i) (fraction i d F))) :=
  (Classical.choose_spec
    (ProjSpace.exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq φ d)).1 F.val F.property i

theorem polynomialSectionMap_eq_zero_iff (d : ℕ)
    (F : homogeneousSubmodule (Fin (N + 1)) K d) :
    polynomialSectionMap φ d F = 0 ↔ ∀ i : Fin (N + 1),
      φ.app (Proj.basicOpen _ (MvPolynomial.X i))
        (Proj.awayToSection _ (MvPolynomial.X i) (fraction i d F)) = 0 :=
  (Classical.choose_spec
    (ProjSpace.exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq φ d)).2 F.val F.property

theorem polynomialSectionMap_eventually_surjective [IsClosedImmersion φ] :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, Function.Surjective (polynomialSectionMap φ d) := by
  obtain ⟨d₀, hd₀⟩ :=
    ProjSpace.exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion φ
  refine ⟨d₀, fun d hd s => ?_⟩
  obtain ⟨F, hF, hval⟩ := hd₀ d hd
    (ProjSpace.objToTwistFam φ (φ ≫ ProjSpace.π K N) d s)
    (ProjSpace.objToTwistFam_mem φ (φ ≫ ProjSpace.π K N) d s)
  refine ⟨⟨F, hF⟩, ProjSpace.twistObj.val_injective (funext fun i => ?_)⟩
  rw [polynomialSectionMap_val]
  have hv := hval i
  simp [ProjSpace.objToTwistFam] at hv
  convert hv.symm using 1
  congr 3

end PhilipponMultiplicity.ProjectiveSections

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectiveTwistSheaf

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ProjectiveTwistSheaf
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace
open Scheme.Modules Scheme.Modules.GlueOfCocycle
universe u
variable {K : Type u} [Field K] {N : ℕ} {X : Scheme.{u}}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (φ : X ⟶ Proj (homogeneousSubmodule (Fin (N + 1)) K))

abbrev chart (i : ULift.{u} (Fin (N + 1))) : X.Opens := ProjSpace.pullbackChart φ i.down

theorem chart_cover : ⨆ i, chart φ i = ⊤ := by
  simpa only [chart, ProjSpace.pullbackChart, iSup_ulift] using
    (Scheme.Hom.iSup_preimage_eq_top φ
      (Proj.iSup_basicOpen_eq_top _ _ (ProjSpace.irrelevant_le_span_X K N)))

theorem frameUnit_mul_restrict (i j k : Fin (N + 1)) {W : X.Opens}
    (hi : W ≤ ProjSpace.pullbackChart φ i) (hj : W ≤ ProjSpace.pullbackChart φ j) :
    ProjSpace.restrictFun hi (ProjSpace.frameUnit φ i j) *
      ProjSpace.restrictFun hj (ProjSpace.frameUnit φ j k) =
      ProjSpace.restrictFun hi (ProjSpace.frameUnit φ i k) := by
  have hW : W ≤ ProjSpace.pullbackOverlap φ i j := by
    rw [ProjSpace.pullbackOverlap_eq_inf]
    exact le_inf hi hj
  have h := congrArg (ProjSpace.restrictFun hW) (ProjSpace.frameUnit_cocycle φ i j k)
  simpa only [map_mul, ProjSpace.restrictFun_restrictFun] using h

def cocycle (d : ℕ) : UnitCocycle (chart φ) where
  u i j := ProjSpace.restrictFun inf_le_left (ProjSpace.frameUnit φ i.down j.down) ^ d
  refl i := by rw [ProjSpace.frameUnit_self, map_one, one_pow]
  cocycle i j k := by
    dsimp only [chart]
    change ProjSpace.restrictFun _ (ProjSpace.restrictFun _ _ ^ d) *
      ProjSpace.restrictFun _ (ProjSpace.restrictFun _ _ ^ d) =
      ProjSpace.restrictFun _ (ProjSpace.restrictFun _ _ ^ d)
    simp only [map_pow, ProjSpace.restrictFun_restrictFun]
    rw [← mul_pow, frameUnit_mul_restrict]

abbrev twistSheaf (d : ℕ) : X.Modules := glueOfCocycle (cocycle φ d)

theorem twistSheaf_isInvertible (d : ℕ) : IsInvertible (twistSheaf φ d) :=
  isInvertible_glueOfCocycle (chart_cover φ) (cocycle φ d)

theorem rO_eq_restrictFun {U W : X.Opens} (h : W ≤ U) :
    rO h = ProjSpace.restrictFun h := rfl

theorem families_iff_twistCompat (d : ℕ) (U : X.Opens)
    (x : ∀ i : ULift.{u} (Fin (N + 1)), Γ(X, U ⊓ chart φ i)) :
    x ∈ families (cocycle φ d) U ↔
      ProjSpace.TwistCompat φ d U (fun i => x ⟨i⟩) := by
  constructor
  · intro hx i j
    have h := congrArg (rO (le_of_eq (inf_assoc U
      (ProjSpace.pullbackChart φ i) (ProjSpace.pullbackChart φ j)))) (hx ⟨i⟩ ⟨j⟩)
    dsimp only [cocycle, chart] at h ⊢
    simpa only [rO_eq_restrictFun, map_mul, map_pow,
      ProjSpace.restrictFun_restrictFun] using h
  · intro hx i j
    have h := congrArg (rO (le_of_eq (inf_assoc U
      (chart φ i) (chart φ j)).symm)) (hx i.down j.down)
    dsimp only [cocycle, chart] at h ⊢
    simpa only [rO_eq_restrictFun, map_mul, map_pow,
      ProjSpace.restrictFun_restrictFun] using h

def sectionEquiv (π : X ⟶ Spec (.of K)) (d : ℕ) (U : X.Opens) :
    Γ(twistSheaf φ d, U) ≃ₗ[Γ(X, U)] ProjSpace.twistObj π φ d U where
  toFun s := ⟨fun i => (s : families (cocycle φ d) U).val ⟨i⟩,
    (families_iff_twistCompat φ d U _).mp (s : families (cocycle φ d) U).property⟩
  invFun s := (⟨fun i => s.val i.down,
    (families_iff_twistCompat φ d U _).mpr s.compat⟩ : families (cocycle φ d) U)
  left_inv _ := by apply Subtype.ext; funext i; rfl
  right_inv _ := by apply ProjSpace.twistObj.val_injective; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem sectionEquiv_res (π : X ⟶ Spec (.of K)) (d : ℕ) {U U' : X.Opens}
    (h : U ≤ U') (s : Γ(twistSheaf φ d, U')) :
    sectionEquiv φ π d U ((twistSheaf φ d).presheaf.map (homOfLE h).op s) =
      ProjSpace.twistRes π φ d h (sectionEquiv φ π d U' s) := by
  apply ProjSpace.twistObj.val_injective
  rfl

end PhilipponMultiplicity.ProjectiveTwistSheaf
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponCocycleRefinement

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.CocycleCalculus
open AlgebraicGeometry CategoryTheory MonoidalCategory
open Scheme.Modules Scheme.Modules.GlueOfCocycle
universe u v
variable {X : Scheme.{u}} {ι κ : Type u} {U : ι → X.Opens}

theorem ext {c c' : UnitCocycle U} (h : ∀ i j, c.u i j = c'.u i j) : c = c' := by
  cases c
  cases c'
  congr
  funext i j
  exact h i j

def refinement (c : UnitCocycle U) (V : κ → X.Opens) (r : κ → ι)
    (h : ∀ a, V a ≤ U (r a)) : UnitCocycle V where
  u a b := rO (inf_le_inf (h a) (h b)) (c.u (r a) (r b))
  refl a := by rw [c.refl, map_one]
  cocycle a b d := by
    simp only [rO_rO]
    exact c.cocycle_le (r a) (r b) (r d) _ _ _

theorem refinement_iso (c : UnitCocycle U) (V : κ → X.Opens) (hV : ⨆ a, V a = ⊤)
    (r : κ → ι) (h : ∀ a, V a ≤ U (r a)) :
    Nonempty (glueOfCocycle c ≅ glueOfCocycle (refinement c V r h)) := by
  let e (a : κ) : Γ(glueOfCocycle c, V a) :=
    (glueOfCocycle c).presheaf.map (homOfLE (h a)).op (glueFrame c (r a))
  have he (a : κ) : IsFrameOn (e a) (V a) :=
    ((isFrameOn_glueFrame c (r a)).map (homOfLE (h a))).mono (h a)
  have htrans (a b : κ) :
      (glueOfCocycle c).presheaf.map (homOfLE (inf_le_right : V a ⊓ V b ≤ V b)).op (e b) =
        (refinement c V r h).u a b •
          (glueOfCocycle c).presheaf.map (homOfLE (inf_le_left : V a ⊓ V b ≤ V a)).op (e a) := by
    apply glue_ext
    intro k
    simp only [e, glueComponent_map, glueComponent_smul, glueComponent_glueFrame,
      refinement, rO_rO]
    rw [mul_comm]
    exact (c.cocycle_le k (r a) (r b)
      (le_inf inf_le_right (inf_le_left.trans (inf_le_left.trans (h a))))
      (inf_le_left.trans (inf_le_inf (h a) (h b)))
      (le_inf inf_le_right (inf_le_left.trans (inf_le_right.trans (h b))))).symm
  obtain ⟨e, -⟩ := exists_iso_glueOfCocycle_app_eq_glueFrame hV (refinement c V r h) e he htrans
  exact ⟨e⟩

def power (c : UnitCocycle U) (n : ℕ) : UnitCocycle U where
  u i j := c.u i j ^ n
  refl i := by rw [c.refl, one_pow]
  cocycle i j k := by
    simp only [map_pow]
    rw [← mul_pow, c.cocycle]

def finiteProduct {α : Type v} [Fintype α] (c : α → UnitCocycle U) : UnitCocycle U where
  u i j := ∏ a, (c a).u i j
  refl i := by simp only [(c _).refl, Finset.prod_const_one]
  cocycle i j k := by
    simp only [map_prod]
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun a _ => (c a).cocycle i j k

theorem trivial_iso (hU : ⨆ i, U i = ⊤) :
    Nonempty (glueOfCocycle (UnitCocycle.trivial U) ≅ 𝟙_ X.Modules) := by
  obtain ⟨e, -⟩ := exists_iso_glueOfCocycle_app_eq_glueFrame hU (UnitCocycle.trivial U)
    (fun i => unitSection (U i)) (fun i => isFrameOn_unitSection (U i)) (by
      intro i j
      simp only [map_unitSection, UnitCocycle.trivial, one_smul])
  exact ⟨e.symm⟩

theorem power_iso_tensorPow (hU : ⨆ i, U i = ⊤) (c : UnitCocycle U) (n : ℕ) :
    Nonempty (glueOfCocycle (power c n) ≅ (glueOfCocycle c).tensorPow n) := by
  induction n with
  | zero =>
      have h : power c 0 = UnitCocycle.trivial U := ext fun _ _ => pow_zero _
      rw [h, tensorPow_zero]
      exact trivial_iso hU
  | succ n ih =>
      have h : power c (n + 1) = (power c n).mul c := ext fun _ _ => pow_succ _ _
      rw [h, tensorPow_succ]
      obtain ⟨e, -⟩ := exists_glueOfCocycle_mul_iso_tensor hU (power c n) c
      obtain ⟨e'⟩ := ih
      exact ⟨e ≪≫ (e' ⊗ᵢ Iso.refl _)⟩

end PhilipponMultiplicity.CocycleCalculus
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProductRegularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open Set MvPolynomial
open scoped Topology

namespace PhilipponMultiplicity
universe u
variable {K : Type u} [Field K]

theorem MultiProjectiveSpace.projection_regular (M : MultiProjectiveSpace K)
    (i : M.FactorIndex) :
    M.IsRegularAlong (projectiveSpace K (M.ambientDimension i)) id (fun p _ => p i) := by
  let := M.zariskiTopology
  intro x b
  refine ⟨univ, isOpen_univ, mem_univ _, (fun a => if a = i then 1 else 0),
    (fun j => X ⟨i, j⟩), (fun j => M.isHomogeneous_X ⟨i, j⟩), ?_⟩
  intro y _
  simp only [MultiProjectiveSpace.eval, eval_X, MultiProjectiveSpace.coordinate, id_eq]
  exact ⟨Projectivization.rep_nonzero (y i), Projectivization.mk_rep (y i)⟩

end PhilipponMultiplicity
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponClosureProjectiveMaps

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option synthInstance.maxHeartbeats 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ProjectivePointComparison
open AlgebraicGeometry CategoryTheory MvPolynomial ProjectiveCoordinateScheme
universe u
variable {K : Type u} [Field K] (N : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

theorem bot_multihomogeneous :
    IsMultihomogeneousIdeal (projectiveSpace K N) ⊥ := by
  intro F hF d
  simp [Ideal.mem_bot.mp hF]

def ambientMap (I : Ideal (projectiveSpace K N).CoordinateRing)
    (hI : IsMultihomogeneousIdeal (projectiveSpace K N) I) :
    scheme N I hI ⟶ Proj (homogeneousSubmodule (Fin (N + 1)) K) :=
  quotientMap I (ordinaryHomogeneous N I hI) ≫
    (renameProjIso (ClosureScheme.singleVariableEquiv (K := K) N)).hom

theorem ambientMap_over (I : Ideal (projectiveSpace K N).CoordinateRing)
    (hI : IsMultihomogeneousIdeal (projectiveSpace K N) I) :
    ambientMap N I hI ≫ polynomialStructureMap =
      ProjectiveCoordinateScheme.structureMap I (ordinaryHomogeneous N I hI) := by
  rw [ambientMap, Category.assoc, renameProjIso_hom_over, quotientMap_over]

def ambientPoint (p : (projectiveSpace K N).Point) :
    Proj (homogeneousSubmodule (Fin (N + 1)) K) :=
  ambientMap N ⊥ (bot_multihomogeneous N)
    (point N ⊥ (bot_multihomogeneous N) ⟨p, by
      intro F hF
      simp [Ideal.mem_bot.mp hF, MultiProjectiveSpace.eval]⟩)

theorem ambientPoint_mem_basicOpen (p : (projectiveSpace K N).Point)
    (F : MvPolynomial (Fin (N + 1)) K) (d : ℕ) (hF : F.IsHomogeneous d) (hd : 0 < d) :
    ambientPoint N p ∈ Proj.basicOpen _ F ↔
      (projectiveSpace K N).eval
        (rename (ClosureScheme.singleVariableEquiv (K := K) N).symm F) p ≠ 0 := by
  let x : (projectiveSpace K N).zeroLocus (⊥ : Ideal (projectiveSpace K N).CoordinateRing) :=
    ⟨p, by intro P hP; simp [Ideal.mem_bot.mp hP, MultiProjectiveSpace.eval]⟩
  change point N ⊥ (bot_multihomogeneous N) x ∈
    polynomialOpen ⊥ (ordinaryHomogeneous N ⊥ (bot_multihomogeneous N))
      (rename (ClosureScheme.singleVariableEquiv (K := K) N).symm F) ↔ _
  exact point_mem_polynomialOpen N ⊥ (bot_multihomogeneous N) x _ d
    hF.rename_isHomogeneous hd

end PhilipponMultiplicity.ProjectivePointComparison

namespace PhilipponMultiplicity.ClosureScheme
open AlgebraicGeometry CategoryTheory MvPolynomial ProjectiveCoordinateScheme
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] (G : EmbeddedGroupProduct K) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension (fun _ => 1)))
attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_regular_projectiveMap (r : ℕ)
    (f : groupProjectiveClosure G → (projectiveSpace K r).Point)
    (hf : G.ambient.IsRegularAlong (projectiveSpace K r) Subtype.val f) :
    ∃ F : scheme G b ⟶ Proj (homogeneousSubmodule (Fin (r + 1)) K),
      F ≫ polynomialStructureMap = structureMap G b ∧
      ∀ x, F (point G b x) = ProjectivePointComparison.ambientPoint r (f x) := by
  let J := Hilbert.SegreVeronese.diagonalIdeal G.ambient (fun _ => 1) b (ideal G)
  let hJ := Hilbert.SegreVeronese.diagonalIdeal_homogeneous G.ambient (fun _ => 1) b
    (fun _ => le_rfl) (ideal G) (ideal_homogeneous G)
  let e := (locusEquiv G).trans
    (Hilbert.SegreVeronese.locusEquiv G.ambient b (ideal G) (ideal_homogeneous G))
  let f' : (projectiveSpace K N).zeroLocus J → (projectiveSpace K r).zeroLocus ⊥ :=
    fun y => ⟨f (e.symm y), by
      intro P hP
      simp [Ideal.mem_bot.mp hP, MultiProjectiveSpace.eval]⟩
  have hf' : (projectiveSpace K N).IsRegularAlong (projectiveSpace K r)
      Subtype.val (fun y => (f' y).val) :=
    (Hilbert.SegreVeronese.locusEquiv_inverse_regular G.ambient b (ideal G)
      (ideal_homogeneous G)).comp (hf.comp_domain e.symm)
  obtain ⟨F, ⟨hF, hpoint⟩, _⟩ := ProjectivePointComparison.existsUnique_regular_schemeMap
    N r J hJ ((ideal_radical G).comap
      (Hilbert.SegreVeronese.substitution G.ambient (fun _ => 1) b).toRingHom)
    ⊥ (ProjectivePointComparison.bot_multihomogeneous r) f' hf'
  refine ⟨F ≫ ProjectivePointComparison.ambientMap r ⊥
      (ProjectivePointComparison.bot_multihomogeneous r), ?_, ?_⟩
  · rw [Category.assoc, ProjectivePointComparison.ambientMap_over, hF]
    rfl
  · intro x
    change ProjectivePointComparison.ambientMap r ⊥ _
      (F (ProjectivePointComparison.point N J hJ (e x))) = _
    rw [hpoint]
    simp only [f', Equiv.symm_apply_apply, ProjectivePointComparison.ambientPoint]

theorem exists_factorMap (i : G.FactorIndex) :
    ∃ F : scheme G b ⟶ Proj (homogeneousSubmodule (Fin (G.ambient.ambientDimension i + 1)) K),
      F ≫ polynomialStructureMap = structureMap G b ∧
      ∀ x, F (point G b x) =
        ProjectivePointComparison.ambientPoint (G.ambient.ambientDimension i) (fun _ => x.val i) :=
  exists_regular_projectiveMap G b _ (fun x _ => x.val i)
    ((G.ambient.projection_regular i).comp_domain Subtype.val)

end PhilipponMultiplicity.ClosureScheme

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponHyperplanePresentation

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ProjectiveTwistSheaf
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace
open Scheme.Modules Scheme.Modules.GlueOfCocycle
universe u
variable {K : Type u} [Field K] {N : ℕ} {X : Scheme.{u}}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (φ : X ⟶ Proj (homogeneousSubmodule (Fin (N + 1)) K))

def coordinateSection (i : Fin (N + 1)) : Γ(twistSheaf φ 1, ⊤) :=
  glueMk (cocycle φ 1) ⊤
    (fun j => ProjSpace.restrictFun inf_le_right (ProjSpace.frameUnit φ j.down i))
    (by
      intro j k
      dsimp only [cocycle, chart]
      simp only [pow_one, rO_eq_restrictFun, ProjSpace.restrictFun_restrictFun]
      exact (frameUnit_mul_restrict φ j.down k.down i _ _).symm)

theorem coordinateSection_component (i : Fin (N + 1)) (j : ULift.{u} (Fin (N + 1))) :
    glueComponent (cocycle φ 1) ⊤ j (coordinateSection φ i) =
      ProjSpace.restrictFun inf_le_right (ProjSpace.frameUnit φ j.down i) := rfl

theorem coordinateSection_restrict_eq_glueFrame (i : Fin (N + 1)) :
    (twistSheaf φ 1).presheaf.map (homOfLE (le_top : chart φ ⟨i⟩ ≤ ⊤)).op
      (coordinateSection φ i) = glueFrame (cocycle φ 1) ⟨i⟩ := by
  apply glue_ext
  intro j
  rw [glueComponent_map, coordinateSection_component, glueComponent_glueFrame]
  simp only [cocycle, pow_one, rO_eq_restrictFun, ProjSpace.restrictFun_restrictFun]

theorem coordinateSection_frame (i : Fin (N + 1)) (U : X.Opens)
    (hU : U ≤ ProjSpace.pullbackChart φ i) :
    Function.Bijective (fun g : Γ(X, U) =>
      g • (twistSheaf φ 1).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
        (coordinateSection φ i)) := by
  have he : (twistSheaf φ 1).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
      (coordinateSection φ i) =
    (twistSheaf φ 1).presheaf.map (homOfLE hU).op (glueFrame (cocycle φ 1) ⟨i⟩) := by
    rw [← coordinateSection_restrict_eq_glueFrame]
    apply glue_ext
    intro j
    simp only [glueComponent_map, rO_rO]
  rw [he]
  exact isFrameOn_glueFrame (cocycle φ 1) ⟨i⟩ hU hU

theorem coordinateSection_ratio (i j : Fin (N + 1)) :
    ProjSpace.frameUnit φ i j •
      (twistSheaf φ 1).presheaf.map
        (homOfLE (le_top : ProjSpace.pullbackChart φ i ≤ ⊤)).op (coordinateSection φ i) =
      (twistSheaf φ 1).presheaf.map
        (homOfLE (le_top : ProjSpace.pullbackChart φ i ≤ ⊤)).op (coordinateSection φ j) := by
  apply glue_ext
  intro k
  rw [glueComponent_smul, glueComponent_map, glueComponent_map,
    coordinateSection_component, coordinateSection_component]
  simp only [rO_eq_restrictFun, ProjSpace.restrictFun_restrictFun]
  rw [mul_comm]
  exact frameUnit_mul_restrict φ k.down i j inf_le_right inf_le_left

def presentation : (twistSheaf φ 1).ProjPresentation (φ ≫ ProjSpace.π K N) N where
  σ := coordinateSection φ
  toProj := φ
  toProj_π := rfl
  frame := coordinateSection_frame φ
  app_ratio_smul := coordinateSection_ratio φ

theorem presentation_isFinite [IsFinite φ] :
    IsFinite (presentation φ).toProj := inferInstanceAs (IsFinite φ)

end PhilipponMultiplicity.ProjectiveTwistSheaf
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponClosureFactorHyperplanes

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ClosureScheme
open AlgebraicGeometry CategoryTheory MvPolynomial ProjectiveTwistSheaf
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] (G : EmbeddedGroupProduct K) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension (fun _ => 1)))
attribute [local instance] MvPolynomial.gradedAlgebra

def factorMap (i : G.FactorIndex) :
    scheme G b ⟶ Proj (homogeneousSubmodule (Fin (G.ambient.ambientDimension i + 1)) K) :=
  (exists_factorMap G b i).choose

theorem factorMap_over (i : G.FactorIndex) :
    factorMap G b i ≫ ProjSpace.π K (G.ambient.ambientDimension i) = structureMap G b :=
  (exists_factorMap G b i).choose_spec.1

theorem factorMap_point (i : G.FactorIndex) (x : groupProjectiveClosure G) :
    factorMap G b i (point G b x) =
      ProjectivePointComparison.ambientPoint (G.ambient.ambientDimension i) (fun _ => x.val i) :=
  (exists_factorMap G b i).choose_spec.2 x

abbrev factorHyperplane (i : G.FactorIndex) : (scheme G b).Modules :=
  twistSheaf (factorMap G b i) 1

theorem factorHyperplane_isInvertible (i : G.FactorIndex) :
    Scheme.Modules.IsInvertible (factorHyperplane G b i) :=
  twistSheaf_isInvertible (factorMap G b i) 1

abbrev closedSubschemeFactorMap (V : Set (groupProjectiveClosure G)) (i : G.FactorIndex) :=
  closedSubschemeι G b V ≫ factorMap G b i

end PhilipponMultiplicity.ClosureScheme
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponHyperplanePullback

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ProjectiveTwistSheaf
open AlgebraicGeometry CategoryTheory MvPolynomial
universe u
variable {K : Type u} [Field K] {N : ℕ} {X Y : Scheme.{u}}
attribute [local instance] MvPolynomial.gradedAlgebra

theorem hyperplane_pullback_iso (φ : Y ⟶ Proj (homogeneousSubmodule (Fin (N + 1)) K))
    (f : X ⟶ Y) :
    Nonempty ((Scheme.Modules.pullback f).obj (twistSheaf φ 1) ≅ twistSheaf (f ≫ φ) 1) := by
  obtain ⟨p, -, hp⟩ := (presentation φ).exists_projPresentation_pullback_sigma_eq_toProj_eq f
  let q : (twistSheaf (f ≫ φ) 1).ProjPresentation (f ≫ (φ ≫ ProjSpace.π K N)) N :=
    { presentation (f ≫ φ) with toProj_π := Category.assoc f φ (ProjSpace.π K N) }
  exact p.nonempty_iso_of_toProj_eq q hp

end PhilipponMultiplicity.ProjectiveTwistSheaf

namespace PhilipponMultiplicity.ClosureScheme
open AlgebraicGeometry CategoryTheory ProjectiveTwistSheaf
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] (G : EmbeddedGroupProduct K) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension (fun _ => 1)))

end PhilipponMultiplicity.ClosureScheme
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProductHyperplaneCocycle

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ProductHyperplanes
open AlgebraicGeometry CategoryTheory MonoidalCategory MvPolynomial TopologicalSpace
open Scheme.Modules Scheme.Modules.GlueOfCocycle ProjectiveTwistSheaf CocycleCalculus
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type u} [Field K] {X : Scheme.{u}} {ι : Type} [Fintype ι]
    (N : ι → ℕ) (φ : ∀ i, X ⟶ Proj (homogeneousSubmodule (Fin (N i + 1)) K))

abbrev Pivot := ∀ i, ULift.{u} (Fin (N i + 1))

def chart (a : Pivot N) : X.Opens := ⨅ i, ProjectiveTwistSheaf.chart (φ i) (a i)

theorem chart_le (a : Pivot N) (i : ι) :
    chart N φ a ≤ ProjectiveTwistSheaf.chart (φ i) (a i) := iInf_le _ i

theorem chart_cover : ⨆ a, chart N φ a = ⊤ := by
  classical
  apply top_unique
  intro x hx
  have he (i : ι) : ∃ a, x ∈ ProjectiveTwistSheaf.chart (φ i) a := by
    apply Opens.mem_iSup.mp
    rw [ProjectiveTwistSheaf.chart_cover]
    trivial
  choose a ha using he
  apply Opens.mem_iSup.mpr
  refine ⟨a, ?_⟩
  change x ∈ ((⨅ i, ProjectiveTwistSheaf.chart (φ i) (a i) : X.Opens) : Set X)
  rw [Opens.coe_iInf]
  exact Set.mem_iInter.mpr ha

def factorCocycle (i : ι) : UnitCocycle (chart N φ) :=
  refinement (cocycle (φ i) 1) (chart N φ) (fun a => a i) (fun a => chart_le N φ a i)

theorem factorCocycle_iso (i : ι) :
    Nonempty (glueOfCocycle (factorCocycle N φ i) ≅ twistSheaf (φ i) 1) := by
  obtain ⟨e⟩ := refinement_iso (cocycle (φ i) 1) (chart N φ) (chart_cover N φ)
    (fun a => a i) (fun a => chart_le N φ a i)
  exact ⟨e.symm⟩

def degreeCocycle (D : ι → ℕ) : UnitCocycle (chart N φ) :=
  finiteProduct (fun i => power (factorCocycle N φ i) (D i))

abbrev twist (D : ι → ℕ) : X.Modules := glueOfCocycle (degreeCocycle N φ D)

theorem twist_isInvertible (D : ι → ℕ) : IsInvertible (twist N φ D) :=
  isInvertible_glueOfCocycle (chart_cover N φ) (degreeCocycle N φ D)

theorem degreeCocycle_add (D E : ι → ℕ) :
    degreeCocycle N φ (D + E) = (degreeCocycle N φ D).mul (degreeCocycle N φ E) := by
  apply CocycleCalculus.ext
  intro a b
  simp only [degreeCocycle, finiteProduct, power, Pi.add_apply, pow_add,
    Finset.prod_mul_distrib, UnitCocycle.mul]

theorem twist_add_iso (D E : ι → ℕ) :
    Nonempty (twist N φ (D + E) ≅ twist N φ D ⊗ twist N φ E) := by
  change Nonempty (glueOfCocycle (degreeCocycle N φ (D + E)) ≅ _)
  rw [degreeCocycle_add]
  obtain ⟨e, -⟩ := exists_glueOfCocycle_mul_iso_tensor (chart_cover N φ)
    (degreeCocycle N φ D) (degreeCocycle N φ E)
  exact ⟨e⟩

theorem twist_zero_iso : Nonempty (twist N φ 0 ≅ 𝟙_ X.Modules) := by
  have h : degreeCocycle N φ 0 = UnitCocycle.trivial (chart N φ) := by
    apply CocycleCalculus.ext
    intro a b
    simp only [degreeCocycle, finiteProduct, power, Pi.zero_apply, pow_zero,
      Finset.prod_const_one, UnitCocycle.trivial]
  change Nonempty (glueOfCocycle (degreeCocycle N φ 0) ≅ _)
  rw [h]
  exact trivial_iso (chart_cover N φ)

theorem twist_single_iso [DecidableEq ι] (i : ι) (n : ℕ) :
    Nonempty (twist N φ (Pi.single i n) ≅ (twistSheaf (φ i) 1).tensorPow n) := by
  have h : degreeCocycle N φ (Pi.single i n) = power (factorCocycle N φ i) n := by
    apply CocycleCalculus.ext
    intro a b
    change (∏ j, (factorCocycle N φ j).u a b ^ (Pi.single i n j)) = _
    rw [Finset.prod_eq_single i]
    · rw [Pi.single_eq_same]
      rfl
    · intro j hj hji
      rw [Pi.single_eq_of_ne hji, pow_zero]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  change Nonempty (glueOfCocycle (degreeCocycle N φ (Pi.single i n)) ≅ _)
  rw [h]
  obtain ⟨e⟩ := power_iso_tensorPow (chart_cover N φ) (factorCocycle N φ i) n
  obtain ⟨e'⟩ := factorCocycle_iso N φ i
  have hpow : Nonempty ((glueOfCocycle (factorCocycle N φ i)).tensorPow n ≅
      (twistSheaf (φ i) 1).tensorPow n) := by
    clear h e
    induction n with
    | zero => exact ⟨Iso.refl _⟩
    | succ n ih => obtain ⟨f⟩ := ih; exact ⟨f ⊗ᵢ e'⟩
  exact ⟨e ≪≫ hpow.some⟩

end PhilipponMultiplicity.ProductHyperplanes
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProductHyperplaneClasses

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ProductHyperplanes
open AlgebraicGeometry CategoryTheory MonoidalCategory MvPolynomial
open ProjectiveTwistSheaf Scheme.Modules
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type u} [Field K] {X : Scheme.{u}} {ι : Type} [Fintype ι]
    (N : ι → ℕ) (φ : ∀ i, X ⟶ Proj (homogeneousSubmodule (Fin (N i + 1)) K))

theorem tensorPow_class (M : X.Modules) (n : ℕ) :
    toSkeleton (M.tensorPow n) = toSkeleton M ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [tensorPow_succ, Skeleton.toSkeleton_tensorObj, ih, pow_succ]

def degreeClass : Multiplicative (ι → ℕ) →* Skeleton X.Modules where
  toFun D := toSkeleton (twist N φ D.toAdd)
  map_one' := toSkeleton_eq_toSkeleton_iff.mpr (twist_zero_iso N φ)
  map_mul' D E :=
    (toSkeleton_eq_toSkeleton_iff.mpr (twist_add_iso N φ D.toAdd E.toAdd)).trans
      (Skeleton.toSkeleton_tensorObj _ _)

theorem twist_class (D : ι → ℕ) :
    toSkeleton (twist N φ D) = ∏ i, toSkeleton (twistSheaf (φ i) 1) ^ D i := by
  classical
  change degreeClass N φ (Multiplicative.ofAdd D) = _
  conv_lhs => rw [← Finset.univ_sum_single D]
  rw [ofAdd_sum, map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact (toSkeleton_eq_toSkeleton_iff.mpr (twist_single_iso N φ i (D i))).trans
    (tensorPow_class _ _)

end PhilipponMultiplicity.ProductHyperplanes
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProductTwistPullback

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ProductHyperplanes
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X Y : Scheme.{u}}

def pullbackClass (f : X ⟶ Y) : Skeleton Y.Modules →* Skeleton X.Modules :=
  Skeleton.monoidHom (pullback f)

theorem pullbackClass_toSkeleton (f : X ⟶ Y) (M : Y.Modules) :
    pullbackClass f (toSkeleton M) = toSkeleton ((pullback f).obj M) :=
  Functor.mapSkeleton_obj_toSkeleton (pullback f) M

variable {K : Type u} [Field K] {ι : Type} [Fintype ι]
    (N : ι → ℕ)
    (φ : ∀ i, Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N i + 1)) K))

theorem twist_pullback_iso (D : ι → ℕ) (f : X ⟶ Y) :
    Nonempty ((pullback f).obj (twist N φ D) ≅ twist N (fun i => f ≫ φ i) D) := by
  apply toSkeleton_eq_toSkeleton_iff.mp
  rw [← pullbackClass_toSkeleton, twist_class, map_prod, twist_class]
  apply Finset.prod_congr rfl
  intro i hi
  rw [map_pow, pullbackClass_toSkeleton]
  congr 1
  exact toSkeleton_eq_toSkeleton_iff.mpr (ProjectiveTwistSheaf.hyperplane_pullback_iso (φ i) f)

end PhilipponMultiplicity.ProductHyperplanes
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponInvertibleClassLattice

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.InvertibleClassLattice
open AlgebraicGeometry CategoryTheory MonoidalCategory
open Scheme.Modules
universe u v
variable {X : Scheme.{u}}

def unitClass (M : X.Modules) (hM : IsInvertible M) : (Skeleton X.Modules)ˣ := by
  let N := hM.exists_tensor_inverse_monoidalV2.choose
  let e := hM.exists_tensor_inverse_monoidalV2.choose_spec.2.some
  have he : toSkeleton M * toSkeleton N = 1 :=
    (Skeleton.toSkeleton_tensorObj M N).symm.trans (congr_toSkeleton_of_iso e)
  exact ⟨toSkeleton M, toSkeleton N, he, by rw [mul_comm]; exact he⟩

theorem unitClass_val (M : X.Modules) (hM : IsInvertible M) :
    (unitClass M hM).val = toSkeleton M := rfl

variable {S : Type v} (B : S → X.Modules) (hB : ∀ s, IsInvertible (B s))

def unitHom : Multiplicative (FreeAbelianGroup S) →* (Skeleton X.Modules)ˣ :=
  AddMonoidHom.toMultiplicativeLeft
    (FreeAbelianGroup.lift (fun s => Additive.ofMul (unitClass (B s) (hB s))))

def classHom : Multiplicative (FreeAbelianGroup S) →* Skeleton X.Modules :=
  (Units.coeHom (Skeleton X.Modules)).comp (unitHom B hB)

theorem classHom_generator (s : S) :
    classHom B hB (Multiplicative.ofAdd (FreeAbelianGroup.of s)) = toSkeleton (B s) := by
  change ((FreeAbelianGroup.lift (fun s => Additive.ofMul (unitClass (B s) (hB s))))
    (FreeAbelianGroup.of s)).toMul.val = _
  rw [FreeAbelianGroup.lift_apply_of]
  exact unitClass_val (B s) (hB s)

theorem exists_representative (l : FreeAbelianGroup S) :
    ∃ M : X.Modules, IsInvertible M ∧ toSkeleton M = classHom B hB (Multiplicative.ofAdd l) := by
  induction l using FreeAbelianGroup.induction_on with
  | zero =>
      exact ⟨𝟙_ X.Modules, isInvertible_unit X, (map_one (classHom B hB)).symm⟩
  | of s => exact ⟨B s, hB s, (classHom_generator B hB s).symm⟩
  | neg s ih =>
      obtain ⟨M, hM, hm⟩ := ih
      obtain ⟨N, hN, ⟨e⟩⟩ := hM.exists_tensor_inverse_monoidalV2
      refine ⟨N, hN, ?_⟩
      let a := unitHom B hB (Multiplicative.ofAdd (FreeAbelianGroup.of s))
      have he : a.val * toSkeleton N = 1 := by
        change classHom B hB (Multiplicative.ofAdd (FreeAbelianGroup.of s)) * toSkeleton N = 1
        rw [← hm, ← Skeleton.toSkeleton_tensorObj]
        exact congr_toSkeleton_of_iso e
      change toSkeleton N = (unitHom B hB (Multiplicative.ofAdd (-FreeAbelianGroup.of s))).val
      rw [ofAdd_neg, map_inv]
      change toSkeleton N = a.inv
      calc
        _ = a.inv * (a.val * toSkeleton N) := by rw [← mul_assoc, a.inv_val, one_mul]
        _ = a.inv := by rw [he, mul_one]
  | add l m ihl ihm =>
      obtain ⟨M, hM, hm⟩ := ihl
      obtain ⟨N, hN, hn⟩ := ihm
      refine ⟨M ⊗ N, hM.tensor_monoidalV2 hN, ?_⟩
      rw [Skeleton.toSkeleton_tensorObj, hm, hn, ofAdd_add, map_mul]

def representative (l : FreeAbelianGroup S) : X.Modules :=
  (exists_representative B hB l).choose

theorem representative_isInvertible (l : FreeAbelianGroup S) :
    IsInvertible (representative B hB l) := (exists_representative B hB l).choose_spec.1

theorem representative_class (l : FreeAbelianGroup S) :
    toSkeleton (representative B hB l) = classHom B hB (Multiplicative.ofAdd l) :=
  (exists_representative B hB l).choose_spec.2

end PhilipponMultiplicity.InvertibleClassLattice
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponFreeTwistAction

set_option autoImplicit false
set_option maxHeartbeats 150000
noncomputable section

namespace PhilipponMultiplicity.FreeTwistAction
universe u v
variable (Γ : Type u) [AddCommGroup Γ] (ι : Type v)

abbrev Lattice := FreeAbelianGroup (Γ × ι)

def indexShift (g : Γ) : Γ × ι ≃ Γ × ι where
  toFun s := (g + s.1, s.2)
  invFun s := (-g + s.1, s.2)
  left_inv s := by simp
  right_inv s := by simp

def shift (g : Γ) : Lattice Γ ι ≃ₗ[ℤ] Lattice Γ ι :=
  (FreeAbelianGroup.equivOfEquiv (indexShift Γ ι g)).toIntLinearEquiv

def action : Multiplicative Γ →* (Lattice Γ ι ≃ₗ[ℤ] Lattice Γ ι) where
  toFun g := shift Γ ι g.toAdd
  map_one' := by
    apply LinearEquiv.ext
    intro l
    change FreeAbelianGroup.map (indexShift Γ ι 0) l = l
    have h : (indexShift Γ ι 0 : Γ × ι → Γ × ι) = id := by
      funext s
      simp [indexShift]
    rw [h, FreeAbelianGroup.map_id_apply]
  map_mul' g h := by
    apply LinearEquiv.ext
    intro l
    change FreeAbelianGroup.map (indexShift Γ ι (g.toAdd + h.toAdd)) l =
      FreeAbelianGroup.map (indexShift Γ ι g.toAdd)
        (FreeAbelianGroup.map (indexShift Γ ι h.toAdd) l)
    rw [← FreeAbelianGroup.map_comp_apply]
    congr 1
    apply congrArg FreeAbelianGroup.map
    funext s
    simp [indexShift, Function.comp_def, add_assoc]

def factor (i : ι) : Lattice Γ ι := FreeAbelianGroup.of (0, i)

theorem action_generator (g h : Γ) (i : ι) :
    action Γ ι (Multiplicative.ofAdd g) (FreeAbelianGroup.of (h, i)) =
      FreeAbelianGroup.of (g + h, i) := rfl

end PhilipponMultiplicity.FreeTwistAction

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponVeroneseInverseEquations

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.Hilbert.SegreVeronese.Positive
open MvPolynomial
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (D : M.FactorIndex → ℕ) (hD : ∀ i, 1 ≤ D i)
    (a : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))

def pivotProduct : M.CoordinateRing := ∏ i, X ⟨i, a i⟩ ^ D i

theorem pivotProduct_homogeneous : M.IsHomogeneous (pivotProduct M D a) D :=
  variable_product_homogeneous M a D

def pivotForm : degreePiece K M.factorCount M.ambientDimension D :=
  ⟨pivotProduct M D a, (M.degreePiece_iff _ _).mpr (pivotProduct_homogeneous M D a)⟩

def omittedProduct (i : M.FactorIndex) : M.CoordinateRing :=
  ∏ k, X ⟨k, a k⟩ ^ (D k - if k = i then 1 else 0)

theorem omittedProduct_homogeneous (i : M.FactorIndex) :
    M.IsHomogeneous (omittedProduct M D a i) (fun k => D k - if k = i then 1 else 0) :=
  variable_product_homogeneous M a _

include hD in
theorem omittedProduct_mul_pivot (i : M.FactorIndex) :
    omittedProduct M D a i * X ⟨i, a i⟩ = pivotProduct M D a := by
  classical
  calc
    _ = (∏ k, (X ⟨k, a k⟩ : M.CoordinateRing) ^ (D k - if k = i then 1 else 0)) *
        (∏ k, (X ⟨k, a k⟩ : M.CoordinateRing) ^ (if k = i then 1 else 0)) := by
      simp [omittedProduct]
    _ = ∏ k, (X ⟨k, a k⟩ : M.CoordinateRing) ^ (D k - if k = i then 1 else 0) *
        X ⟨k, a k⟩ ^ (if k = i then 1 else 0) := by rw [Finset.prod_mul_distrib]
    _ = pivotProduct M D a := by
      apply Finset.prod_congr rfl
      intro k _
      rw [← pow_add]
      congr 1
      by_cases h : k = i
      · simp only [h, if_true]
        exact Nat.sub_add_cancel (hD i)
      · simp [h]

include hD in
theorem sum_degree_pos : 0 < ∑ i, D i := by
  let i : M.FactorIndex := ⟨0, M.positive⟩
  exact lt_of_lt_of_le (hD i) (Finset.single_le_sum (fun j _ => Nat.zero_le (D j))
    (Finset.mem_univ i))

include hD in
theorem prod_omittedProducts :
    (∏ i, omittedProduct M D a i ^ D i) =
      pivotProduct M D a ^ ((∑ i, D i) - 1) := by
  classical
  have hS : pivotProduct M D a ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact pow_ne_zero _ (X_ne_zero (⟨i, a i⟩ : M.Variable))
  apply mul_right_cancel₀ hS
  calc
    _ = ∏ i, (omittedProduct M D a i * X ⟨i, a i⟩) ^ D i := by
      simp only [mul_pow, Finset.prod_mul_distrib, pivotProduct]
    _ = ∏ i, pivotProduct M D a ^ D i := by
      simp only [omittedProduct_mul_pivot M D hD a]
    _ = pivotProduct M D a ^ (∑ i, D i) := Finset.prod_pow_eq_pow_sum _ _ _
    _ = pivotProduct M D a ^ ((∑ i, D i) - 1) * pivotProduct M D a := by
      rw [← pow_succ, Nat.sub_add_cancel (sum_degree_pos M D hD)]

def replacementForm (v : M.Variable) : degreePiece K M.factorCount M.ambientDimension D :=
  ⟨omittedProduct M D a v.1 * X v, by
    apply (M.degreePiece_iff _ _).mpr
    have h := (omittedProduct_homogeneous M D a v.1).mul M (M.isHomogeneous_X v)
    convert h using 1
    ext i
    by_cases hi : i = v.1
    · simp only [hi, Pi.add_apply, if_true]
      exact (Nat.sub_add_cancel (hD v.1)).symm
    · simp [hi]⟩

@[simp] theorem replacementForm_pivot (i : M.FactorIndex) :
    replacementForm M D hD a ⟨i, a i⟩ = pivotForm M D a := by
  apply Subtype.ext
  exact omittedProduct_mul_pivot M D hD a i

variable {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (degreePiece K M.factorCount M.ambientDimension D))

def inverseSubstitution : M.CoordinateRing →ₐ[K] (projectiveSpace K N).CoordinateRing :=
  aeval (fun v => (linearForm M D b (replacementForm M D hD a v)).val)

theorem substitution_inverseSubstitution (P : M.CoordinateRing)
    (E : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P E) :
    substitution M D b (inverseSubstitution M D hD a b P) =
      (∏ i, omittedProduct M D a i ^ E i) * P := by
  have hcomp : (substitution M D b).comp (inverseSubstitution M D hD a b) =
      aeval (fun v => omittedProduct M D a v.1 * X v) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [AlgHom.comp_apply, inverseSubstitution, aeval_X,
      substitution_linearForm, replacementForm]
  change ((substitution M D b).comp (inverseSubstitution M D hD a b)) P = _
  rw [hcomp]
  have h := AffineChartDomain.eval₂_block_scale M (C : K →+* M.CoordinateRing)
    P E hP (fun v => X v) (omittedProduct M D a)
  change eval₂ C (fun v => omittedProduct M D a v.1 * X v) P = _
  simpa only [coe_eval₂Hom, eval₂_eta] using h

theorem inverseSubstitution_mem_diagonal (I : Ideal M.CoordinateRing)
    (P : M.CoordinateRing) (hP : P ∈ I)
    (E : M.FactorIndex → ℕ) (hE : M.IsHomogeneous P E) :
    inverseSubstitution M D hD a b P ∈ diagonalIdeal M D b I := by
  change substitution M D b (inverseSubstitution M D hD a b P) ∈ I
  rw [substitution_inverseSubstitution M D hD a b P E hE]
  exact I.mul_mem_left _ hP

theorem inverse_basis_relation (I : Ideal M.CoordinateRing)
    (j : (projectiveSpace K N).Variable) :
    inverseSubstitution M D hD a b (b j).val -
      X j * (linearForm M D b (pivotForm M D a)).val ^ ((∑ i, D i) - 1) ∈
        diagonalIdeal M D b I := by
  change substitution M D b _ ∈ I
  rw [map_sub, substitution_inverseSubstitution M D hD a b _ D
    ((M.degreePiece_iff _ _).mp (b j).property)]
  simp only [prod_omittedProducts M D hD a, map_mul, map_pow,
    substitution_linearForm, pivotForm]
  have hx : substitution M D b (X j) = (b j).val := by simp [substitution]
  rw [hx, mul_comm, sub_self]
  exact I.zero_mem

end PhilipponMultiplicity.Hilbert.SegreVeronese.Positive

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProductPolynomialSections

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ProductHyperplanes
open AlgebraicGeometry CategoryTheory MonoidalCategory MvPolynomial TopologicalSpace
open Scheme.Modules Scheme.Modules.GlueOfCocycle ProjectiveTwistSheaf CocycleCalculus
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type u} [Field K] {X : Scheme.{u}} (M : MultiProjectiveSpace K)
    (π : X ⟶ Spec (.of K))
    (φ : ∀ i : M.FactorIndex, X ⟶ Proj (homogeneousSubmodule (Fin (M.ambientDimension i + 1)) K))

def coordinateOnChart (a : Pivot M.ambientDimension) (U : X.Opens)
    (hU : U ≤ chart M.ambientDimension φ a) (v : M.Variable) : Γ(X, U) :=
  rO (hU.trans (chart_le M.ambientDimension φ a v.1))
    (ProjSpace.frameUnit (φ v.1) (a v.1).down v.2)

def evalOnChart (a : Pivot M.ambientDimension) (U : X.Opens)
    (hU : U ≤ chart M.ambientDimension φ a) : M.CoordinateRing →+* Γ(X, U) :=
  eval₂Hom (Scheme.TwoAffineOpenCover.algebraOfHom π U).algebraMap
    (coordinateOnChart M φ a U hU)

theorem evalOnChart_restrict (a : Pivot M.ambientDimension) {U W : X.Opens}
    (hU : U ≤ chart M.ambientDimension φ a) (h : W ≤ U) (P : M.CoordinateRing) :
    rO h (evalOnChart M π φ a U hU P) = evalOnChart M π φ a W (h.trans hU) P := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π W
  have hc : (rO h).comp (Scheme.TwoAffineOpenCover.algebraOfHom π U).algebraMap =
      (Scheme.TwoAffineOpenCover.algebraOfHom π W).algebraMap := by
    ext k
    exact (Scheme.TwoAffineOpenCover.restrictAlgHom π h).commutes k
  simp only [evalOnChart, map_eval₂Hom, hc, coordinateOnChart, rO_rO]
  rfl

theorem coordinateOnChart_transition (a b : Pivot M.ambientDimension) {W : X.Opens}
    (ha : W ≤ chart M.ambientDimension φ a) (hb : W ≤ chart M.ambientDimension φ b)
    (v : M.Variable) :
    coordinateOnChart M φ a W ha v =
      rO (ha.trans (chart_le M.ambientDimension φ a v.1))
        (ProjSpace.frameUnit (φ v.1) (a v.1).down (b v.1).down) *
      coordinateOnChart M φ b W hb v := by
  exact (frameUnit_mul_restrict (φ v.1) (a v.1).down (b v.1).down v.2
    (ha.trans (chart_le M.ambientDimension φ a v.1))
    (hb.trans (chart_le M.ambientDimension φ b v.1))).symm

theorem evalOnChart_transition (D : M.FactorIndex → ℕ) (P : M.CoordinateRing)
    (hP : M.IsHomogeneous P D) (a b : Pivot M.ambientDimension) {W : X.Opens}
    (ha : W ≤ chart M.ambientDimension φ a) (hb : W ≤ chart M.ambientDimension φ b) :
    evalOnChart M π φ a W ha P =
      rO (le_inf ha hb) ((degreeCocycle M.ambientDimension φ D).u a b) *
        evalOnChart M π φ b W hb P := by
  have hc := AffineChartDomain.eval₂_block_scale M
    (Scheme.TwoAffineOpenCover.algebraOfHom π W).algebraMap P D hP
    (coordinateOnChart M φ b W hb)
    (fun i => rO (ha.trans (chart_le M.ambientDimension φ a i))
      (ProjSpace.frameUnit (φ i) (a i).down (b i).down))
  have hcoord : coordinateOnChart M φ a W ha = fun v : M.Variable =>
      rO (ha.trans (chart_le M.ambientDimension φ a v.1))
        (ProjSpace.frameUnit (φ v.1) (a v.1).down (b v.1).down) *
          coordinateOnChart M φ b W hb v := by
    funext v
    exact coordinateOnChart_transition M φ a b ha hb v
  dsimp only [evalOnChart]
  rw [hcoord, hc]
  congr 1
  simp only [degreeCocycle, finiteProduct, power, factorCocycle, refinement, cocycle,
    pow_one, map_prod, map_pow, rO_rO]

def polynomialSection (D : M.FactorIndex → ℕ) (P : M.CoordinateRing)
    (hP : M.IsHomogeneous P D) : Γ(twist M.ambientDimension φ D, ⊤) :=
  glueMk (degreeCocycle M.ambientDimension φ D) ⊤
    (fun a => evalOnChart M π φ a (⊤ ⊓ chart M.ambientDimension φ a) inf_le_right P)
    (by
      intro a b
      rw [evalOnChart_restrict, evalOnChart_restrict]
      exact evalOnChart_transition M π φ D P hP a b _ _)

theorem polynomialSection_component (D : M.FactorIndex → ℕ) (P : M.CoordinateRing)
    (hP : M.IsHomogeneous P D) (a : Pivot M.ambientDimension) :
    glueComponent (degreeCocycle M.ambientDimension φ D) ⊤ a (polynomialSection M π φ D P hP) =
      evalOnChart M π φ a (⊤ ⊓ chart M.ambientDimension φ a) inf_le_right P := rfl

end PhilipponMultiplicity.ProductHyperplanes
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectiveFractionSupport

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ProjectiveFractions
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
universe u
variable {R : Type u} [CommRing R] {σ : Type*}
    [SetLike σ R] [AddSubgroupClass σ R] (𝒜 : ℕ → σ) [GradedRing 𝒜]

theorem basicOpen_awayToSection_mk (f : R)
    (s : NumDenSameDeg 𝒜 (Submonoid.powers f)) :
    (Proj 𝒜).basicOpen (Proj.awayToSection 𝒜 f (HomogeneousLocalization.mk s)) =
      Proj.basicOpen 𝒜 f ⊓ Proj.basicOpen 𝒜 s.num.val := by
  ext p
  constructor
  · intro hp
    have hpf : p ∈ Proj.basicOpen 𝒜 f := (Proj 𝒜).basicOpen_le _ hp
    refine ⟨hpf, ?_⟩
    have hp := (Scheme.mem_basicOpen _ _ p hpf).mp hp
    have hgerm := congrArg (fun h => h (HomogeneousLocalization.mk s))
      (ProjectiveSpectrum.Proj.awayToSection_germ 𝒜 f p hpf)
    change (Proj 𝒜).presheaf.germ _ p hpf
        (Proj.awayToSection 𝒜 f (HomogeneousLocalization.mk s)) = _ at hgerm
    rw [hgerm] at hp
    change IsUnit ((Proj.stalkIso' 𝒜 p).symm
      (HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr hpf)
        (HomogeneousLocalization.mk s))) at hp
    rw [isUnit_map_iff] at hp
    rw [← HomogeneousLocalization.isUnit_iff_isUnit_val, HomogeneousLocalization.mapId,
      HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk,
      Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff] at hp
    exact hp
  · rintro ⟨hpf, hpn⟩
    apply (Scheme.mem_basicOpen _ _ p hpf).mpr
    have hgerm := congrArg (fun h => h (HomogeneousLocalization.mk s))
      (ProjectiveSpectrum.Proj.awayToSection_germ 𝒜 f p hpf)
    change (Proj 𝒜).presheaf.germ _ p hpf
        (Proj.awayToSection 𝒜 f (HomogeneousLocalization.mk s)) = _ at hgerm
    rw [hgerm]
    change IsUnit ((Proj.stalkIso' 𝒜 p).symm
      (HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr hpf)
        (HomogeneousLocalization.mk s)))
    rw [isUnit_map_iff]
    rw [← HomogeneousLocalization.isUnit_iff_isUnit_val, HomogeneousLocalization.mapId,
      HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk,
      Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff]
    exact hpn

end PhilipponMultiplicity.ProjectiveFractions

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectiveSectionKernel

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ProjectiveSections
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace
universe u
variable {K : Type u} [Field K] {N : ℕ} {X : Scheme.{u}}
attribute [local instance] MvPolynomial.gradedAlgebra

variable (φ : X ⟶ Proj (homogeneousSubmodule (Fin (N + 1)) K)) [IsReduced X]

theorem chartSection_eq_zero_iff (i : Fin (N + 1)) (d : ℕ)
    (F : homogeneousSubmodule (Fin (N + 1)) K d) :
    φ.app (Proj.basicOpen _ (MvPolynomial.X i))
      (Proj.awayToSection _ (MvPolynomial.X i) (fraction i d F)) = 0 ↔
      (φ ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i)) ⊓ (φ ⁻¹ᵁ Proj.basicOpen _ F.val) = ⊥ := by
  rw [← AlgebraicGeometry.basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen]
  unfold fraction
  rw [ProjectiveFractions.basicOpen_awayToSection_mk]
  rfl

theorem polynomialSectionMap_eq_zero_iff_preimage (d : ℕ)
    (F : homogeneousSubmodule (Fin (N + 1)) K d) :
    polynomialSectionMap φ d F = 0 ↔ φ ⁻¹ᵁ Proj.basicOpen _ F.val = ⊥ := by
  rw [polynomialSectionMap_eq_zero_iff]
  constructor
  · intro h
    apply le_bot_iff.mp
    intro x hx
    have htop : φ x ∈ ⨆ i : Fin (N + 1), Proj.basicOpen _ (MvPolynomial.X i) := by
      rw [Proj.iSup_basicOpen_eq_top _ _ (ProjSpace.irrelevant_le_span_X K N)]
      trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp htop
    have hh : x ∈ (φ ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i)) ⊓
        (φ ⁻¹ᵁ Proj.basicOpen _ F.val) := ⟨hi, hx⟩
    rw [(chartSection_eq_zero_iff φ i d F).mp (h i)] at hh
    exact hh
  · intro h i
    apply (chartSection_eq_zero_iff φ i d F).mpr
    rw [h, inf_bot_eq]

end PhilipponMultiplicity.ProjectiveSections
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectiveLinearFractions

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ProjectiveSections
open AlgebraicGeometry CategoryTheory MvPolynomial
open Scheme.Modules.GlueOfCocycle
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type u} [Field K] {N : ℕ} {X : Scheme.{u}}

def coordinateForm (i : Fin (N + 1)) : homogeneousSubmodule (Fin (N + 1)) K 1 :=
  ⟨MvPolynomial.X i, isHomogeneous_X K i⟩

theorem fraction_coordinate (i j : Fin (N + 1)) :
    fraction i 1 (coordinateForm (K := K) j) = ProjSpace.ratio K N i j := by
  apply HomogeneousLocalization.val_injective
  simp only [fraction, coordinateForm, ProjSpace.ratio, HomogeneousLocalization.val_mk,
    HomogeneousLocalization.Away.val_mk, pow_one]

variable (φ : X ⟶ Proj (homogeneousSubmodule (Fin (N + 1)) K))

theorem polynomialSectionMap_coordinate (i j : Fin (N + 1)) :
    (polynomialSectionMap φ 1 (coordinateForm j)).val i =
      ProjSpace.restrictFun inf_le_right (ProjSpace.frameUnit φ i j) := by
  rw [polynomialSectionMap_val, fraction_coordinate]
  rfl

theorem chartFraction_linear_difference (i j : Fin (N + 1)) (c : K) :
    φ.app (Proj.basicOpen _ (MvPolynomial.X i))
      (Proj.awayToSection _ (MvPolynomial.X i)
        (fraction i 1 (coordinateForm j - c • coordinateForm i))) =
      ProjSpace.frameUnit φ i j -
        (Scheme.TwoAffineOpenCover.algebraOfHom (φ ≫ ProjSpace.π K N)
          (ProjSpace.pullbackChart φ i)).algebraMap c := by
  have h := congrArg (fun s => s.val i)
    (map_sub (polynomialSectionMap φ 1) (coordinateForm j) (c • coordinateForm i))
  rw [map_smul] at h
  change (polynomialSectionMap φ 1 (coordinateForm j - c • coordinateForm i)).val i =
    (polynomialSectionMap φ 1 (coordinateForm j)).val i -
      ProjSpace.restrictFun inf_le_left
        ((Scheme.TwoAffineOpenCover.algebraOfHom (φ ≫ ProjSpace.π K N) ⊤).algebraMap c) *
      (polynomialSectionMap φ 1 (coordinateForm i)).val i at h
  rw [polynomialSectionMap_val, polynomialSectionMap_coordinate,
    polynomialSectionMap_coordinate, ProjSpace.frameUnit_self, map_one, mul_one,
    ProjSpace.restrictFun_algebraMap'] at h
  apply (rO_bijective_of_le_le
    (inf_le_right : ⊤ ⊓ ProjSpace.pullbackChart φ i ≤ ProjSpace.pullbackChart φ i)
    (le_inf le_top le_rfl)).1
  change ProjSpace.restrictFun inf_le_right _ = ProjSpace.restrictFun inf_le_right _
  rw [map_sub, ProjSpace.restrictFun_algebraMap']
  exact h

theorem basicOpen_frameUnit_difference (i j : Fin (N + 1)) (c : K) :
    X.basicOpen (ProjSpace.frameUnit φ i j -
      (Scheme.TwoAffineOpenCover.algebraOfHom (φ ≫ ProjSpace.π K N)
        (ProjSpace.pullbackChart φ i)).algebraMap c) =
      (φ ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i)) ⊓
        (φ ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X j - MvPolynomial.C c * MvPolynomial.X i)) := by
  rw [← chartFraction_linear_difference, ← Scheme.preimage_basicOpen]
  unfold fraction
  rw [ProjectiveFractions.basicOpen_awayToSection_mk]
  simp only [coordinateForm, Submodule.coe_sub, Submodule.coe_smul,
    smul_eq_C_mul]
  rfl

theorem evaluation_frameUnit_eq_of_numerator_notMem
    (i j : Fin (N + 1)) (c : K) (x : X) (hx : x ∈ ProjSpace.pullbackChart φ i)
    (hnum : φ x ∉ Proj.basicOpen _ (MvPolynomial.X j - MvPolynomial.C c * MvPolynomial.X i)) :
    X.evaluation (ProjSpace.pullbackChart φ i) x hx (ProjSpace.frameUnit φ i j) =
      X.evaluation (ProjSpace.pullbackChart φ i) x hx
        ((Scheme.TwoAffineOpenCover.algebraOfHom (φ ≫ ProjSpace.π K N)
          (ProjSpace.pullbackChart φ i)).algebraMap c) := by
  apply sub_eq_zero.mp
  rw [← map_sub, Scheme.evaluation_eq_zero_iff_notMem_basicOpen,
    basicOpen_frameUnit_difference]
  exact fun h => hnum h.2

end PhilipponMultiplicity.ProjectiveSections
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProductPointEvaluation

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ProductHyperplanes
open AlgebraicGeometry CategoryTheory MvPolynomial
open Scheme.Modules.GlueOfCocycle
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type u} [Field K] {X : Scheme.{u}}

theorem evaluation_restrict {U W : X.Opens} (h : W ≤ U)
    (x : X) (hx : x ∈ W) (s : Γ(X, U)) :
    X.evaluation W x hx (rO h s) = X.evaluation U x (h hx) s := by
  change X.residue x (X.presheaf.germ W x hx (X.presheaf.map (homOfLE h).op s)) = _
  rw [X.presheaf.germ_res_apply]
  rfl

def residueScalar (π : X ⟶ Spec (.of K)) (x : X) : K →+* X.residueField x :=
  (X.Γevaluation x).hom.comp (Scheme.TwoAffineOpenCover.algebraOfHom π ⊤).algebraMap

theorem evaluation_scalar (π : X ⟶ Spec (.of K)) (U : X.Opens)
    (x : X) (hx : x ∈ U) (c : K) :
    X.evaluation U x hx ((Scheme.TwoAffineOpenCover.algebraOfHom π U).algebraMap c) =
      residueScalar π x c := by
  rw [← ProjSpace.restrictFun_algebraMap' π le_top]
  exact evaluation_restrict le_top x hx _

variable (M : MultiProjectiveSpace K) (π : X ⟶ Spec (.of K))
    (φ : ∀ i : M.FactorIndex, X ⟶ Proj (homogeneousSubmodule (Fin (M.ambientDimension i + 1)) K))
    (hφ : ∀ i, φ i ≫ ProjSpace.π K (M.ambientDimension i) = π)
    (x : X) (p : M.Point)
    (hp : ∀ i, φ i x = ProjectivePointComparison.ambientPoint (M.ambientDimension i) (fun _ => p i))

include hp in
theorem point_mem_chart (a : Pivot M.ambientDimension)
    (ha : ∀ i, (p i).rep (a i).down ≠ 0) : x ∈ chart M.ambientDimension φ a := by
  change x ∈ (↑(⨅ i, ProjectiveTwistSheaf.chart (φ i) (a i)) : Set X)
  rw [TopologicalSpace.Opens.coe_iInf]
  apply Set.mem_iInter.mpr
  intro i
  change φ i x ∈ Proj.basicOpen _ (MvPolynomial.X (a i).down)
  rw [hp i, ProjectivePointComparison.ambientPoint_mem_basicOpen _ _ _ 1
    (isHomogeneous_X K _) (by decide)]
  simpa [MultiProjectiveSpace.eval, MultiProjectiveSpace.coordinate, eval_rename,
    ClosureScheme.singleVariableEquiv] using ha i

include hφ hp in
theorem evaluation_coordinateOnChart (a : Pivot M.ambientDimension)
    (U : X.Opens) (hU : U ≤ chart M.ambientDimension φ a) (hx : x ∈ U)
    (ha : ∀ i, (p i).rep (a i).down ≠ 0) (v : M.Variable) :
    X.evaluation U x hx (coordinateOnChart M φ a U hU v) =
      residueScalar π x ((p v.1).rep v.2 / (p v.1).rep (a v.1).down) := by
  rw [coordinateOnChart, evaluation_restrict]
  rw [ProjectiveSections.evaluation_frameUnit_eq_of_numerator_notMem]
  · rw [hφ v.1]
    exact evaluation_scalar π _ x _ _
  · rw [hp v.1, ProjectivePointComparison.ambientPoint_mem_basicOpen _ _ _ 1
      ((isHomogeneous_X K _).sub ((isHomogeneous_X K _).C_mul _)) (by decide)]
    simp [MultiProjectiveSpace.eval, MultiProjectiveSpace.coordinate,
      ClosureScheme.singleVariableEquiv, div_mul_cancel₀ _ (ha v.1)]

include hφ hp in

theorem evaluation_evalOnChart (a : Pivot M.ambientDimension)
    (U : X.Opens) (hU : U ≤ chart M.ambientDimension φ a) (hx : x ∈ U)
    (ha : ∀ i, (p i).rep (a i).down ≠ 0) (P : M.CoordinateRing) :
    X.evaluation U x hx (evalOnChart M π φ a U hU P) =
      residueScalar π x (MvPolynomial.eval
        (fun v : M.Variable => (p v.1).rep v.2 / (p v.1).rep (a v.1).down) P) := by
  have h : (X.evaluation U x hx).hom.comp (evalOnChart M π φ a U hU) =
      (residueScalar π x).comp (MvPolynomial.eval
        (fun v : M.Variable => (p v.1).rep v.2 / (p v.1).rep (a v.1).down)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simpa only [RingHom.comp_apply, evalOnChart, eval₂Hom_C, eval_C] using
        evaluation_scalar π U x hx c
    · intro v
      simpa only [RingHom.comp_apply, evalOnChart, eval₂Hom_X', eval_X] using
        evaluation_coordinateOnChart M π φ hφ x p hp a U hU hx ha v
  exact RingHom.congr_fun h P

end PhilipponMultiplicity.ProductHyperplanes
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProductPivotFrames

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ProductHyperplanes
open AlgebraicGeometry CategoryTheory MvPolynomial
open Scheme.Modules Scheme.Modules.GlueOfCocycle ProjectiveTwistSheaf CocycleCalculus
open Hilbert.SegreVeronese.Positive
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type u} [Field K] {X : Scheme.{u}} (M : MultiProjectiveSpace K)
    (π : X ⟶ Spec (.of K))
    (φ : ∀ i : M.FactorIndex, X ⟶ Proj (homogeneousSubmodule (Fin (M.ambientDimension i + 1)) K))

theorem evalOnChart_pivotProduct (D : M.FactorIndex → ℕ)
    (a b : Pivot M.ambientDimension) (U : X.Opens)
    (hU : U ≤ chart M.ambientDimension φ a) :
    evalOnChart M π φ a U hU (pivotProduct M D (fun i => (b i).down)) =
      ∏ i, coordinateOnChart M φ a U hU ⟨i, (b i).down⟩ ^ D i := by
  simp only [pivotProduct, map_prod, map_pow, evalOnChart, coe_eval₂Hom, eval₂_X]

theorem polynomialSection_pivot_frame (D : M.FactorIndex → ℕ)
    (b : Pivot M.ambientDimension) :
    (twist M.ambientDimension φ D).presheaf.map
      (homOfLE (le_top : chart M.ambientDimension φ b ≤ ⊤)).op
      (polynomialSection M π φ D (pivotProduct M D (fun i => (b i).down))
        (pivotProduct_homogeneous M D (fun i => (b i).down))) =
      glueFrame (degreeCocycle M.ambientDimension φ D) b := by
  apply glue_ext
  intro a
  rw [glueComponent_map, polynomialSection_component, glueComponent_glueFrame,
    evalOnChart_restrict, evalOnChart_pivotProduct]
  simp only [coordinateOnChart, degreeCocycle, finiteProduct, power, factorCocycle,
    refinement, cocycle, pow_one, map_prod, map_pow, rO_rO]

theorem polynomialSection_pivot_isFrameOn (D : M.FactorIndex → ℕ)
    (b : Pivot M.ambientDimension) :
    IsFrameOn
      (polynomialSection M π φ D (pivotProduct M D (fun i => (b i).down))
        (pivotProduct_homogeneous M D (fun i => (b i).down)))
      (chart M.ambientDimension φ b) := by
  intro W hWtop hWb
  have heq : (twist M.ambientDimension φ D).presheaf.map (homOfLE hWtop).op
      (polynomialSection M π φ D (pivotProduct M D (fun i => (b i).down))
        (pivotProduct_homogeneous M D (fun i => (b i).down))) =
      (twist M.ambientDimension φ D).presheaf.map (homOfLE hWb).op
        (glueFrame (degreeCocycle M.ambientDimension φ D) b) := by
    rw [← polynomialSection_pivot_frame M π φ D b]
    change _ = ((twist M.ambientDimension φ D).presheaf.map
      (homOfLE (le_top : chart M.ambientDimension φ b ≤ ⊤)).op ≫
        (twist M.ambientDimension φ D).presheaf.map (homOfLE hWb).op) _
    rw [← Functor.map_comp]
    rfl
  rw [heq]
  exact isFrameOn_glueFrame (degreeCocycle M.ambientDimension φ D) b hWb hWb

end PhilipponMultiplicity.ProductHyperplanes
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponVeroneseInverseChart

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.Hilbert.SegreVeronese.Positive
open MvPolynomial
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K) (D : M.FactorIndex → ℕ) (hD : ∀ i, 1 ≤ D i) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (degreePiece K M.factorCount M.ambientDimension D))

theorem pointMap_represents_of_lift (p : M.Point) (w : M.Variable → K)
    (hw : ∀ i, ∃ h : (fun j => w ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => w ⟨i, j⟩) h = p i)
    (i : (projectiveSpace K N).FactorIndex) :
    ∃ h : (fun j => aeval w (b ⟨i, j⟩).val) ≠ 0,
      Projectivization.mk K (fun j => aeval w (b ⟨i, j⟩).val) h =
        pointMap M D b p i := by
  obtain ⟨hn, he⟩ := pointMap_represents M D b p i
  obtain ⟨hn', he'⟩ := M.homogeneous_tuple_lift p w hw (fun j => (b ⟨i, j⟩).val)
    D (fun j => (M.degreePiece_iff _ _).mp (b ⟨i, j⟩).property) hn
  exact ⟨hn', he'.trans he⟩

theorem exists_inverse_on_pivot
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (p : (projectiveSpace K N).Point)
    (hp : p ∈ (projectiveSpace K N).zeroLocus (diagonalIdeal M D b I))
    (a : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))
    (ha : (projectiveSpace K N).eval
      (linearForm M D b (pivotForm M D a)).val p ≠ 0) :
    ∃ q : M.Point, q ∈ M.zeroLocus I ∧ pointMap M D b q = p ∧
      ∀ i : M.FactorIndex,
        ∃ h : (fun j => (projectiveSpace K N).eval
          (linearForm M D b (replacementForm M D hD a ⟨i, j⟩)).val p) ≠ 0,
          Projectivization.mk K (fun j => (projectiveSpace K N).eval
            (linearForm M D b (replacementForm M D hD a ⟨i, j⟩)).val p) h = q i := by
  classical
  let Q := projectiveSpace K N
  obtain ⟨z, hz, hzS, hzrep⟩ := MultiProjectiveSpace.exists_lift_normalized_by_linear_form N
    (diagonalIdeal M D b I)
    (diagonalIdeal_homogeneous M D b hD I hI)
    p hp (linearForm M D b (pivotForm M D a)).val
    (linearForm M D b (pivotForm M D a)).property ha
  let w : M.Variable → K := fun v =>
    aeval z (linearForm M D b (replacementForm M D hD a v)).val
  have hw_pivot (i : M.FactorIndex) : w ⟨i, a i⟩ = 1 := by
    simpa only [w, replacementForm_pivot] using hzS
  have hw (i : M.FactorIndex) : (fun j => w ⟨i, j⟩) ≠ 0 := by
    intro h
    have hz0 : w ⟨i, a i⟩ = 0 := congrFun h (a i)
    exact one_ne_zero ((hw_pivot i).symm.trans hz0)
  let q : M.Point := fun i => Projectivization.mk K (fun j => w ⟨i, j⟩) (hw i)
  have hqrep (i : M.FactorIndex) : ∃ h : (fun j => w ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => w ⟨i, j⟩) h = q i := ⟨hw i, rfl⟩
  have heval (P : M.CoordinateRing) :
      aeval w P = aeval z (inverseSubstitution M D hD a b P) :=
    (AffineClosedPoints.evaluate_substitution _ z P).symm
  have hbasis (j : Q.Variable) : aeval w (b j).val = z j := by
    have h := hz _ (inverse_basis_relation M D hD a b I j)
    rw [map_sub, map_mul, map_pow, aeval_X, hzS, one_pow, mul_one] at h
    exact (heval _).trans (sub_eq_zero.mp h)
  refine ⟨q, ?_, ?_, ?_⟩
  · apply (M.mem_zeroLocus_iff_homogeneous I hI q).mpr
    intro P hP E hE
    apply (M.eval_eq_zero_iff_of_lift q w hqrep P E hE).mp
    change aeval w P = 0
    rw [heval]
    exact hz _ (inverseSubstitution_mem_diagonal M D hD a b I P hP E hE)
  · funext i
    obtain ⟨hn, he⟩ := pointMap_represents_of_lift M D b q w hqrep i
    obtain ⟨hznon, hzpoint⟩ := hzrep i
    have hcoords : (fun j => aeval w (b ⟨i, j⟩).val) = (fun j => z ⟨i, j⟩) :=
      funext (fun j => hbasis ⟨i, j⟩)
    have hmk : Projectivization.mk K (fun j => aeval w (b ⟨i, j⟩).val) hn = p i := by
      simpa only [hcoords] using hzpoint
    exact he.symm.trans hmk
  · intro i
    let F : Fin (M.ambientDimension i + 1) → Q.CoordinateRing :=
      fun j => (linearForm M D b (replacementForm M D hD a ⟨i, j⟩)).val
    have hF (j) : Q.IsHomogeneous (F j) (fun _ => 1) :=
      (MultiProjectiveSpace.projective_homogeneous_iff N (F j) 1).mpr
        (linearForm M D b (replacementForm M D hD a ⟨i, j⟩)).property
    have hn : (fun j => Q.eval (F j) p) ≠ 0 := by
      intro h
      have hzero : Q.eval (F (a i)) p = 0 := congrFun h (a i)
      exact ha (by simpa only [F, replacementForm_pivot] using hzero)
    obtain ⟨hn', he⟩ := Q.homogeneous_tuple_lift p z hzrep F (fun _ => 1) hF hn
    exact ⟨hn, he.symm⟩

end PhilipponMultiplicity.Hilbert.SegreVeronese.Positive

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponVeronesePivotCover

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.Hilbert.SegreVeronese.Positive
open MvPolynomial
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (D : M.FactorIndex → ℕ) (hD : ∀ i, 1 ≤ D i)

def pivotExponent (a : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1)) : M.Variable →₀ ℕ :=
  ∑ i, Finsupp.single ⟨i, a i⟩ (D i)

theorem pivotExponent_apply (a : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))
    (v : M.Variable) : pivotExponent M D a v = if v.2 = a v.1 then D v.1 else 0 := by
  classical
  rw [pivotExponent, Finsupp.finsetSum_apply, Finset.sum_eq_single v.1]
  · rcases v with ⟨i, j⟩
    simp [Finsupp.single_apply, eq_comm]
  · intro i _ hi
    apply Finsupp.single_eq_of_ne
    intro he
    exact hi (congrArg Sigma.fst he).symm
  · simp

theorem pivotProduct_eq_monomial
    (a : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1)) :
    pivotProduct M D a = monomial (pivotExponent M D a) (1 : K) := by
  classical
  have h (s : Finset M.FactorIndex) :
      (∏ i ∈ s, (X ⟨i, a i⟩ : M.CoordinateRing) ^ D i) =
        monomial (∑ i ∈ s, Finsupp.single ⟨i, a i⟩ (D i)) (1 : K) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, X_pow_eq_monomial,
        monomial_mul, one_mul]
  exact h Finset.univ

theorem weight_pivotExponent
    (a : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1)) :
    Finsupp.weight (blockWeight M.factorCount M.ambientDimension) (pivotExponent M D a) = D := by
  have h := (M.degreePiece_iff _ _).mpr (pivotProduct_homogeneous M D a)
  rw [pivotProduct_eq_monomial] at h
  exact h (by simp)

include hD in

theorem exists_pivot_divisor (e : M.Variable →₀ ℕ)
    (he : Finsupp.weight (blockWeight M.factorCount M.ambientDimension) e = D) :
    ∃ (a : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1)) (Q : M.CoordinateRing),
      Q ∈ degreePiece K M.factorCount M.ambientDimension (fun i => ((∑ j, D j) - 1) * D i) ∧
      monomial e (1 : K) ^ (∑ i, D i) = pivotProduct M D a * Q := by
  classical
  have hp (i : M.FactorIndex) : ∃ j : Fin (M.ambientDimension i + 1), 1 ≤ e ⟨i, j⟩ := by
    have hs : 0 < ∑ j : Fin (M.ambientDimension i + 1), e ⟨i, j⟩ := by
      rw [← MonomialCells.weight_apply, he]
      exact hD i
    obtain ⟨j, _, hj⟩ := Finset.sum_pos_iff.mp hs
    exact ⟨j, hj⟩
  choose a ha using hp
  let m := ∑ i, D i
  let v := pivotExponent M D a
  have hv : v ≤ m • e := by
    intro x
    change pivotExponent M D a x ≤ (m • e) x
    rw [pivotExponent_apply]
    by_cases hx : x.2 = a x.1
    · rw [if_pos hx]
      have hepos : 1 ≤ e x := by
        rcases x with ⟨i, j⟩
        dsimp at hx
        subst j
        exact ha i
      have hbound : D x.1 ≤ m := Finset.single_le_sum (fun i _ => Nat.zero_le (D i))
        (Finset.mem_univ x.1)
      simp only [Finsupp.smul_apply, smul_eq_mul]
      nlinarith
    · simp [hx]
  let r := m • e - v
  have hr : r + v = m • e := tsub_add_cancel_of_le hv
  have hwr : Finsupp.weight (blockWeight M.factorCount M.ambientDimension) r =
      fun i => (m - 1) * D i := by
    have hw := congrArg (Finsupp.weight (blockWeight M.factorCount M.ambientDimension)) hr
    rw [map_add, map_nsmul, he, show Finsupp.weight
      (blockWeight M.factorCount M.ambientDimension) v = D from weight_pivotExponent M D a] at hw
    funext i
    have hi := congrFun hw i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi
    have hm : 1 ≤ m := sum_degree_pos M D hD
    have hmul : (m - 1) * D i + D i = m * D i := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hm]
    exact Nat.add_right_cancel (hi.trans hmul.symm)
  refine ⟨a, monomial r 1, isWeightedHomogeneous_monomial _ _ _ hwr, ?_⟩
  rw [pivotProduct_eq_monomial, monomial_pow, one_pow, monomial_mul, one_mul]
  exact congrArg (fun t : M.Variable →₀ ℕ => monomial t (1 : K))
    ((add_comm v r).trans hr).symm

end PhilipponMultiplicity.Hilbert.SegreVeronese.Positive

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponVeroneseMonomialBasis

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.Hilbert.SegreVeronese
open MvPolynomial
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K) (D : M.FactorIndex → ℕ)

abbrev MonomialIndex := {e : M.Variable →₀ ℕ //
  Finsupp.weight (blockWeight M.factorCount M.ambientDimension) e = D}

def monomialBasis : Module.Basis (MonomialIndex M D) K
    (degreePiece K M.factorCount M.ambientDimension D) :=
  (basisRestrictSupport K {e | Finsupp.weight (blockWeight M.factorCount M.ambientDimension) e = D}).map
    (LinearEquiv.ofEq _ _ (weightedHomogeneousSubmodule_eq_finsupp_supported K _ D).symm)

theorem monomialBasis_value (e : MonomialIndex M D) :
    (monomialBasis M D e).val = monomial e.val (1 : K) := by
  change ((basisRestrictSupport K
    {e | Finsupp.weight (blockWeight M.factorCount M.ambientDimension) e = D} e).val) = _
  rw [← Module.Basis.repr_symm_single_one]
  simp only [basisRestrictSupport, AddMonoidAlgebra.supportedEquivFinsupp,
    LinearEquiv.trans_symm, LinearEquiv.trans_apply]
  change AddMonoidAlgebra.ofCoeff
    (((Finsupp.supportedEquivFinsupp (R := K)
      {e : M.Variable →₀ ℕ | Finsupp.weight (blockWeight M.factorCount M.ambientDimension) e = D}).symm
        (Finsupp.single e 1)).val) = _
  rw [Finsupp.supportedEquivFinsupp_symm_single]
  rfl

instance monomialIndex_finite : Finite (MonomialIndex M D) :=
  Module.Finite.finite_basis (monomialBasis M D)

def pivotMonomialIndex (a : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1)) :
    MonomialIndex M D :=
  ⟨Positive.pivotExponent M D a, Positive.weight_pivotExponent M D a⟩

theorem monomialBasis_pivot (a : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1)) :
    monomialBasis M D (pivotMonomialIndex M D a) = Positive.pivotForm M D a := by
  apply Subtype.ext
  rw [monomialBasis_value]
  exact (Positive.pivotProduct_eq_monomial M D a).symm

theorem exists_monomial_coordinate_basis :
    ∃ (r : ℕ) (c : Module.Basis (projectiveSpace K r).Variable K
      (degreePiece K M.factorCount M.ambientDimension D)),
      ∀ a : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
        ∃ j, c j = Positive.pivotForm M D a := by
  classical
  letI : Fintype (MonomialIndex M D) := Fintype.ofFinite _
  let a₀ : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1) := fun _ => 0
  letI : Nonempty (MonomialIndex M D) := ⟨pivotMonomialIndex M D a₀⟩
  let r := Fintype.card (MonomialIndex M D) - 1
  have hc : Fintype.card (projectiveSpace K r).Variable = Fintype.card (MonomialIndex M D) := by
    simp [MultiProjectiveSpace.Variable, projectiveSpace, r,
      Nat.sub_add_cancel Fintype.card_pos]
  let e : MonomialIndex M D ≃ (projectiveSpace K r).Variable :=
    Fintype.equivOfCardEq hc.symm
  refine ⟨r, (monomialBasis M D).reindex e, fun a => ?_⟩
  refine ⟨e (pivotMonomialIndex M D a), ?_⟩
  simpa using monomialBasis_pivot M D a

end PhilipponMultiplicity.Hilbert.SegreVeronese

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProductProjectivePresentation

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ProductHyperplanes
open AlgebraicGeometry CategoryTheory MvPolynomial
open Scheme.Modules Scheme.Modules.GlueOfCocycle Hilbert.SegreVeronese.Positive
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type u} [Field K] {X : Scheme.{u}} (M : MultiProjectiveSpace K)
    (π : X ⟶ Spec (.of K))
    (φ : ∀ i : M.FactorIndex, X ⟶ Proj (homogeneousSubmodule (Fin (M.ambientDimension i + 1)) K))
    (D : M.FactorIndex → ℕ) {r : ℕ}
    (c : Module.Basis (projectiveSpace K r).Variable K
      (Hilbert.degreePiece K M.factorCount M.ambientDimension D))

def basisSection (j : Fin (r + 1)) : Γ(twist M.ambientDimension φ D, ⊤) :=
  polynomialSection M π φ D (c ⟨(0 : Fin 1), j⟩).val ((M.degreePiece_iff _ _).mp (c ⟨(0 : Fin 1), j⟩).property)

theorem exists_basisPresentation
    (hc : ∀ a : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
      ∃ j, c j = pivotForm M D a) :
    ∃ p : (twist M.ambientDimension φ D).ProjPresentation π r,
      p.σ = basisSection M π φ D c ∧
      ∀ a : Pivot M.ambientDimension, ∃ j : Fin (r + 1),
        c ⟨(0 : Fin 1), j⟩ = pivotForm M D (fun i => (a i).down) ∧
          chart M.ambientDimension φ a ≤ ProjSpace.pullbackChart p.toProj j := by
  classical
  have hidx (a : Pivot M.ambientDimension) : ∃ j : Fin (r + 1),
      c ⟨(0 : Fin 1), j⟩ = pivotForm M D (fun i => (a i).down) := by
    obtain ⟨⟨i, j⟩, hj⟩ := hc (fun i => (a i).down)
    have hi : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) i 0
    subst i
    exact ⟨j, hj⟩
  choose idx hidx using hidx
  let U (j : Fin (r + 1)) : X.Opens :=
    ⨆ a : {a : Pivot M.ambientDimension // idx a = j}, chart M.ambientDimension φ a.val
  have hle (a : Pivot M.ambientDimension) : chart M.ambientDimension φ a ≤ U (idx a) :=
    le_iSup (fun z : {z : Pivot M.ambientDimension // idx z = idx a} =>
      chart M.ambientDimension φ z.val) ⟨a, rfl⟩
  have hcover : ⨆ j, U j = ⊤ := by
    apply top_unique
    rw [← chart_cover M.ambientDimension φ]
    exact iSup_le fun a => (hle a).trans (le_iSup U (idx a))
  have hsection (a : Pivot M.ambientDimension) :
      basisSection M π φ D c (idx a) =
        polynomialSection M π φ D (pivotProduct M D (fun i => (a i).down))
          (pivotProduct_homogeneous M D (fun i => (a i).down)) := by
    dsimp only [basisSection]
    simp only [hidx a, pivotForm]
  have hframe (j : Fin (r + 1)) : IsFrameOn (basisSection M π φ D c j) (U j) := by
    apply IsFrameOn.of_iSup_monoidalV2
    intro a
    have hs := hsection a.val
    rw [a.property] at hs
    rw [hs]
    exact polynomialSection_pivot_isFrameOn M π φ D a.val
  obtain ⟨p, hp, hchart⟩ := exists_projPresentation_of_iSup_eq_top π
    (twist M.ambientDimension φ D) r (basisSection M π φ D c) U hcover
    (fun j W hW => hframe j le_top hW)
  exact ⟨p, hp, fun a => ⟨idx a, hidx a, (hle a).trans (hchart (idx a))⟩⟩

end PhilipponMultiplicity.ProductHyperplanes
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProductPresentationRatios

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ProductHyperplanes
open AlgebraicGeometry CategoryTheory MvPolynomial
open Scheme.Modules Scheme.Modules.GlueOfCocycle Hilbert.SegreVeronese.Positive
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type u} [Field K] {X : Scheme.{u}} (M : MultiProjectiveSpace K)
    (π : X ⟶ Spec (.of K))
    (φ : ∀ i : M.FactorIndex, X ⟶ Proj (homogeneousSubmodule (Fin (M.ambientDimension i + 1)) K))
    (D : M.FactorIndex → ℕ) {r : ℕ}
    (c : Module.Basis (projectiveSpace K r).Variable K
      (Hilbert.degreePiece K M.factorCount M.ambientDimension D))

theorem basisPresentation_ratio
    (p : (twist M.ambientDimension φ D).ProjPresentation π r)
    (hp : p.σ = basisSection M π φ D c)
    (a : Pivot M.ambientDimension) (ja : Fin (r + 1))
    (ha : c ⟨(0 : Fin 1), ja⟩ = pivotForm M D (fun i => (a i).down))
    (hchart : chart M.ambientDimension φ a ≤ ProjSpace.pullbackChart p.toProj ja)
    (j : Fin (r + 1)) :
    p.toProj.appLE (Proj.basicOpen _ (MvPolynomial.X ja)) (chart M.ambientDimension φ a) hchart
      (Proj.awayToSection _ (MvPolynomial.X ja) (ProjSpace.ratio K r ja j)) =
        evalOnChart M π φ a (chart M.ambientDimension φ a) le_rfl (c ⟨(0 : Fin 1), j⟩).val := by
  have h := congrArg (fun s => rO (le_inf hchart le_rfl)
    (glueComponent (degreeCocycle M.ambientDimension φ D)
      (ProjSpace.pullbackChart p.toProj ja) a s)) (p.app_ratio_smul ja j)
  dsimp only [ProjSpace.pullbackChart] at h
  simp only [hp, basisSection, glueComponent_smul, map_mul, rO_rO] at h
  rw [glueComponent_map, glueComponent_map, polynomialSection_component,
    polynomialSection_component] at h
  simp only [rO_rO, evalOnChart_restrict] at h
  simp only [ha, pivotForm, evalOnChart_pivotProduct, coordinateOnChart,
    ProjSpace.frameUnit_self, map_one, one_pow, Finset.prod_const_one, mul_one] at h
  exact h

end PhilipponMultiplicity.ProductHyperplanes
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectiveLinearPointExt

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ProjectivePointComparison
open AlgebraicGeometry CategoryTheory MvPolynomial
universe u v
variable {K : Type u} [Field K] {N : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

theorem eval₂_homogeneous_scale {A : Type v} [CommRing A] (f : K →+* A)
    (F : MvPolynomial (Fin (N + 1)) K) (d : ℕ) (hF : F.IsHomogeneous d)
    (v : Fin (N + 1) → A) (a : A) :
    eval₂Hom f (fun j => a * v j) F = a ^ d * eval₂Hom f v F := by
  have h := AffineChartDomain.eval₂_block_scale (projectiveSpace K N) f
    (rename (ClosureScheme.singleVariableEquiv (K := K) N).symm F) (fun _ => d)
    ((MultiProjectiveSpace.projective_homogeneous_iff N _ d).mpr hF.rename_isHomogeneous)
    (fun j => v j.2) (fun _ => a)
  simpa [coe_eval₂Hom, eval₂_rename, ClosureScheme.singleVariableEquiv,
    projectiveSpace, Function.comp_def] using h

theorem mem_homogeneousIdeal_iff_eval_eq_zero
    (x : Proj (homogeneousSubmodule (Fin (N + 1)) K)) (i : Fin (N + 1))
    (c : Fin (N + 1) → K) (hi : x ∈ Proj.basicOpen _ (MvPolynomial.X i))
    (hc : ∀ j, x ∉ Proj.basicOpen _ (MvPolynomial.X j - C (c j) * MvPolynomial.X i))
    (F : MvPolynomial (Fin (N + 1)) K) (d : ℕ) (hF : F.IsHomogeneous d) :
    F ∈ x.asHomogeneousIdeal ↔ MvPolynomial.eval c F = 0 := by
  let I := x.asHomogeneousIdeal.toIdeal
  let q := Ideal.Quotient.mk I
  let f : K →+* (MvPolynomial (Fin (N + 1)) K ⧸ I) := q.comp C
  have hq (j : Fin (N + 1)) : q (MvPolynomial.X j) = q (MvPolynomial.X i) * f (c j) := by
    have hz : q (MvPolynomial.X j - C (c j) * MvPolynomial.X i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (not_not.mp (hc j))
    rw [map_sub, map_mul, sub_eq_zero] at hz
    exact hz.trans (mul_comm _ _)
  have hmap : q = eval₂Hom f (fun j => q (MvPolynomial.X i) * f (c j)) := by
    apply MvPolynomial.ringHom_ext
    · intro k
      simp [f]
    · intro j
      simpa only [eval₂Hom_X'] using hq j
  have he : q F = q (MvPolynomial.X i) ^ d * f (MvPolynomial.eval c F) := by
    conv_lhs => rw [hmap]
    rw [eval₂_homogeneous_scale f F d hF]
    congr 1
    simpa only [MvPolynomial.eval, map_eval₂Hom, RingHom.comp_id] using
      (map_eval₂Hom f (RingHom.id K) c F).symm
  have hn : q (MvPolynomial.X i) ≠ 0 := fun hz =>
    hi (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  change F ∈ I ↔ _
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change q F = 0 ↔ _
  rw [he, mul_eq_zero]
  simp only [pow_ne_zero d hn, false_or, map_eq_zero_iff f f.injective]

theorem point_ext_linear_relations
    {x y : Proj (homogeneousSubmodule (Fin (N + 1)) K)}
    (i : Fin (N + 1)) (c : Fin (N + 1) → K)
    (hx : x ∈ Proj.basicOpen _ (MvPolynomial.X i))
    (hy : y ∈ Proj.basicOpen _ (MvPolynomial.X i))
    (hxc : ∀ j, x ∉ Proj.basicOpen _ (MvPolynomial.X j - C (c j) * MvPolynomial.X i))
    (hyc : ∀ j, y ∉ Proj.basicOpen _ (MvPolynomial.X j - C (c j) * MvPolynomial.X i)) : x = y := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro d F hF
  exact (mem_homogeneousIdeal_iff_eval_eq_zero x i c hx hxc F d hF).trans
    (mem_homogeneousIdeal_iff_eval_eq_zero y i c hy hyc F d hF).symm

end PhilipponMultiplicity.ProjectivePointComparison

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProductPresentationPoints

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ProductHyperplanes
open AlgebraicGeometry CategoryTheory MvPolynomial
open Scheme.Modules.GlueOfCocycle Hilbert.SegreVeronese Hilbert.SegreVeronese.Positive
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type u} [Field K] {X : Scheme.{u}} (M : MultiProjectiveSpace K)

theorem eval_normalized (p : M.Point) (a : Pivot M.ambientDimension)
    (D : M.FactorIndex → ℕ) (P : M.CoordinateRing) (hP : M.IsHomogeneous P D) :
    MvPolynomial.eval (fun v : M.Variable =>
      (p v.1).rep v.2 / (p v.1).rep (a v.1).down) P =
        (∏ i, (p i).rep (a i).down ^ D i)⁻¹ * M.eval P p := by
  have h := AffineChartDomain.eval₂_block_scale M (RingHom.id K) P D hP
    (M.coordinate p) (fun i => ((p i).rep (a i).down)⁻¹)
  simpa only [MvPolynomial.eval, MultiProjectiveSpace.eval, MultiProjectiveSpace.coordinate,
    ← inv_pow, ← Finset.prod_inv_distrib, div_eq_mul_inv, mul_comm] using h

variable (π : X ⟶ Spec (.of K))
    (φ : ∀ i : M.FactorIndex, X ⟶ Proj (homogeneousSubmodule (Fin (M.ambientDimension i + 1)) K))
    (hφ : ∀ i, φ i ≫ ProjSpace.π K (M.ambientDimension i) = π)
    (D : M.FactorIndex → ℕ) {r : ℕ}
    (c : Module.Basis (projectiveSpace K r).Variable K
      (Hilbert.degreePiece K M.factorCount M.ambientDimension D))

include hφ in

theorem basisPresentation_point_eq
    (𝔓 : (twist M.ambientDimension φ D).ProjPresentation π r)
    (h𝔓 : 𝔓.σ = basisSection M π φ D c)
    (hchart : ∀ a : Pivot M.ambientDimension, ∃ j : Fin (r + 1),
      c ⟨(0 : Fin 1), j⟩ = pivotForm M D (fun i => (a i).down) ∧
        chart M.ambientDimension φ a ≤ ProjSpace.pullbackChart 𝔓.toProj j)
    (x : X) (p : M.Point)
    (hp : ∀ i, φ i x = ProjectivePointComparison.ambientPoint (M.ambientDimension i) (fun _ => p i))
    (y : Proj (homogeneousSubmodule (Fin (r + 1)) K))
    (hy : ∀ (F : MvPolynomial (Fin (r + 1)) K) (d : ℕ), F.IsHomogeneous d → 0 < d →
      (y ∈ Proj.basicOpen _ F ↔ M.eval
        (substitution M D c (rename (ClosureScheme.singleVariableEquiv (K := K) r).symm F)) p ≠ 0)) :
    𝔓.toProj x = y := by
  classical
  choose a ha using fun i => Function.ne_iff.mp (p i).rep_nonzero
  let a' : Pivot M.ambientDimension := fun i => ⟨a i⟩
  let U := chart M.ambientDimension φ a'
  have hx : x ∈ U := point_mem_chart M φ x p hp a' ha
  obtain ⟨j₀, hj₀, hU⟩ := hchart a'
  let s : K := ∏ i, (p i).rep (a i) ^ D i
  have hs : s ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (ha i)
  let v : Fin (r + 1) → K := fun j => M.eval (c ⟨(0 : Fin 1), j⟩).val p
  have hv : v j₀ = s := by
    simp only [v, hj₀, pivotForm, pivotProduct, MultiProjectiveSpace.eval,
      map_prod, map_pow, eval_X, MultiProjectiveSpace.coordinate]
    rfl
  let k : Fin (r + 1) → K := fun j => s⁻¹ * v j
  have hyeval (j : Fin (r + 1)) :
      M.eval (substitution M D c (rename (ClosureScheme.singleVariableEquiv (K := K) r).symm
        (MvPolynomial.X j))) p = v j := by
    simp [substitution, ClosureScheme.singleVariableEquiv, v]
  apply ProjectivePointComparison.point_ext_linear_relations j₀ k (hU hx)
  · rw [hy _ 1 (isHomogeneous_X K _) (by decide), hyeval, hv]
    exact hs
  · intro j
    have hratio := congrArg (fun s => X.evaluation U x hx s)
      (basisPresentation_ratio M π φ D c 𝔓 h𝔓 a' j₀ hj₀ hU j)
    rw [evaluation_evalOnChart M π φ hφ x p hp a' U le_rfl hx ha,
      eval_normalized M p a' D _ ((M.degreePiece_iff _ _).mp (c ⟨(0 : Fin 1), j⟩).property)] at hratio
    change X.evaluation U x hx (rO hU (ProjSpace.frameUnit 𝔓.toProj j₀ j)) = residueScalar π x (k j) at hratio
    rw [evaluation_restrict] at hratio
    have hconst := evaluation_scalar (𝔓.toProj ≫ ProjSpace.π K r)
      (ProjSpace.pullbackChart 𝔓.toProj j₀) x (hU hx) (k j)
    rw [𝔓.toProj_π] at hconst
    have hz : X.evaluation (ProjSpace.pullbackChart 𝔓.toProj j₀) x (hU hx)
        (ProjSpace.frameUnit 𝔓.toProj j₀ j -
          (Scheme.TwoAffineOpenCover.algebraOfHom (𝔓.toProj ≫ ProjSpace.π K r)
            (ProjSpace.pullbackChart 𝔓.toProj j₀)).algebraMap (k j)) = 0 := by
      rw [map_sub, hratio, 𝔓.toProj_π, hconst, sub_self]
    rw [Scheme.evaluation_eq_zero_iff_notMem_basicOpen,
      ProjectiveSections.basicOpen_frameUnit_difference] at hz
    exact fun hj => hz ⟨hU hx, hj⟩
  · intro j
    rw [hy _ 1 ((isHomogeneous_X K _).sub ((isHomogeneous_X K _).C_mul _)) (by decide)]
    simp only [map_sub, map_mul, rename_C]
    have hC : substitution M D c (C (k j)) = C (k j) := (substitution M D c).commutes _
    rw [hC]
    change ¬ MvPolynomial.eval (M.coordinate p) _ ≠ 0
    rw [map_sub, map_mul, eval_C]
    change ¬ (M.eval _ p - k j * M.eval _ p ≠ 0)
    rw [hyeval, hyeval, hv]
    dsimp only [k]
    field_simp
    simp

end PhilipponMultiplicity.ProductHyperplanes
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponVeroneseLocusSurjectivity

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.Hilbert.SegreVeronese.Positive
open MvPolynomial
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (D : M.FactorIndex → ℕ) (hD : ∀ i, 1 ≤ D i) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (degreePiece K M.factorCount M.ambientDimension D))

include hD in

theorem exists_pivotForm_nonzero
    (I : Ideal M.CoordinateRing) (p : (projectiveSpace K N).Point)
    (hp : p ∈ (projectiveSpace K N).zeroLocus (diagonalIdeal M D b I)) :
    ∃ a, (projectiveSpace K N).eval (linearForm M D b (pivotForm M D a)).val p ≠ 0 := by
  classical
  by_contra! hz
  let ev := (aeval ((projectiveSpace K N).coordinate p) :
    (projectiveSpace K N).CoordinateRing →ₐ[K] K).toLinearMap.comp
    ((homogeneousSubmodule (projectiveSpace K N).Variable K 1).subtype.comp (linearForm M D b))
  have hmon (e : M.Variable →₀ ℕ)
      (he : Finsupp.weight (blockWeight M.factorCount M.ambientDimension) e = D) :
      ev ⟨monomial e 1, isWeightedHomogeneous_monomial _ _ _ he⟩ = 0 := by
    obtain ⟨a, Q, hQ, hdiv⟩ := exists_pivot_divisor M D hD e he
    let m := ∑ i, D i
    have hQ' : Q ∈ (degreePiece K 1 (fun _ => N) (fun _ => m - 1)).map
        (substitution M D b).toLinearMap := by
      rw [substitution_degreePiece]
      exact hQ
    obtain ⟨R, _, hR⟩ := hQ'
    let F : degreePiece K M.factorCount M.ambientDimension D :=
      ⟨monomial e 1, isWeightedHomogeneous_monomial _ _ _ he⟩
    have hrel : (linearForm M D b F).val ^ m -
        (linearForm M D b (pivotForm M D a)).val * R ∈ diagonalIdeal M D b I := by
      change substitution M D b _ ∈ I
      rw [map_sub, map_pow, map_mul, substitution_linearForm, substitution_linearForm]
      change (monomial e (1 : K)) ^ m - pivotProduct M D a * substitution M D b R ∈ I
      rw [show substitution M D b R = Q from hR, hdiv, sub_self]
      exact I.zero_mem
    have hv := hp _ hrel
    change (projectiveSpace K N).eval
      ((linearForm M D b F).val ^ m - (linearForm M D b (pivotForm M D a)).val * R) p = 0 at hv
    simp only [MultiProjectiveSpace.eval, map_sub, map_pow, map_mul] at hv
    have hz' := hz a
    change eval ((projectiveSpace K N).coordinate p)
      (linearForm M D b (pivotForm M D a)).val = 0 at hz'
    rw [hz', zero_mul, sub_zero] at hv
    change eval ((projectiveSpace K N).coordinate p) (linearForm M D b F).val = 0
    exact eq_zero_of_pow_eq_zero hv
  have hall (P : degreePiece K M.factorCount M.ambientDimension D) : ev P = 0 := by
    rcases P with ⟨P, hP⟩
    refine IsWeightedHomogeneous.induction_on
      (motive := fun Q hQ => ev ⟨Q, hQ⟩ = 0) ?_ ?_ ?_ hP
    · exact map_zero ev
    · intro F H hF hH heF heH
      change ev (⟨F, hF⟩ + ⟨H, hH⟩) = 0
      rw [map_add, heF, heH, zero_add]
    · intro e c he
      have hs : (⟨monomial e c, isWeightedHomogeneous_monomial _ _ _ he⟩ :
          degreePiece K M.factorCount M.ambientDimension D) =
          c • ⟨monomial e 1, isWeightedHomogeneous_monomial _ _ _ he⟩ := by
        apply Subtype.ext
        simp [smul_monomial]
      rw [hs, map_smul, hmon e he, smul_zero]
  have hcoords (j : (projectiveSpace K N).Variable) :
      (projectiveSpace K N).coordinate p j = 0 := by
    have h := hall (b j)
    change aeval ((projectiveSpace K N).coordinate p) (linearForm M D b (b j)).val = 0 at h
    simpa only [linearForm_basis, aeval_X] using h
  exact (p (0 : Fin 1)).rep_nonzero (funext (fun j => hcoords ⟨(0 : Fin 1), j⟩))

include hD in
theorem pointMap_surjective_on_locus
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (p : (projectiveSpace K N).Point)
    (hp : p ∈ (projectiveSpace K N).zeroLocus (diagonalIdeal M D b I)) :
    ∃ q ∈ M.zeroLocus I, pointMap M D b q = p := by
  obtain ⟨a, ha⟩ := exists_pivotForm_nonzero M D hD b I p hp
  obtain ⟨q, hq, he, _⟩ := exists_inverse_on_pivot M D hD b I hI p hp a ha
  exact ⟨q, hq, he⟩

end PhilipponMultiplicity.Hilbert.SegreVeronese.Positive

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponVeroneseLocusEquivalence

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option synthInstance.maxHeartbeats 1500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.Hilbert.SegreVeronese.Positive
open MvPolynomial
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K) (D : M.FactorIndex → ℕ) (hD : ∀ i, 1 ≤ D i) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (degreePiece K M.factorCount M.ambientDimension D))
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)

def locusMap : M.zeroLocus I →
    (projectiveSpace K N).zeroLocus (diagonalIdeal M D b I) :=
  fun x => ⟨pointMap M D b x.val,
    pointMap_mem_diagonal_zeroLocus M D b hD I hI x.val x.property⟩

theorem locusMap_bijective : Function.Bijective (locusMap M D hD b I hI) := by
  constructor
  · intro x y h
    apply Subtype.ext
    exact pointMap_injective M D b hD (congrArg Subtype.val h)
  · intro y
    obtain ⟨x, hx, he⟩ := pointMap_surjective_on_locus M D hD b I hI y.val y.property
    exact ⟨⟨x, hx⟩, Subtype.ext he⟩

def locusEquiv : M.zeroLocus I ≃
    (projectiveSpace K N).zeroLocus (diagonalIdeal M D b I) :=
  Equiv.ofBijective (locusMap M D hD b I hI) (locusMap_bijective M D hD b I hI)

theorem locusEquiv_regular : M.IsRegularAlong (projectiveSpace K N)
    Subtype.val (fun x => (locusEquiv M D hD b I hI x).val) :=
  (pointMap_regular M D b).comp_domain Subtype.val

theorem locusEquiv_inverse_regular : (projectiveSpace K N).IsRegularAlong M
    Subtype.val (fun x => ((locusEquiv M D hD b I hI).symm x).val) := by
  intro x i
  obtain ⟨a, ha⟩ := exists_pivotForm_nonzero M D hD b I x.val x.property
  let S := (linearForm M D b (pivotForm M D a)).val
  have hS : (projectiveSpace K N).IsHomogeneous S (fun _ => 1) :=
    (MultiProjectiveSpace.projective_homogeneous_iff N S 1).mpr
      (linearForm M D b (pivotForm M D a)).property
  refine ⟨{p | (projectiveSpace K N).eval S p ≠ 0},
    (projectiveSpace K N).isOpen_basic S (fun _ => 1) hS, ha, fun _ => 1,
    fun j => (linearForm M D b (replacementForm M D hD a ⟨i, j⟩)).val,
    ?_, ?_⟩
  · intro j
    exact (MultiProjectiveSpace.projective_homogeneous_iff N _ 1).mpr
      (linearForm M D b (replacementForm M D hD a ⟨i, j⟩)).property
  · intro y hy
    obtain ⟨q, hq, he, hlift⟩ := exists_inverse_on_pivot M D hD b I hI y.val y.property a hy
    have heq : locusEquiv M D hD b I hI ⟨q, hq⟩ = y := Subtype.ext he
    have hq' : (⟨q, hq⟩ : M.zeroLocus I) = (locusEquiv M D hD b I hI).symm y := by
      rw [← heq, Equiv.symm_apply_apply]
    have hval : q = ((locusEquiv M D hD b I hI).symm y).val := congrArg Subtype.val hq'
    obtain ⟨hn, hpoint⟩ := hlift i
    exact ⟨hn, hpoint.trans (congrFun hval i)⟩

end PhilipponMultiplicity.Hilbert.SegreVeronese.Positive

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectiveRegularIso

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section

namespace PhilipponMultiplicity.ProjectivePointComparison
open MvPolynomial AlgebraicGeometry CategoryTheory
universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
    (M N : ℕ) (I : Ideal (projectiveSpace K M).CoordinateRing)
    (hI : IsMultihomogeneousIdeal (projectiveSpace K M) I) (hred : I.IsRadical)
    (J : Ideal (projectiveSpace K N).CoordinateRing)
    (hJ : IsMultihomogeneousIdeal (projectiveSpace K N) J)

include hred

theorem hom_ext_of_points (F H : scheme M I hI ⟶ scheme N J hJ)
    (hF : F ≫ ProjectiveCoordinateScheme.structureMap J (ordinaryHomogeneous N J hJ) =
      ProjectiveCoordinateScheme.structureMap I (ordinaryHomogeneous M I hI))
    (hH : H ≫ ProjectiveCoordinateScheme.structureMap J (ordinaryHomogeneous N J hJ) =
      ProjectiveCoordinateScheme.structureMap I (ordinaryHomogeneous M I hI))
    (hp : ∀ x, F (point M I hI x) = H (point M I hI x)) : F = H := by
  let πX := ProjectiveCoordinateScheme.structureMap I (ordinaryHomogeneous M I hI)
  let πY := ProjectiveCoordinateScheme.structureMap J (ordinaryHomogeneous N J hJ)
  letI : IsProper πX := ProjectiveCoordinateScheme.structureMap_isProper I _
  letI : IsProper πY := ProjectiveCoordinateScheme.structureMap_isProper J _
  letI : IsReduced (scheme M I hI) :=
    ProjectiveCoordinateScheme.scheme_isReduced I (ordinaryHomogeneous M I hI) hred
  letI : LocallyOfFiniteType (F ≫ πY) := by
    rw [hF]
    exact inferInstanceAs (LocallyOfFiniteType πX)
  apply AlgebraicGeometry.ext_of_apply_eq πY Set.univ isOpen_univ.isLocallyClosed dense_univ
  · intro a _ ha
    obtain ⟨x, rfl⟩ := closed_points_surjective M I hI a ha
    exact hp x
  · exact hF.trans hH.symm

theorem exists_regular_schemeIso (hredJ : J.IsRadical)
    (e : (projectiveSpace K M).zeroLocus I ≃ (projectiveSpace K N).zeroLocus J)
    (he : (projectiveSpace K M).IsRegularAlong (projectiveSpace K N)
      Subtype.val (fun x => (e x).val))
    (hei : (projectiveSpace K N).IsRegularAlong (projectiveSpace K M)
      Subtype.val (fun y => (e.symm y).val)) :
    ∃ F : scheme M I hI ≅ scheme N J hJ,
      F.hom ≫ ProjectiveCoordinateScheme.structureMap J (ordinaryHomogeneous N J hJ) =
        ProjectiveCoordinateScheme.structureMap I (ordinaryHomogeneous M I hI) ∧
      ∀ x, F.hom (point M I hI x) = point N J hJ (e x) := by
  obtain ⟨F, ⟨hF, hpF⟩, _⟩ := existsUnique_regular_schemeMap M N I hI hred J hJ e he
  obtain ⟨H, ⟨hH, hpH⟩, _⟩ := existsUnique_regular_schemeMap N M J hJ hredJ I hI e.symm hei
  have hFH : F ≫ H = 𝟙 _ := by
    apply hom_ext_of_points M M I hI hred I hI
    · rw [Category.assoc, hH, hF]
    · exact Category.id_comp _
    · intro x
      change H (F (point M I hI x)) = point M I hI x
      rw [hpF, hpH, e.symm_apply_apply]
  have hHF : H ≫ F = 𝟙 _ := by
    apply hom_ext_of_points N N J hJ hredJ J hJ
    · rw [Category.assoc, hF, hH]
    · exact Category.id_comp _
    · intro y
      change F (H (point N J hJ y)) = point N J hJ y
      rw [hpH, hpF, e.apply_symm_apply]
  exact ⟨⟨F, H, hFH, hHF⟩, hF, hpF⟩

end PhilipponMultiplicity.ProjectivePointComparison

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponVeroneseSchemeComparison

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option synthInstance.maxHeartbeats 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.Hilbert.SegreVeronese.Positive
open MvPolynomial AlgebraicGeometry CategoryTheory
universe u
variable {K : Type u} [Field K] (M : MultiProjectiveSpace K)
    (D : M.FactorIndex → ℕ) (hD : ∀ i, 1 ≤ D i) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (degreePiece K M.factorCount M.ambientDimension D))
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)

def schemePoint (x : M.zeroLocus I) : scheme M D b I hI hD :=
  ProjectivePointComparison.point N (diagonalIdeal M D b I)
    (diagonalIdeal_homogeneous M D b hD I hI) (locusEquiv M D hD b I hI x)

theorem exists_changeDegreeIso [IsAlgClosed K] (hred : I.IsRadical)
    (E : M.FactorIndex → ℕ) (hE : ∀ i, 1 ≤ E i) {N' : ℕ}
    (c : Module.Basis (projectiveSpace K N').Variable K
      (degreePiece K M.factorCount M.ambientDimension E)) :
    ∃ F : scheme M D b I hI hD ≅ scheme M E c I hI hE,
      F.hom ≫ structureMap M E c I hI hE = structureMap M D b I hI hD ∧
      ∀ x, F.hom (schemePoint M D hD b I hI x) = schemePoint M E hE c I hI x := by
  let eD := locusEquiv M D hD b I hI
  let eE := locusEquiv M E hE c I hI
  let e := eD.symm.trans eE
  have he : (projectiveSpace K N).IsRegularAlong (projectiveSpace K N')
      Subtype.val (fun x => (e x).val) :=
    (locusEquiv_inverse_regular M D hD b I hI).comp
      ((locusEquiv_regular M E hE c I hI).comp_domain eD.symm)
  have hei : (projectiveSpace K N').IsRegularAlong (projectiveSpace K N)
      Subtype.val (fun x => (e.symm x).val) :=
    (locusEquiv_inverse_regular M E hE c I hI).comp
      ((locusEquiv_regular M D hD b I hI).comp_domain eE.symm)
  obtain ⟨F, hF, hpoint⟩ := ProjectivePointComparison.exists_regular_schemeIso N N'
    (diagonalIdeal M D b I) (diagonalIdeal_homogeneous M D b hD I hI)
    (hred.comap (substitution M D b).toRingHom)
    (diagonalIdeal M E c I) (diagonalIdeal_homogeneous M E c hE I hI)
    (hred.comap (substitution M E c).toRingHom) e he hei
  refine ⟨F, hF, ?_⟩
  intro x
  have h := hpoint (eD x)
  simp only [e, Equiv.trans_apply, Equiv.symm_apply_apply] at h
  exact h

end PhilipponMultiplicity.Hilbert.SegreVeronese.Positive

namespace PhilipponMultiplicity.ClosureScheme
open MvPolynomial AlgebraicGeometry CategoryTheory Hilbert.SegreVeronese
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] (G : EmbeddedGroupProduct K) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension (fun _ => 1)))

theorem exists_veroneseIso (D : G.FactorIndex → ℕ) (hD : ∀ i, 1 ≤ D i) {r : ℕ}
    (c : Module.Basis (projectiveSpace K r).Variable K
      (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension D)) :
    ∃ F : scheme G b ≅ Hilbert.SegreVeronese.scheme G.ambient D c (ideal G) (ideal_homogeneous G) hD,
      F.hom ≫ Hilbert.SegreVeronese.structureMap G.ambient D c (ideal G) (ideal_homogeneous G) hD =
        structureMap G b ∧
      ∀ x, F.hom (point G b x) =
        Positive.schemePoint G.ambient D hD c (ideal G) (ideal_homogeneous G) (locusEquiv G x) := by
  obtain ⟨F, hF, hpoint⟩ := Positive.exists_changeDegreeIso G.ambient (fun _ => 1)
    (fun _ => le_rfl) b (ideal G) (ideal_homogeneous G) (ideal_radical G) D hD c
  exact ⟨F, hF, fun x => hpoint (locusEquiv G x)⟩

end PhilipponMultiplicity.ClosureScheme

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponClosureEmbeddingSupport

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ClosureScheme
open AlgebraicGeometry CategoryTheory MvPolynomial ProjectiveCoordinateScheme
open Hilbert.SegreVeronese
universe u
variable {K : Type u} [Field K] (G : EmbeddedGroupProduct K) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension (fun _ => 1)))
attribute [local instance] MvPolynomial.gradedAlgebra

theorem closedSubscheme_preimage_eq_bot_iff (V : Set (groupProjectiveClosure G))
    (U : (scheme G b).Opens) :
    closedSubschemeι G b V ⁻¹ᵁ U = ⊥ ↔ ∀ x ∈ V, point G b x ∉ U := by
  have hrange : Set.range (closedSubschemeι G b V) =
      closure (point G b '' V) :=
    (Scheme.IdealSheafData.range_subschemeι
      (Scheme.IdealSheafData.vanishingIdeal (closedLocus G b V))).trans
        (Scheme.IdealSheafData.coe_support_vanishingIdeal _)
  constructor
  · intro h x hx hxU
    have hxrange : point G b x ∈ Set.range (closedSubschemeι G b V) := by
      rw [hrange]
      exact subset_closure ⟨x, hx, rfl⟩
    obtain ⟨y, hy⟩ := hxrange
    have hyU : y ∈ closedSubschemeι G b V ⁻¹ᵁ U := by
      change closedSubschemeι G b V y ∈ U
      rwa [hy]
    rw [h] at hyU
    exact hyU
  · intro h
    have hclosure : closure (point G b '' V) ⊆ (U : Set (scheme G b))ᶜ :=
      closure_minimal (by rintro _ ⟨x, hx, rfl⟩; exact h x hx) U.isOpen.isClosed_compl
    apply le_bot_iff.mp
    intro y hy
    exact hclosure (hrange ▸ Set.mem_range_self y) hy

end PhilipponMultiplicity.ClosureScheme

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponClosureVeroneseEmbedding

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option synthInstance.maxHeartbeats 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section

namespace PhilipponMultiplicity.ProjectivePointComparison
open AlgebraicGeometry CategoryTheory MvPolynomial ProjectiveCoordinateScheme
universe u
variable {K : Type u} [Field K] (N : ℕ)
    (I : Ideal (projectiveSpace K N).CoordinateRing)
    (hI : IsMultihomogeneousIdeal (projectiveSpace K N) I)
attribute [local instance] MvPolynomial.gradedAlgebra

theorem ambientMap_isClosedImmersion : IsClosedImmersion (ambientMap N I hI) := by
  letI := quotientMap_isClosedImmersion I (ordinaryHomogeneous N I hI)
  unfold ambientMap
  infer_instance

theorem ambientMap_point_mem_basicOpen (x : (projectiveSpace K N).zeroLocus I)
    (F : MvPolynomial (Fin (N + 1)) K) (d : ℕ) (hF : F.IsHomogeneous d) (hd : 0 < d) :
    ambientMap N I hI (point N I hI x) ∈ Proj.basicOpen _ F ↔
      (projectiveSpace K N).eval
        (rename (ClosureScheme.singleVariableEquiv (K := K) N).symm F) x.val ≠ 0 := by
  change point N I hI x ∈ polynomialOpen I (ordinaryHomogeneous N I hI)
    (rename (ClosureScheme.singleVariableEquiv (K := K) N).symm F) ↔ _
  exact point_mem_polynomialOpen N I hI x _ d hF.rename_isHomogeneous hd

end PhilipponMultiplicity.ProjectivePointComparison

namespace PhilipponMultiplicity.ClosureScheme
open AlgebraicGeometry CategoryTheory MvPolynomial ProjectiveCoordinateScheme Hilbert.SegreVeronese
universe u
variable {K : Type u} [Field K] (G : EmbeddedGroupProduct K) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension (fun _ => 1)))
    (D : G.FactorIndex → ℕ) (hD : ∀ i, 1 ≤ D i) {r : ℕ}
    (c : Module.Basis (projectiveSpace K r).Variable K
      (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension D))
attribute [local instance] MvPolynomial.gradedAlgebra

def veronesePolynomial : MvPolynomial (Fin (r + 1)) K →ₐ[K] G.ambient.CoordinateRing :=
  (substitution G.ambient D c).comp (rename (singleVariableEquiv (K := K) r).symm)

theorem veronesePolynomial_homogeneous (F : MvPolynomial (Fin (r + 1)) K)
    (d : ℕ) (hF : F.IsHomogeneous d) :
    G.ambient.IsHomogeneous (veronesePolynomial G D c F) (fun i => d * D i) := by
  apply (G.ambient.degreePiece_iff _ _).mp
  exact substitution_homogeneous G.ambient D c d _ hF.rename_isHomogeneous

variable [IsAlgClosed K]

def veroneseIso : scheme G b ≅
    Hilbert.SegreVeronese.scheme G.ambient D c (ideal G) (ideal_homogeneous G) hD :=
  (exists_veroneseIso G b D hD c).choose

theorem veroneseIso_over : (veroneseIso G b D hD c).hom ≫
    Hilbert.SegreVeronese.structureMap G.ambient D c (ideal G) (ideal_homogeneous G) hD =
      structureMap G b := (exists_veroneseIso G b D hD c).choose_spec.1

theorem veroneseIso_point (x : groupProjectiveClosure G) :
    (veroneseIso G b D hD c).hom (point G b x) =
      Positive.schemePoint G.ambient D hD c (ideal G) (ideal_homogeneous G) (locusEquiv G x) :=
  (exists_veroneseIso G b D hD c).choose_spec.2 x

def veroneseEmbedding : scheme G b ⟶ Proj (homogeneousSubmodule (Fin (r + 1)) K) :=
  (veroneseIso G b D hD c).hom ≫
    ProjectivePointComparison.ambientMap r (diagonalIdeal G.ambient D c (ideal G))
      (diagonalIdeal_homogeneous G.ambient D c hD (ideal G) (ideal_homogeneous G))

theorem veroneseEmbedding_isClosedImmersion :
    IsClosedImmersion (veroneseEmbedding G b D hD c) := by
  letI := ProjectivePointComparison.ambientMap_isClosedImmersion r
    (diagonalIdeal G.ambient D c (ideal G))
    (diagonalIdeal_homogeneous G.ambient D c hD (ideal G) (ideal_homogeneous G))
  unfold veroneseEmbedding
  infer_instance

theorem veroneseEmbedding_over : veroneseEmbedding G b D hD c ≫ polynomialStructureMap =
    structureMap G b := by
  rw [veroneseEmbedding, Category.assoc, ProjectivePointComparison.ambientMap_over]
  exact veroneseIso_over G b D hD c

theorem veroneseEmbedding_point_mem_basicOpen (x : groupProjectiveClosure G)
    (F : MvPolynomial (Fin (r + 1)) K) (d : ℕ) (hF : F.IsHomogeneous d) (hd : 0 < d) :
    veroneseEmbedding G b D hD c (point G b x) ∈ Proj.basicOpen _ F ↔
      G.ambient.eval (veronesePolynomial G D c F) x.val ≠ 0 := by
  rw [veroneseEmbedding, Scheme.Hom.comp_apply, veroneseIso_point]
  exact (ProjectivePointComparison.ambientMap_point_mem_basicOpen r
    (diagonalIdeal G.ambient D c (ideal G))
    (diagonalIdeal_homogeneous G.ambient D c hD (ideal G) (ideal_homogeneous G))
    (Positive.locusEquiv G.ambient D hD c (ideal G) (ideal_homogeneous G) (locusEquiv G x))
    F d hF hd).trans
      (pointMap_eval_eq_zero_iff G.ambient D c x.val _ (fun _ => d)
        ((MultiProjectiveSpace.projective_homogeneous_iff r _ d).mpr hF.rename_isHomogeneous)).not

def closedSubschemeVeroneseEmbedding (V : Set (groupProjectiveClosure G)) :
    closedSubscheme G b V ⟶ Proj (homogeneousSubmodule (Fin (r + 1)) K) :=
  closedSubschemeι G b V ≫ veroneseEmbedding G b D hD c

theorem closedSubschemeVeroneseEmbedding_isClosedImmersion
    (V : Set (groupProjectiveClosure G)) :
    IsClosedImmersion (closedSubschemeVeroneseEmbedding G b D hD c V) := by
  letI := closedSubschemeι_isClosedImmersion G b V
  letI := veroneseEmbedding_isClosedImmersion G b D hD c
  unfold closedSubschemeVeroneseEmbedding
  infer_instance

theorem closedSubschemeVeroneseEmbedding_over (V : Set (groupProjectiveClosure G)) :
    closedSubschemeVeroneseEmbedding G b D hD c V ≫ polynomialStructureMap =
      closedSubschemeι G b V ≫ structureMap G b := by
  rw [closedSubschemeVeroneseEmbedding, Category.assoc, veroneseEmbedding_over]

theorem closedSubschemeVeroneseEmbedding_preimage_eq_bot_iff
    (V : Set (groupProjectiveClosure G)) (F : MvPolynomial (Fin (r + 1)) K)
    (d : ℕ) (hF : F.IsHomogeneous d) (hd : 0 < d) :
    closedSubschemeVeroneseEmbedding G b D hD c V ⁻¹ᵁ Proj.basicOpen _ F = ⊥ ↔
      veronesePolynomial G D c F ∈ G.ambient.vanishingIdeal (Subtype.val '' V) := by
  rw [closedSubschemeVeroneseEmbedding, Scheme.Hom.comp_preimage, closedSubscheme_preimage_eq_bot_iff]
  have he : (∀ x ∈ V, point G b x ∉ veroneseEmbedding G b D hD c ⁻¹ᵁ Proj.basicOpen _ F) ↔
      ∀ x ∈ V, G.ambient.eval (veronesePolynomial G D c F) x.val = 0 := by
    simp only [Scheme.Hom.mem_preimage, veroneseEmbedding_point_mem_basicOpen G b D hD c _ F d hF hd,
      not_not]
  rw [he]
  constructor
  · intro h
    apply Ideal.subset_span
    refine ⟨⟨fun i => d * D i, veronesePolynomial_homogeneous G D c F d hF⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  · intro h x hx
    exact G.ambient.eval_eq_zero_of_mem_vanishingIdeal h ⟨x, hx, rfl⟩

end PhilipponMultiplicity.ClosureScheme

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProductVeroneseComparison

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section

namespace PhilipponMultiplicity.ClosureScheme
open AlgebraicGeometry CategoryTheory MvPolynomial ProductHyperplanes ProjectiveTwistSheaf
open Hilbert.SegreVeronese.Positive
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type u} [Field K] [IsAlgClosed K] (G : EmbeddedGroupProduct K) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension (fun _ => 1)))
    (D : G.FactorIndex → ℕ) (hD : ∀ i, 1 ≤ D i) {r : ℕ}
    (c : Module.Basis (projectiveSpace K r).Variable K
      (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension D))

theorem productPresentation_toProj_eq {X : Scheme.{u}} [IsReduced X]
    (f : X ⟶ scheme G b) [IsClosedImmersion f]
    (𝔓 : (twist G.ambient.ambientDimension (fun i => f ≫ factorMap G b i) D).ProjPresentation
      (f ≫ structureMap G b) r)
    (h𝔓 : 𝔓.σ = basisSection G.ambient (f ≫ structureMap G b)
      (fun i => f ≫ factorMap G b i) D c)
    (hchart : ∀ a : Pivot G.ambient.ambientDimension, ∃ j : Fin (r + 1),
      c ⟨(0 : Fin 1), j⟩ = pivotForm G.ambient D (fun i => (a i).down) ∧
        chart G.ambient.ambientDimension (fun i => f ≫ factorMap G b i) a ≤
          ProjSpace.pullbackChart 𝔓.toProj j) :
    𝔓.toProj = f ≫ veroneseEmbedding G b D hD c := by
  letI := G.ambient.zariskiTopology
  letI := isProper G b
  letI : LocallyOfFiniteType (𝔓.toProj ≫ ProjSpace.π K r) := by
    rw [𝔓.toProj_π]
    infer_instance
  apply AlgebraicGeometry.ext_of_apply_eq (ProjSpace.π K r) Set.univ
    isOpen_univ.isLocallyClosed dense_univ
  · intro x _ hx
    have hfx : IsClosed {f x} := by
      rw [← Set.image_singleton]
      exact f.isClosedEmbedding.isClosedMap _ hx
    obtain ⟨p, hp⟩ := (closedPointHomeomorph G b).surjective ⟨f x, hfx⟩
    have hp' : point G b p = f x := congrArg Subtype.val hp
    apply basisPresentation_point_eq G.ambient (f ≫ structureMap G b)
      (fun i => f ≫ factorMap G b i)
      (fun i => by rw [Category.assoc, factorMap_over]) D c 𝔓 h𝔓 hchart x p.val
    · intro i
      rw [Scheme.Hom.comp_apply, ← hp', factorMap_point]
    · intro F d hF hd
      rw [Scheme.Hom.comp_apply, ← hp']
      exact veroneseEmbedding_point_mem_basicOpen G b D hD c p F d hF hd
  · have hover : veroneseEmbedding G b D hD c ≫ ProjSpace.π K r = structureMap G b :=
      veroneseEmbedding_over G b D hD c
    rw [𝔓.toProj_π, Category.assoc, hover]

theorem productTwist_veronese_iso {X : Scheme.{u}} [IsReduced X]
    (f : X ⟶ scheme G b) [IsClosedImmersion f]
    (hc : ∀ a : ∀ i : G.FactorIndex, Fin (G.ambient.ambientDimension i + 1),
      ∃ j, c j = pivotForm G.ambient D a) :
    Nonempty (twist G.ambient.ambientDimension (fun i => f ≫ factorMap G b i) D ≅
      twistSheaf (f ≫ veroneseEmbedding G b D hD c) 1) := by
  obtain ⟨𝔓, h𝔓, hchart⟩ := exists_basisPresentation G.ambient (f ≫ structureMap G b)
    (fun i => f ≫ factorMap G b i) D c hc
  let 𝔔 : (twistSheaf (f ≫ veroneseEmbedding G b D hD c) 1).ProjPresentation
      (f ≫ structureMap G b) r :=
    { presentation (f ≫ veroneseEmbedding G b D hD c) with
      toProj_π := by
        change (f ≫ veroneseEmbedding G b D hD c) ≫ ProjSpace.π K r = _
        exact (Category.assoc _ _ _).trans
          (congrArg (fun h => f ≫ h) (veroneseEmbedding_over G b D hD c)) }
  exact 𝔓.nonempty_iso_of_toProj_eq 𝔔
    (productPresentation_toProj_eq G b D hD c f 𝔓 h𝔓 hchart)

end PhilipponMultiplicity.ClosureScheme
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponClosureHilbertPieces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ProjectiveCoordinateScheme
open MvPolynomial
variable {K : Type*} [Field K] {σ τ : Type*}

theorem rename_homogeneousSubmodule (e : σ ≃ τ) (d : ℕ) :
    (homogeneousSubmodule σ K d).map (MvPolynomial.rename e).toLinearMap =
      homogeneousSubmodule τ K d := by
  ext P
  constructor
  · rintro ⟨F, hF, rfl⟩
    exact hF.rename_isHomogeneous
  · intro hP
    refine ⟨MvPolynomial.rename e.symm P, hP.rename_isHomogeneous, ?_⟩
    simp [rename_rename]

end PhilipponMultiplicity.ProjectiveCoordinateScheme

namespace PhilipponMultiplicity.ClosureScheme
open AlgebraicGeometry CategoryTheory MvPolynomial ProjectiveCoordinateScheme
open Hilbert.SegreVeronese
universe u
variable {K : Type u} [Field K] (G : EmbeddedGroupProduct K) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension (fun _ => 1)))

end PhilipponMultiplicity.ClosureScheme

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponVeroneseHilbertPieces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ClosureScheme
open AlgebraicGeometry CategoryTheory MvPolynomial ProjectiveCoordinateScheme Hilbert.SegreVeronese
universe u
variable {K : Type u} [Field K] (G : EmbeddedGroupProduct K)
    (D : G.FactorIndex → ℕ) {r : ℕ}
    (c : Module.Basis (projectiveSpace K r).Variable K
      (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension D))

theorem veronesePolynomial_degreePiece (n : ℕ) :
    (homogeneousSubmodule (Fin (r + 1)) K n).map (veronesePolynomial G D c).toLinearMap =
      Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension (fun i => n * D i) := by
  change (homogeneousSubmodule (Fin (r + 1)) K n).map
    ((substitution G.ambient D c).toLinearMap.comp
      (MvPolynomial.rename (singleVariableEquiv (K := K) r).symm).toLinearMap) = _
  rw [Submodule.map_comp, rename_homogeneousSubmodule,
    ← Hilbert.ordinary_degreePiece_eq, substitution_degreePiece]

def veroneseQuotientMap (V : Set (groupProjectiveClosure G)) (n : ℕ) :
    homogeneousSubmodule (Fin (r + 1)) K n →ₗ[K]
      G.ambient.CoordinateRing ⧸ G.ambient.vanishingIdeal (Subtype.val '' V) :=
  ((Ideal.Quotient.mkₐ K (G.ambient.vanishingIdeal (Subtype.val '' V))).comp
    (veronesePolynomial G D c)).toLinearMap.domRestrict _

theorem veroneseQuotientMap_eq_zero_iff (V : Set (groupProjectiveClosure G)) (n : ℕ)
    (F : homogeneousSubmodule (Fin (r + 1)) K n) :
    veroneseQuotientMap G D c V n F = 0 ↔
      veronesePolynomial G D c F.val ∈ G.ambient.vanishingIdeal (Subtype.val '' V) :=
  Ideal.Quotient.eq_zero_iff_mem

theorem veroneseQuotientMap_range (V : Set (groupProjectiveClosure G)) (n : ℕ) :
    LinearMap.range (veroneseQuotientMap G D c V n) =
      Hilbert.quotientPiece K G.ambient.factorCount G.ambient.ambientDimension
        (G.ambient.vanishingIdeal (Subtype.val '' V)) (fun i => n * D i) := by
  rw [veroneseQuotientMap, LinearMap.range_domRestrict]
  change (homogeneousSubmodule (Fin (r + 1)) K n).map
    ((Ideal.Quotient.mkₐ K (G.ambient.vanishingIdeal (Subtype.val '' V))).toLinearMap.comp
      (veronesePolynomial G D c).toLinearMap) = _
  rw [Submodule.map_comp, veronesePolynomial_degreePiece]
  rfl

end PhilipponMultiplicity.ClosureScheme

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponVeroneseSectionHilbertComparison

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ClosureScheme
open AlgebraicGeometry CategoryTheory MvPolynomial ProjectiveSections
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] (G : EmbeddedGroupProduct K) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension (fun _ => 1)))
    (D : G.FactorIndex → ℕ) (hD : ∀ i, 1 ≤ D i) {r : ℕ}
    (c : Module.Basis (projectiveSpace K r).Variable K
      (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension D))
    (V : Set (groupProjectiveClosure G))
attribute [local instance] MvPolynomial.gradedAlgebra

theorem veronesePolynomialSectionMap_kernel (n : ℕ) (hn : 0 < n) :
    LinearMap.ker (polynomialSectionMap (closedSubschemeVeroneseEmbedding G b D hD c V) n) =
      LinearMap.ker (veroneseQuotientMap G D c V n) := by
  letI := closedSubscheme_isReduced G b V
  ext F
  rw [LinearMap.mem_ker, LinearMap.mem_ker, polynomialSectionMap_eq_zero_iff_preimage,
    closedSubschemeVeroneseEmbedding_preimage_eq_bot_iff G b D hD c V F.val n F.property hn,
    veroneseQuotientMap_eq_zero_iff]

theorem eventually_veronese_quotientPiece_sections_equiv :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      Nonempty (Hilbert.quotientPiece K G.ambient.factorCount G.ambient.ambientDimension
          (G.ambient.vanishingIdeal (Subtype.val '' V)) (fun i => n * D i) ≃ₗ[K]
        ProjSpace.twistObj
          (closedSubschemeVeroneseEmbedding G b D hD c V ≫ ProjSpace.π K r)
          (closedSubschemeVeroneseEmbedding G b D hD c V) n ⊤) := by
  let φ := closedSubschemeVeroneseEmbedding G b D hD c V
  letI := closedSubschemeVeroneseEmbedding_isClosedImmersion G b D hD c V
  obtain ⟨n₀, hn₀⟩ := polynomialSectionMap_eventually_surjective φ
  refine ⟨max n₀ 1, fun n hn => ?_⟩
  have hpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ _) hn)
  have hsurj := hn₀ n (le_trans (le_max_left _ _) hn)
  let e := (veroneseQuotientMap G D c V n).quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ (veronesePolynomialSectionMap_kernel G b D hD c V n hpos).symm).trans
      ((polynomialSectionMap φ n).quotKerEquivOfSurjective hsurj))
  rw [veroneseQuotientMap_range G D c V n] at e
  exact ⟨e⟩

theorem eventually_veronese_sections_finrank_eq_hilbertFunction :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      Module.finrank K (ProjSpace.twistObj
        (closedSubschemeVeroneseEmbedding G b D hD c V ≫ ProjSpace.π K r)
        (closedSubschemeVeroneseEmbedding G b D hD c V) n ⊤) =
      Hilbert.hilbertFunction K G.ambient.factorCount G.ambient.ambientDimension
        (G.ambient.vanishingIdeal (Subtype.val '' V)) (fun i => n * D i) := by
  obtain ⟨n₀, hn₀⟩ := eventually_veronese_quotientPiece_sections_equiv G b D hD c V
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨e⟩ := hn₀ n hn
  exact e.finrank_eq.symm

end PhilipponMultiplicity.ClosureScheme
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponLocalSectionEquivalence

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.SchemeSections
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
variable {X : Scheme.{u}} (M N : X.Modules)

theorem bijective_of_cover {ι : Type*} (W : ι → X.Opens) (hW : iSup W = ⊤)
    (e : ∀ U : X.Opens, Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U))
    (hnat : ∀ (U U' : X.Opens) (h : U ≤ U') (s : Γ(M, U')),
      e U (M.presheaf.map (homOfLE h).op s) =
        N.presheaf.map (homOfLE h).op (e U' s))
    (hloc : ∀ i (U : X.Opens), U ≤ W i → Function.Bijective (e U)) :
    ∀ U : X.Opens, Function.Bijective (e U) := by
  let MS : TopCat.Sheaf AddCommGrpCat X := ⟨M.presheaf, M.isSheaf⟩
  let NS : TopCat.Sheaf AddCommGrpCat X := ⟨N.presheaf, N.isSheaf⟩
  intro U
  let V : ι → X.Opens := fun i => U ⊓ W i
  have hV : U ≤ iSup V := by
    dsimp only [V]
    rw [← inf_iSup_eq, hW, inf_top_eq]
  constructor
  · intro s t hst
    apply MS.eq_of_locally_eq' V U (fun _ => homOfLE inf_le_left) hV
    intro i
    apply (hloc i (V i) inf_le_right).1
    rw [hnat, hnat, hst]
  · intro t
    choose s hs using fun i => (hloc i (V i) inf_le_right).2
      (N.presheaf.map (homOfLE (inf_le_left : V i ≤ U)).op t)
    have hcompat : TopCat.Presheaf.IsCompatible M.presheaf V s := by
      intro i j
      apply (hloc i (V i ⊓ V j) (inf_le_left.trans inf_le_right)).1
      change e _ (M.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (s i)) =
        e _ (M.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (s j))
      rw [hnat, hnat, hs i, hs j]
      change (N.presheaf.map (homOfLE (inf_le_left : V i ≤ U)).op ≫
        N.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op) t =
        (N.presheaf.map (homOfLE (inf_le_left : V j ≤ U)).op ≫
          N.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op) t
      rw [← N.presheaf.map_comp, ← N.presheaf.map_comp]
      rfl
    obtain ⟨z, hz, _⟩ := MS.existsUnique_gluing' V U
      (fun _ => homOfLE inf_le_left) hV s hcompat
    refine ⟨z, ?_⟩
    apply NS.eq_of_locally_eq' V U (fun _ => homOfLE inf_le_left) hV
    intro i
    rw [← hnat, hz i, hs i]

end PhilipponMultiplicity.SchemeSections

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponTensorPowerTwistSections

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ProjectiveTwistSheaf
open AlgebraicGeometry CategoryTheory MvPolynomial
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} {π : X ⟶ Spec (.of K)}
    {L : X.Modules} {N : ℕ} (p : L.ProjPresentation π N)
attribute [local instance] MvPolynomial.gradedAlgebra

theorem tensorPow_sections_equiv (d : ℕ) (U : X.Opens) :
    Nonempty (Γ(L.tensorPow d, U) ≃ₗ[Γ(X, U)]
      ProjSpace.twistObj π p.toProj d U) := by
  obtain ⟨e, _, hnat, hbij⟩ := p.exists_linearMap_sections_tensorPow_twistObj_monoidalV2 d
  let f (W : X.Opens) : Γ(L.tensorPow d, W) →ₗ[Γ(X, W)] Γ(twistSheaf p.toProj d, W) :=
    (sectionEquiv p.toProj π d W).symm.toLinearMap.comp (e W)
  have hf : ∀ (W W' : X.Opens) (h : W ≤ W') (s : Γ(L.tensorPow d, W')),
      f W ((L.tensorPow d).presheaf.map (homOfLE h).op s) =
        (twistSheaf p.toProj d).presheaf.map (homOfLE h).op (f W' s) := by
    intro W W' h s
    apply (sectionEquiv p.toProj π d W).injective
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.apply_symm_apply, sectionEquiv_res]
    exact hnat W W' h s
  have hlocal : ∀ (i : ULift.{u} (Fin (N + 1))) (W : X.Opens),
      W ≤ chart p.toProj i → Function.Bijective (f W) := by
    intro i W hW
    exact (sectionEquiv p.toProj π d W).symm.bijective.comp (hbij W i.down hW)
  have hb := SchemeSections.bijective_of_cover (L.tensorPow d) (twistSheaf p.toProj d)
    (chart p.toProj) (chart_cover p.toProj) f hf hlocal U
  exact ⟨(LinearEquiv.ofBijective (f U) hb).trans (sectionEquiv p.toProj π d U)⟩

theorem tensorPow_sections_equiv_over (d : ℕ) (U : X.Opens) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π (L.tensorPow d) U
    Nonempty (Γ(L.tensorPow d, U) ≃ₗ[K] ProjSpace.twistObj π p.toProj d U) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π (L.tensorPow d) U
  letI := Scheme.TwoAffineOpenCover.isScalarTower_sections π (L.tensorPow d) U
  letI : IsScalarTower K Γ(X, U) (ProjSpace.twistObj π p.toProj d U) :=
    (ProjSpace.twist π p.toProj d).isScalarTower U
  obtain ⟨e⟩ := tensorPow_sections_equiv p d U
  exact ⟨e.restrictScalars K⟩

end PhilipponMultiplicity.ProjectiveTwistSheaf
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponJacobsonClosedPoints

set_option autoImplicit false
noncomputable section

namespace PhilipponMultiplicity.JacobsonClosedPoints
open Topology TopologicalSpace Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem irreducible_of_image {f : X → Y} (hf : IsInducing f) {s : Set X}
    (hs : IsIrreducible (f '' s)) : IsIrreducible s := by
  refine ⟨Set.image_nonempty.mp hs.nonempty, ?_⟩
  intro u v hu hv hu' hv'
  obtain ⟨U, hU, rfl⟩ := hf.isOpen_iff.mp hu
  obtain ⟨V, hV, rfl⟩ := hf.isOpen_iff.mp hv
  obtain ⟨x, hx, hxu⟩ := hu'
  obtain ⟨y, hy, hyv⟩ := hv'
  obtain ⟨z, ⟨w, hw, rfl⟩, hwU, hwV⟩ := hs.isPreirreducible U V hU hV
    ⟨f x, ⟨x, hx, rfl⟩, hxu⟩ ⟨f y, ⟨y, hy, rfl⟩, hyv⟩
  exact ⟨w, hw, hwU, hwV⟩

variable (X) [JacobsonSpace X]

def irreducibleClosedOrderIso : IrreducibleCloseds (closedPoints X) ≃o
    IrreducibleCloseds X where
  toFun := IrreducibleCloseds.map Subtype.val continuous_subtype_val
  invFun Z :=
    { carrier := Subtype.val ⁻¹' (Z : Set X)
      isClosed' := Z.isClosed.preimage continuous_subtype_val
      isIrreducible' := by
        apply irreducible_of_image IsInducing.subtypeVal
        rw [Set.image_preimage_eq_inter_range, Subtype.range_coe]
        apply isIrreducible_iff_closure.mp
        rw [closure_inter_closedPoints Z.isClosed]
        exact Z.isIrreducible }
  left_inv Z := by
    apply IrreducibleCloseds.ext
    exact (IsInducing.subtypeVal.closure_eq_preimage_closure_image (Z : Set (closedPoints X))).symm.trans
      Z.isClosed.closure_eq
  right_inv Z := by
    apply IrreducibleCloseds.ext
    change closure (Subtype.val '' (Subtype.val ⁻¹' (Z : Set X))) = _
    rw [Set.image_preimage_eq_inter_range, Subtype.range_coe,
      closure_inter_closedPoints Z.isClosed]
  map_rel_iff' {A B} := by
    change IrreducibleCloseds.map Subtype.val continuous_subtype_val A ≤
      IrreducibleCloseds.map Subtype.val continuous_subtype_val B ↔ A ≤ B
    constructor
    · intro h
      have h' := Set.preimage_mono (f := (Subtype.val : closedPoints X → X)) h
      change (A : Set (closedPoints X)) ⊆ B
      simpa only [IrreducibleCloseds.coe_map,
        ← IsInducing.subtypeVal.closure_eq_preimage_closure_image,
        A.isClosed.closure_eq, B.isClosed.closure_eq] using h'
    · intro h
      exact IrreducibleCloseds.map_mono continuous_subtype_val h

theorem topologicalKrullDim_closedPoints :
    topologicalKrullDim (closedPoints X) = topologicalKrullDim X :=
  Order.krullDim_eq_of_orderIso (irreducibleClosedOrderIso X)

end PhilipponMultiplicity.JacobsonClosedPoints

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponClosureSubschemePoints

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ClosureScheme
open AlgebraicGeometry CategoryTheory Topology
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] (G : EmbeddedGroupProduct K) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension (fun _ => 1)))
    (V : Set (groupProjectiveClosure G))
    (hV : letI := G.ambient.zariskiTopology; IsClosed V)

def closedSubschemePoint (x : V) : closedSubscheme G b V :=
  Classical.choose (show point G b x.val ∈ Set.range (closedSubschemeι G b V) from
    (Set.ext_iff.mp (closedSubscheme_original_points G b V hV) x.val).mpr x.property)

@[simp] theorem closedSubschemePoint_ι (x : V) :
    closedSubschemeι G b V (closedSubschemePoint G b V hV x) = point G b x.val := by
  exact Classical.choose_spec (show point G b x.val ∈ Set.range (closedSubschemeι G b V) from
    (Set.ext_iff.mp (closedSubscheme_original_points G b V hV) x.val).mpr x.property)

theorem closedSubschemePoint_isClosed (x : V) :
    IsClosed {closedSubschemePoint G b V hV x} := by
  letI := closedSubschemeι_isClosedImmersion G b V
  apply (closedSubschemeι G b V).isClosedEmbedding.isClosed_iff_image_isClosed.mpr
  rw [Set.image_singleton, closedSubschemePoint_ι]
  exact ((closedPointHomeomorph G b) x.val).property

def closedSubschemeClosedPoint (x : V) : closedPoints (closedSubscheme G b V) :=
  ⟨closedSubschemePoint G b V hV x, closedSubschemePoint_isClosed G b V hV x⟩

theorem closedSubschemeClosedPoint_bijective :
    Function.Bijective (closedSubschemeClosedPoint G b V hV) := by
  letI := G.ambient.zariskiTopology
  letI := closedSubschemeι_isClosedImmersion G b V
  constructor
  · intro x y h
    apply Subtype.ext
    apply (closedPointHomeomorph G b).injective
    apply Subtype.ext
    change point G b x.val = point G b y.val
    have h' := congrArg (fun z : closedPoints (closedSubscheme G b V) =>
      closedSubschemeι G b V z.val) h
    simpa only [closedSubschemeClosedPoint, closedSubschemePoint_ι] using h'
  · intro z
    have hz : IsClosed {closedSubschemeι G b V z.val} := by
      rw [← Set.image_singleton]
      exact (closedSubschemeι G b V).isClosedEmbedding.isClosedMap _ z.property
    obtain ⟨x, hx⟩ := (closedPointHomeomorph G b).surjective ⟨_, hz⟩
    have hx' : point G b x = closedSubschemeι G b V z.val := congrArg Subtype.val hx
    have hxV : x ∈ V := by
      rw [← closedSubscheme_original_points G b V hV]
      exact ⟨z.val, hx'.symm⟩
    refine ⟨⟨x, hxV⟩, Subtype.ext ?_⟩
    apply (closedSubschemeι G b V).isClosedEmbedding.injective
    exact (closedSubschemePoint_ι G b V hV ⟨x, hxV⟩).trans hx'

theorem closedSubschemeClosedPoint_isInducing : letI := G.ambient.zariskiTopology
    IsInducing (closedSubschemeClosedPoint G b V hV) := by
  letI := G.ambient.zariskiTopology
  letI := closedSubschemeι_isClosedImmersion G b V
  have hcomp : (fun x : V =>
      closedSubschemeι G b V (closedSubschemeClosedPoint G b V hV x).val) =
      (fun x : V => point G b x.val) := by
    funext x
    exact closedSubschemePoint_ι G b V hV x
  apply IsInducing.subtypeVal.of_comp_iff.mp
  apply (closedSubschemeι G b V).isClosedEmbedding.isInducing.of_comp_iff.mp
  change IsInducing (fun x : V =>
    closedSubschemeι G b V (closedSubschemeClosedPoint G b V hV x).val)
  rw [hcomp]
  exact (point_isInducing G b).comp IsInducing.subtypeVal

def closedSubschemeClosedPointHomeomorph : letI := G.ambient.zariskiTopology
    V ≃ₜ closedPoints (closedSubscheme G b V) := by
  letI := G.ambient.zariskiTopology
  exact (Equiv.ofBijective _ (closedSubschemeClosedPoint_bijective G b V hV)).toHomeomorphOfIsInducing
    (closedSubschemeClosedPoint_isInducing G b V hV)

include hV in

theorem closedSubscheme_topologicalKrullDim : letI := G.ambient.zariskiTopology
    topologicalKrullDim (closedSubscheme G b V) = topologicalKrullDim V := by
  letI := G.ambient.zariskiTopology
  letI := closedSubscheme_isProper G b V
  letI := LocallyOfFiniteType.jacobsonSpace (closedSubschemeι G b V ≫ structureMap G b)
  exact (JacobsonClosedPoints.topologicalKrullDim_closedPoints (closedSubscheme G b V)).symm.trans
    (IsHomeomorph.topologicalKrullDim_eq _
      (closedSubschemeClosedPointHomeomorph G b V hV).isHomeomorph).symm

end PhilipponMultiplicity.ClosureScheme

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponFiniteDifference

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.FiniteDifference
variable {ι : Type*} [Fintype ι]

def shift (D : ι → ℚ) : MvPolynomial ι ℚ →ₐ[ℚ] MvPolynomial ι ℚ :=
  aeval (fun i => X i - C (D i))

def deriv (D : ι → ℚ) : MvPolynomial ι ℚ →ₗ[ℚ] MvPolynomial ι ℚ :=
  ∑ i, D i • (pderiv i).toLinearMap

theorem deriv_apply (D : ι → ℚ) (F : MvPolynomial ι ℚ) :
    deriv D F = ∑ i, D i • pderiv i F := by
  simp only [deriv, LinearMap.sum_apply, LinearMap.smul_apply]
  rfl

theorem deriv_mul_X (D : ι → ℚ) (F : MvPolynomial ι ℚ) (i : ι) :
    deriv D (F * X i) = deriv D F * X i + D i • F := by
  classical
  simp only [deriv_apply, pderiv_mul, pderiv_X, MvPolynomial.smul_eq_C_mul,
    mul_add, Finset.sum_add_distrib, Finset.sum_mul]
  simp [Pi.single_apply, mul_ite, mul_assoc]

private theorem component_mul_X (F : MvPolynomial ι ℚ) (i : ι) (n : ℕ) :
    homogeneousComponent (n + 1) (F * X i) = homogeneousComponent n F * X i := by
  classical
  letI := weightedGradedAlgebra ℚ (1 : ι → ℕ)
  have h := DirectSum.coe_decompose_mul_add_of_right_mem
    (weightedHomogeneousSubmodule ℚ (1 : ι → ℕ))
    (a := F) (i := n) (isHomogeneous_X ℚ i)
  change ((MvPolynomial.decompose' ℚ (1 : ι → ℕ) (F * X i)) (n + 1) : MvPolynomial ι ℚ) =
    ((MvPolynomial.decompose' ℚ (1 : ι → ℕ) F) n : MvPolynomial ι ℚ) * X i at h
  simpa only [MvPolynomial.decompose'_apply, homogeneousComponent] using h

private theorem degree_le_pred_of_top_zero (F : MvPolynomial ι ℚ) (n : ℕ)
    (hdegree : F.totalDegree ≤ n) (hzero : homogeneousComponent n F = 0) :
    F.totalDegree ≤ n - 1 := by
  classical
  apply Finset.sup_le
  intro d hd
  have hdn : d.degree ≤ n := (le_totalDegree hd).trans hdegree
  have hne : d.degree ≠ n := by
    intro heq
    have hh := congrArg (coeff d) hzero
    simp only [coeff_homogeneousComponent, heq, if_pos rfl, coeff_zero] at hh
    exact (mem_support_iff.mp hd) hh
  change d.degree ≤ n - 1
  omega

private def Expansion (D : ι → ℚ) (F : MvPolynomial ι ℚ) (n : ℕ) : Prop :=
  (shift D F).totalDegree ≤ n ∧ homogeneousComponent n (shift D F) = F ∧
    (∀ k, n = k + 1 → homogeneousComponent k (shift D F) = -deriv D F)

private theorem expansion_C (D : ι → ℚ) (c : ℚ) : Expansion D (C c) 0 := by
  simp [Expansion, shift]

private theorem expansion_mul_X (D : ι → ℚ) (F : MvPolynomial ι ℚ) (n : ℕ)
    (hF : F.IsHomogeneous n) (h : Expansion D F n) (i : ι) :
    Expansion D (F * X i) (n + 1) := by
  classical
  rcases h with ⟨hdeg, htop, hnext⟩
  have hs : shift D (F * X i) = shift D F * X i - D i • shift D F := by
    simp only [shift, map_mul, aeval_X, mul_sub, MvPolynomial.smul_eq_C_mul]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hs]
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · exact (totalDegree_mul _ _).trans (by simpa using Nat.add_le_add_right hdeg 1)
    · exact (totalDegree_smul_le _ _).trans (hdeg.trans (Nat.le_succ n))
  · rw [hs, map_sub, map_smul, component_mul_X, htop,
      homogeneousComponent_eq_zero _ _ (by omega : (shift D F).totalDegree < n + 1)]
    simp
  · intro k hk
    have hkn : k = n := by omega
    subst k
    rw [hs, map_sub, map_smul, htop, deriv_mul_X]
    cases n with
    | zero =>
      have hconst : F = C (coeff 0 F) := by
        exact (homogeneousComponent_eq_self hF).symm.trans
          (MvPolynomial.homogeneousComponent_zero F)
      have hd : deriv D F = 0 := by
        nth_rw 1 [hconst]
        simp [deriv]
      have hz : coeff (0 : ι →₀ ℕ) (shift D F * X i) = 0 := by
        simpa using (MvPolynomial.coeff_mul_X' (0 : ι →₀ ℕ) i (shift D F))
      simp [hd, homogeneousComponent_zero, hz]
    | succ n =>
      rw [component_mul_X, hnext n rfl]
      simp only [neg_mul, neg_add_rev, sub_eq_add_neg]
      ac_rfl

private theorem expansion_monomial (D : ι → ℚ) (a : ι →₀ ℕ) (c : ℚ) :
    Expansion D (monomial a c) a.degree := by
  classical
  induction a using Finsupp.induction with
  | zero => simpa using expansion_C D c
  | @single_add i k a hia hk ih =>
    have haux : ∀ k, Expansion D (monomial (Finsupp.single i k + a) c)
        ((Finsupp.single i k + a).degree) := by
      intro k
      induction k with
      | zero => simpa using ih
      | succ k ihk =>
        have heq : monomial (Finsupp.single i (k + 1) + a) c =
            monomial (Finsupp.single i k + a) c * X i := by
          simp only [monomial_single_add, pow_succ]
          ring
        rw [heq]
        have hh := expansion_mul_X D (monomial (Finsupp.single i k + a) c)
          (Finsupp.single i k + a).degree (isHomogeneous_monomial c rfl) ihk i
        simpa only [map_add, Finsupp.degree_single, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hh
    exact haux k

private theorem monomial_difference (D : ι → ℚ) (a : ι →₀ ℕ) (c : ℚ) :
    (monomial a c - shift D (monomial a c)).totalDegree ≤ a.degree - 1 ∧
    (a.degree = 0 → monomial a c - shift D (monomial a c) = 0) ∧
    (0 < a.degree → homogeneousComponent (a.degree - 1)
      (monomial a c - shift D (monomial a c)) = deriv D (monomial a c)) := by
  obtain ⟨hdeg, htop, hnext⟩ := expansion_monomial D a c
  have hhom := isHomogeneous_monomial (σ := ι) c (show a.degree = a.degree from rfl)
  have hbd : (monomial a c - shift D (monomial a c)).totalDegree ≤ a.degree :=
    (totalDegree_sub _ _).trans (max_le hhom.totalDegree_le hdeg)
  refine ⟨degree_le_pred_of_top_zero _ _ hbd ?_, ?_, ?_⟩
  · rw [map_sub, homogeneousComponent_eq_self hhom, htop, sub_self]
  · intro ha
    have hconst : monomial a c = C (coeff 0 (monomial a c)) :=
      (homogeneousComponent_eq_self (ha ▸ hhom)).symm.trans
        (MvPolynomial.homogeneousComponent_zero _)
    conv_lhs => rw [hconst]
    simp [shift]
  · intro ha
    rw [map_sub, homogeneousComponent_of_mem hhom,
      if_neg (by omega), hnext (a.degree - 1) (by omega)]
    simp

theorem top_difference (D : ι → ℚ) (F : MvPolynomial ι ℚ) (a : ℕ)
    (ha : 0 < a) (hF : F.totalDegree ≤ a) :
    (F - shift D F).totalDegree ≤ a - 1 ∧
    homogeneousComponent (a - 1) (F - shift D F) =
      deriv D (homogeneousComponent a F) := by
  classical
  let δ : MvPolynomial ι ℚ →ₗ[ℚ] MvPolynomial ι ℚ :=
    LinearMap.id - (shift D).toLinearMap
  have hδ : δ F = F - shift D F := rfl
  have hsum : F - shift D F = ∑ d ∈ F.support, δ (monomial d (coeff d F)) := by
    rw [← hδ, ← map_sum]
    congr 1
    exact F.as_sum
  have hterm (d : ι →₀ ℕ) (hd : d ∈ F.support) :
      (δ (monomial d (coeff d F))).totalDegree ≤ a - 1 ∧
      homogeneousComponent (a - 1) (δ (monomial d (coeff d F))) =
        deriv D (homogeneousComponent a (monomial d (coeff d F))) := by
    obtain ⟨hdeg, hz, ht⟩ := monomial_difference D d (coeff d F)
    have hda : d.degree ≤ a := (le_totalDegree hd).trans hF
    refine ⟨hdeg.trans (Nat.sub_le_sub_right hda 1), ?_⟩
    change homogeneousComponent (a - 1) (monomial d (coeff d F) - shift D (monomial d (coeff d F))) = _
    by_cases heq : d.degree = a
    · rw [homogeneousComponent_of_mem (isHomogeneous_monomial (coeff d F) rfl),
        if_pos heq.symm, ← heq]
      exact ht (heq ▸ ha)
    · rw [homogeneousComponent_of_mem (isHomogeneous_monomial (coeff d F) rfl),
        if_neg (Ne.symm heq), map_zero]
      by_cases hd0 : d.degree = 0
      · rw [hz hd0, map_zero]
      · exact homogeneousComponent_eq_zero _ _ (by omega)
  constructor
  · rw [hsum]
    exact (totalDegree_finsetSum _ _).trans (Finset.sup_le (fun d hd => (hterm d hd).1))
  · rw [hsum, map_sum]
    conv_rhs => rw [F.as_sum, map_sum, map_sum]
    exact Finset.sum_congr rfl (fun d hd => (hterm d hd).2)

end PhilipponMultiplicity.FiniteDifference

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponGroupPrimeComponents

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity

theorem IsPhilipponBaseField.isAlgClosed {K : Type*} [NontriviallyNormedField K]
    (hK : IsPhilipponBaseField K) : IsAlgClosed K := by
  have transfer (L : Type) [Field L] [IsAlgClosed L] (e : K ≃+* L) : IsAlgClosed K := by
    apply IsAlgClosed.of_exists_root K
    intro P _ hP
    obtain ⟨x,hx⟩ := IsAlgClosed.exists_eval₂_eq_zero e.toRingHom P
      (ne_of_gt (Polynomial.degree_pos_of_irreducible hP))
    refine ⟨e.symm x,?_⟩
    apply e.injective
    rw [map_zero]
    change e.toRingHom (P.eval (e.symm x)) = 0
    rw [← Polynomial.eval₂_at_apply]
    change P.eval₂ e.toRingHom (e (e.symm x)) = 0
    simpa only [RingEquiv.apply_symm_apply] using hx
  rcases hK with ⟨e,_⟩ | ⟨p,hp,h⟩
  · exact transfer ℂ e
  · letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨e,_⟩ := h
    exact transfer (PadicComplex p) e

theorem MultiProjectiveSpace.relevant_of_zeroLocus_nonempty {K : Type*} [Field K]
    (M : MultiProjectiveSpace K) (I : Ideal M.CoordinateRing)
    (hne : (M.zeroLocus I).Nonempty) :
    Hilbert.IsRelevant K M.factorCount M.ambientDimension I := by
  classical
  obtain ⟨x,hx⟩ := hne
  have hj (i : M.FactorIndex) : ∃ j, (x i).rep j ≠ 0 := by
    simpa only [ne_eq,funext_iff,Pi.zero_apply,not_forall] using
      (Projectivization.rep_nonzero (x i))
  choose j hj using hj
  let F : M.CoordinateRing := ∏ i, X ⟨i,j i⟩
  have hF : F ∈ Hilbert.irrelevantIdeal K M.factorCount M.ambientDimension := by
    apply Ideal.mem_iInf.mpr
    intro i
    apply Ideal.prod_mem _ (Finset.mem_univ i)
    exact Ideal.subset_span ⟨j i,rfl⟩
  intro hle
  have hz := hx F (hle hF)
  have hneF : M.eval F x ≠ 0 := by
    change MvPolynomial.eval (M.coordinate x) (∏ i, X ⟨i,j i⟩) ≠ 0
    simp only [map_prod,eval_X,MultiProjectiveSpace.coordinate]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hj i)
  exact hneF hz

variable {K : Type*} [NontriviallyNormedField K] (G : EmbeddedGroupProduct K)

end PhilipponMultiplicity

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponConnectedGroupIrreducible

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
noncomputable section

namespace PhilipponMultiplicity

variable {K : Type*} [Field K] {G : EmbeddedGroupProduct K}

theorem MultiProjectiveSpace.vanishingIdeal_isPrime_of_isIrreducible
    (M : MultiProjectiveSpace K) (S : Set M.Point)
    (hS : @IsIrreducible _ M.zariskiTopology S) : (M.vanishingIdeal S).IsPrime := by
  classical
  letI : TopologicalSpace M.Point := M.zariskiTopology
  apply Hilbert.prime_of_homogeneous_products M _ (vanishingIdeal_multihomogeneous K M S)
  · intro htop
    obtain ⟨x,hx⟩ := hS.nonempty
    have hz := M.eval_eq_zero_of_mem_vanishingIdeal
      (show (1 : M.CoordinateRing) ∈ M.vanishingIdeal S by rw [htop]; trivial) hx
    exact one_ne_zero (by simpa only [MultiProjectiveSpace.eval,map_one] using hz)
  · rintro P Q ⟨D,hP⟩ ⟨E,hQ⟩ hPQ
    by_contra! hn
    have hnzero (R : M.CoordinateRing) (d : M.FactorIndex → ℕ)
        (hR : M.IsHomogeneous R d) (hRI : R ∉ M.vanishingIdeal S) :
        (S ∩ {x | M.eval R x ≠ 0}).Nonempty := by
      by_contra hz
      apply hRI
      exact Ideal.subset_span ⟨⟨d,hR⟩,fun x hx => by
        by_contra hxR
        exact hz ⟨x,hx,hxR⟩⟩
    obtain ⟨x,hx,hxP,hxQ⟩ := hS.2 _ _ (M.isOpen_basic P D hP)
      (M.isOpen_basic Q E hQ) (hnzero P D hP hn.1) (hnzero Q E hQ hn.2)
    have hz := M.eval_eq_zero_of_mem_vanishingIdeal hPQ hx
    exact (mul_ne_zero hxP hxQ) (by simpa only [MultiProjectiveSpace.eval,map_mul] using hz)

end PhilipponMultiplicity

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponHilbertTopologicalDimension

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity
open Topology TopologicalSpace SectionThree

theorem krullDim_le_of_bounded_strictMono {P : Type*} [Preorder P]
    (f : P → ℕ) (n : ℕ) (hf : StrictMono f) (hn : ∀ x, f x ≤ n) :
    Order.krullDim P ≤ (n : WithBot ℕ∞) := by
  rw [Order.krullDim]
  apply iSup_le
  intro p
  have hp := (p.map f hf).head_add_length_le_nat
  have hl : (p.map f hf).last ≤ n := hn p.last
  have hlen : p.length ≤ n := by
    change f p.head + p.length ≤ f p.last at hp
    change f p.last ≤ n at hl
    omega
  exact_mod_cast hlen

variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem locusDimension_strict_of_irreducible
    (U V : Set M.Point) (hU : @IsClosed _ M.zariskiTopology U)
    (hV : @IsClosed _ M.zariskiTopology V)
    (hirrU : @IsIrreducible _ M.zariskiTopology U)
    (hirrV : @IsIrreducible _ M.zariskiTopology V) (hUV : U ⊂ V) :
    locusDimension M U < locusDimension M V := by
  letI := M.zariskiTopology
  have hzU : M.zeroLocus (M.vanishingIdeal U) = U :=
    (M.zeroLocus_vanishingIdeal_eq_closure U).trans hU.closure_eq
  have hzV : M.zeroLocus (M.vanishingIdeal V) = V :=
    (M.zeroLocus_vanishingIdeal_eq_closure V).trans hV.closure_eq
  apply Hilbert.relevant_prime_dimension_strict M
    (M.vanishingIdeal V) (M.vanishingIdeal U)
    (M.vanishingIdeal_isPrime_of_isIrreducible V hirrV)
    (M.vanishingIdeal_isPrime_of_isIrreducible U hirrU)
    (vanishingIdeal_multihomogeneous K M V) (vanishingIdeal_multihomogeneous K M U)
    (M.relevant_of_zeroLocus_nonempty _ (hzU.symm ▸ hirrU.nonempty))
  refine lt_of_le_of_ne (M.vanishingIdeal_antitone hUV.le) ?_
  intro heq
  apply hUV.ne
  exact (hzV.symm.trans ((congrArg M.zeroLocus heq).trans hzU)).symm

theorem topologicalKrullDim_le_locusDimension
    (V : Set M.Point) (hV : @IsClosed _ M.zariskiTopology V) :
    letI := M.zariskiTopology
    topologicalKrullDim V ≤ (locusDimension M V : WithBot ℕ∞) := by
  letI := M.zariskiTopology
  let f (Z : IrreducibleCloseds V) := locusDimension M (Subtype.val '' (Z : Set V))
  apply krullDim_le_of_bounded_strictMono f (locusDimension M V)
  · intro A B hAB
    apply locusDimension_strict_of_irreducible M
    · exact hV.isClosedEmbedding_subtypeVal.isClosedMap _ A.isClosed
    · exact hV.isClosedEmbedding_subtypeVal.isClosedMap _ B.isClosed
    · exact A.isIrreducible.image Subtype.val continuous_subtype_val.continuousOn
    · exact B.isIrreducible.image Subtype.val continuous_subtype_val.continuousOn
    · exact Subtype.val_injective.image_strictMono hAB
  · intro A
    exact Hilbert.idealDimension_antitone M (M.vanishingIdeal V)
      (M.vanishingIdeal (Subtype.val '' (A : Set V)))
      (vanishingIdeal_multihomogeneous K M V)
      (vanishingIdeal_multihomogeneous K M _)
      (M.vanishingIdeal_antitone (by rintro _ ⟨x, hx, rfl⟩; exact x.property))

end PhilipponMultiplicity

namespace PhilipponMultiplicity.ClosureScheme
open AlgebraicGeometry CategoryTheory Topology
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] (G : EmbeddedGroupProduct K) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension (fun _ => 1)))

theorem closedSubscheme_dimension_le (V : Set (groupProjectiveClosure G))
    (hV : letI := G.ambient.zariskiTopology; IsClosed V) :
    topologicalKrullDim (closedSubscheme G b V) ≤
      (SectionThree.locusDimension G.ambient (Subtype.val '' V) : WithBot ℕ∞) := by
  letI := G.ambient.zariskiTopology
  have hc : IsClosed (groupProjectiveClosure G : Set G.ambient.Point) := isClosed_closure
  rw [closedSubscheme_topologicalKrullDim G b V hV]
  have e := (IsEmbedding.subtypeVal (p := fun x => x ∈ groupProjectiveClosure G)).homeomorphImage V
  rw [IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph]
  exact topologicalKrullDim_le_locusDimension G.ambient _
    (hc.isClosedEmbedding_subtypeVal.isClosedMap V hV)

end PhilipponMultiplicity.ClosureScheme

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponClosureSheafEuler

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.SchemeEuler
open AlgebraicGeometry CategoryTheory MonoidalCategory Topology
universe u

def orderedAffineCover (X : Scheme.{u}) [CompactSpace X] : X.OrderedAffineCover := by
  classical
  let U := X.affineCover.finiteSubcover
  letI : LinearOrder U.I₀ := LinearOrder.lift' (Fintype.equivFin U.I₀) (Fintype.equivFin U.I₀).injective
  exact
    { ι := U.I₀
      U i := (U.f i).opensRange
      isAffineOpen i := isAffineOpen_opensRange (U.f i)
      iSup_eq_top := U.iSup_opensRange }

theorem supportedIn_top {R : Type u} [CommRing R] {X : Scheme.{u}}
    {π : X ⟶ Spec (.of R)} (F : OModulePresheaf π) : F.SupportedIn ⊤ := by
  intro U hU
  have hbot : (U : X.Opens) = ⊥ := by
    apply SetLike.coe_injective
    simpa only [TopologicalSpace.Closeds.coe_top, TopologicalSpace.Opens.coe_bot,
      Set.inter_univ] using hU
  letI : Subsingleton Γ(X, U) := by rw [hbot]; infer_instance
  exact Module.subsingleton Γ(X, U) (F.obj U)

end PhilipponMultiplicity.SchemeEuler

namespace PhilipponMultiplicity.ClosureScheme
open AlgebraicGeometry CategoryTheory MonoidalCategory Topology
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] (G : EmbeddedGroupProduct K) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension (fun _ => 1)))

def closedSubschemeOrderedCover (V : Set (groupProjectiveClosure G)) :
    (closedSubscheme G b V).OrderedAffineCover := by
  letI := closedSubscheme_isProper G b V
  letI := QuasiCompact.compactSpace_of_compactSpace (closedSubschemeι G b V ≫ structureMap G b)
  exact SchemeEuler.orderedAffineCover _

end PhilipponMultiplicity.ClosureScheme

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponFilteredEuler

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.FilteredEuler

section Descent
variable {R L A C : Type*} [Ring R] [AddCommGroup L] [Module R L]
  [AddCommGroup A] [Module R A] [AddCommGroup C] [Module R C]

end Descent

section Action
variable {T L A : Type*} [Group T] [AddCommGroup L] [Module ℤ L]
  [AddCommGroup A] [Module ℤ A]
  (q : L →ₗ[ℤ] A) (hq : Function.Surjective q)
  (ρ : T →* (L ≃ₗ[ℤ] L))
  (hker : ∀ g x, q x = 0 → q (ρ g x) = 0)

end Action

section Twists
variable {L B : Type*} [AddCommGroup L] [AddCommGroup B] [Module ℤ B]
  (β : Multiplicative L →* (B ≃ₗ[ℤ] B))

def twist (x : L) : B →ₗ[ℤ] B := (β (Multiplicative.ofAdd x)).toLinearMap

def difference (y : L) : B →ₗ[ℤ] B := twist β y - LinearMap.id

end Twists

section EulerDescent
variable {L A B : Type*} [AddCommGroup L] [Module ℤ L]
  [AddCommGroup A] [Module ℤ A] [AddCommGroup B] [Module ℤ B]
  (q : L →ₗ[ℤ] A) (hq : Function.Surjective q)
  (β : Multiplicative L →* (B ≃ₗ[ℤ] B)) (χ : B →ₗ[ℤ] ℚ)
  (hχ : ∀ l, q l = 0 → ∀ b, χ (twist β l b) = χ b)

end EulerDescent
end PhilipponMultiplicity.FilteredEuler
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponComplexEuler

set_option autoImplicit false
open scoped BigOperators
open CategoryTheory
noncomputable section

namespace PhilipponMultiplicity.ComplexEuler

universe u
variable {K : Type u} [Field K]

theorem short_complex_rank (S : ShortComplex (ModuleCat.{u} K))
    [Module.Finite K S.X₁] [Module.Finite K S.X₂] :
    Module.finrank K S.homology + Module.finrank K (LinearMap.range S.f.hom) +
      Module.finrank K (LinearMap.range S.g.hom) = Module.finrank K S.X₂ := by
  have hf := S.f.hom.finrank_range_add_finrank_ker
  have hc := S.moduleCatToCycles.finrank_range_add_finrank_ker
  have hker : LinearMap.ker S.moduleCatToCycles = LinearMap.ker S.f.hom :=
    LinearMap.ker_codRestrict _ _ _
  rw [hker] at hc
  have hquot := (LinearMap.range S.moduleCatToCycles).finrank_quotient_add_finrank
  have hhom := S.moduleCatHomologyIso.toLinearEquiv.finrank_eq
  change Module.finrank K S.homology =
    Module.finrank K (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) at hhom
  have hg := S.g.hom.finrank_range_add_finrank_ker
  omega

theorem cochain_rank (V : CochainComplex (ModuleCat.{u} K) ℤ)
    [∀ i, Module.Finite K (V.X i)] (i : ℤ) :
    Module.finrank K (V.homology i) +
      Module.finrank K (LinearMap.range (V.d (i-1) i).hom) +
      Module.finrank K (LinearMap.range (V.d i (i+1)).hom) =
      Module.finrank K (V.X i) := by
  have hp : (ComplexShape.up ℤ).prev i = i-1 :=
    (ComplexShape.up ℤ).prev_eq' (by change i-1+1=i; omega)
  have hn : (ComplexShape.up ℤ).next i = i+1 :=
    (ComplexShape.up ℤ).next_eq' rfl
  let : Module.Finite K (V.sc i).X₁ :=
    show Module.Finite K (V.X ((ComplexShape.up ℤ).prev i)) from inferInstance
  let : Module.Finite K (V.sc i).X₂ :=
    show Module.Finite K (V.X i) from inferInstance
  have h := short_complex_rank (V.sc i)
  change Module.finrank K (V.homology i) +
    Module.finrank K (LinearMap.range (V.d ((ComplexShape.up ℤ).prev i) i).hom) +
    Module.finrank K (LinearMap.range (V.d i ((ComplexShape.up ℤ).next i)).hom) =
      Module.finrank K (V.X i) at h
  rw [congrArg (fun j => Module.finrank K (LinearMap.range (V.d j i).hom)) hp,
    congrArg (fun j => Module.finrank K (LinearMap.range (V.d i j).hom)) hn] at h
  exact h

def sign (i : ℤ) : ℤ := Int.negOnePow i

theorem sign_succ (i : ℤ) : sign (i+1) = -sign i := by
  simp [sign, Int.negOnePow_succ]

theorem signed_finite (r : ℤ → ℕ) (hr : Function.HasFiniteSupport r) :
    Function.HasFiniteSupport (fun i => sign i * (r i : ℤ)) := by
  apply hr.subset
  intro i hi
  change r i ≠ 0
  intro h
  exact hi (by simp [h])

theorem alternating_shift (b : ℤ → ℤ) :
    (∑ᶠ i : ℤ, sign i * b (i-1)) = -(∑ᶠ i : ℤ, sign i * b i) := by
  have h := finsum_comp_equiv (Equiv.addRight (1 : ℤ))
    (f := fun i : ℤ => sign i * b (i-1))
  change (∑ᶠ i : ℤ, sign (i+1) * b (i+1-1)) = _ at h
  simp only [add_sub_cancel_right] at h
  rw [← h]
  simp only [sign_succ, neg_mul, finsum_neg_distrib]

theorem alternating_rank_identity (r h b : ℤ → ℕ)
    (hr : Function.HasFiniteSupport r)
    (heq : ∀ i, h i + b (i-1) + b i = r i) :
    (∑ᶠ i, sign i * (h i : ℤ)) = ∑ᶠ i, sign i * (r i : ℤ) := by
  have hh : Function.HasFiniteSupport h := hr.subset (by
    intro i hi
    change h i ≠ 0 at hi
    change r i ≠ 0
    have := heq i
    omega)
  have hb : Function.HasFiniteSupport b := hr.subset (by
    intro i hi
    change b i ≠ 0 at hi
    change r i ≠ 0
    have := heq i
    omega)
  have hbp : Function.HasFiniteSupport (fun i => b (i-1)) :=
    hb.fun_comp_of_injective (fun _ _ h => by omega)
  have hsum : (∑ᶠ i, sign i * (r i : ℤ)) =
      (∑ᶠ i, sign i * (h i : ℤ)) + (∑ᶠ i, sign i * (b (i-1) : ℤ)) +
        (∑ᶠ i, sign i * (b i : ℤ)) := by
    calc
      _ = ∑ᶠ i, ((sign i * (h i : ℤ) + sign i * (b (i-1) : ℤ)) +
          sign i * (b i : ℤ)) := by
        apply finsum_congr
        intro i
        rw [← heq i, Nat.cast_add, Nat.cast_add]
        ring
      _ = _ := by
        have h₁ := finsum_add_distrib ((signed_finite h hh).add (signed_finite _ hbp))
          (signed_finite b hb)
        have h₂ := finsum_add_distrib (signed_finite h hh) (signed_finite _ hbp)
        simpa only [Pi.add_apply] using
          h₁.trans (congrArg (fun x => x + ∑ᶠ i, sign i * (b i : ℤ)) h₂)
  rw [alternating_shift (fun i => (b i : ℤ))] at hsum
  omega

theorem homology_euler_eq (V : CochainComplex (ModuleCat.{u} K) ℤ)
    [∀ i, Module.Finite K (V.X i)]
    (hfinite : Function.HasFiniteSupport (fun i => Module.finrank K (V.X i))) :
    V.homologyEulerChar = V.eulerChar := by
  apply alternating_rank_identity _ _
    (fun i => Module.finrank K (LinearMap.range (V.d i (i+1)).hom)) hfinite
  intro i
  rw [congrArg (fun j => Module.finrank K (LinearMap.range (V.d (i-1) j).hom))
    (sub_add_cancel i 1)]
  exact cochain_rank V i

theorem homology_euler_of_ranks (V : CochainComplex (ModuleCat.{u} K) ℤ)
    [∀ i, Module.Finite K (V.X i)] (r : ℤ → ℕ) (hr : Function.HasFiniteSupport r)
    (hrank : ∀ i, Module.finrank K (V.X i) = r i) :
    V.homologyEulerChar = ∑ᶠ i, sign i * (r i : ℤ) := by
  have hfinite : Function.HasFiniteSupport (fun i => Module.finrank K (V.X i)) := by
    simpa only [hrank] using hr
  rw [homology_euler_eq V hfinite]
  exact finsum_congr (fun i => congrArg (fun n : ℕ => sign i * (n : ℤ)) (hrank i))

end PhilipponMultiplicity.ComplexEuler
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponIntegerEulerComplex

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity.ComplexEuler
open CategoryTheory
universe u

def integerRanks (z : ℤ) (i : ℤ) : ℕ :=
  if i = 0 then z.toNat else if i = 1 then (-z).toNat else 0

theorem integerRanks_finite (z : ℤ) : Function.HasFiniteSupport (integerRanks z) := by
  apply Set.Finite.subset (Set.toFinite ({0, 1} : Set ℤ))
  intro i hi
  by_contra h
  have h0 : i ≠ 0 := by intro he; exact h (by simp [he])
  have h1 : i ≠ 1 := by intro he; exact h (by simp [he])
  exact hi (by simp [integerRanks, h0, h1])

def integerComplex (K : Type u) [Field K] (z : ℤ) : CochainComplex (ModuleCat.{u} K) ℤ where
  X i := ModuleCat.of K (Fin (integerRanks z i) → K)
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

instance integerComplex_finite (K : Type u) [Field K] (z i : ℤ) :
    Module.Finite K ((integerComplex K z).X i) := by
  change Module.Finite K (Fin (integerRanks z i) → K)
  infer_instance

theorem integerComplex_rank (K : Type u) [Field K] (z i : ℤ) :
    Module.finrank K ((integerComplex K z).X i) = integerRanks z i := by
  change Module.finrank K (Fin (integerRanks z i) → K) = _
  simp

theorem integerComplex_euler (K : Type u) [Field K] (z : ℤ) :
    (integerComplex K z).homologyEulerChar = z := by
  rw [homology_euler_of_ranks _ _ (integerRanks_finite z) (integerComplex_rank K z)]
  have hs : Function.support (fun i => sign i * (integerRanks z i : ℤ)) ⊆
      ({0, 1} : Finset ℤ) := by
    intro i hi
    by_contra h
    have h0 : i ≠ 0 := by intro he; exact h (by simp [he])
    have h1 : i ≠ 1 := by intro he; exact h (by simp [he])
    exact hi (by simp [integerRanks, h0, h1])
  rw [finsum_eq_sum_of_support_subset _ hs]
  simp [integerRanks, sign]
  omega

theorem local_complexes_of_integer_locally_constant (K : Type u) [Field K]
    {X : Type*} [TopologicalSpace X] (f : X → ℤ) (hf : IsLocallyConstant f) :
    ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ r : ℤ → ℕ, Function.HasFiniteSupport r ∧
      ∃ V : U → CochainComplex (ModuleCat.{u} K) ℤ,
        (∀ z i, Module.Finite K ((V z).X i)) ∧
        (∀ z i, Module.finrank K ((V z).X i) = r i) ∧
        (∀ z : U, (f z.val : ℚ) = ((V z).homologyEulerChar : ℚ)) := by
  intro x
  obtain ⟨U, hU, hx, hconst⟩ := (IsLocallyConstant.iff_exists_open f).mp hf x
  refine ⟨U, hU, hx, integerRanks (f x), integerRanks_finite _,
    (fun _ => integerComplex K (f x)), (fun _ _ => inferInstance),
    (fun _ i => integerComplex_rank K (f x) i), ?_⟩
  intro z
  rw [integerComplex_euler, hconst z.val z.property]

end PhilipponMultiplicity.ComplexEuler

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponFilteredTwistGenerators

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.FilteredTwistGenerators
open CategoryTheory
universe u v
variable {L : Type u} [AddCommGroup L] {B : Type v} [AddCommGroup B] [Module ℤ B]
    (β : Multiplicative L →* (B ≃ₗ[ℤ] B)) (F : ℕ → Submodule ℤ B)

@[ext] structure Generator where
  dimension : ℕ
  value : B
  mem_level : value ∈ F (dimension + 1)

variable (hstable : ∀ l n b, b ∈ F n → β l b ∈ F n)

def permutation (l : Multiplicative L) : Equiv.Perm (Generator F) where
  toFun a := ⟨a.dimension, β l a.value, hstable l _ _ a.mem_level⟩
  invFun a := ⟨a.dimension, β l⁻¹ a.value, hstable l⁻¹ _ _ a.mem_level⟩
  left_inv a := by
    apply Generator.ext
    · rfl
    · change β l⁻¹ (β l a.value) = a.value
      rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
  right_inv a := by
    apply Generator.ext
    · rfl
    · change β l (β l⁻¹ a.value) = a.value
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl

def action : Multiplicative L →* Equiv.Perm (Generator F) where
  toFun := permutation β F hstable
  map_one' := by
    apply Equiv.ext
    intro a
    apply Generator.ext
    · rfl
    · change β 1 a.value = a.value
      rw [map_one]
      rfl
  map_mul' l m := by
    apply Equiv.ext
    intro a
    apply Generator.ext
    · rfl
    · change β (l * m) a.value = β l (β m a.value)
      rw [map_mul]
      rfl

@[simp] theorem action_value (l : Multiplicative L) (a : Generator F) :
    (action β F hstable l a).value = β l a.value := rfl

def relation (a b : Generator F) (Q : Option (Generator F)) : Prop :=
  b.value = a.value + Q.elim 0 Generator.value

theorem relation_stable (l : Multiplicative L) (a b : Generator F)
    (Q : Option (Generator F)) (h : relation F a b Q) :
    relation F (action β F hstable l a) (action β F hstable l b)
      (Q.map (action β F hstable l)) := by
  cases Q with
  | none => simpa only [relation, Option.elim_none, add_zero, Option.map_none,
      action_value] using congrArg (β l) (show b.value = a.value from by simpa [relation] using h)
  | some q =>
    change β l b.value = β l a.value + β l q.value
    change b.value = a.value + q.value at h
    rw [h, map_add]

def euler (χ : B →ₗ[ℤ] ℤ) (a : Generator F) : ℚ := χ a.value

theorem euler_additive (χ : B →ₗ[ℤ] ℤ) (a b : Generator F)
    (Q : Option (Generator F)) (h : relation F a b Q) :
    euler F χ b = euler F χ a + Q.elim 0 (euler F χ) := by
  cases Q with
  | none => simpa only [relation, Option.elim_none, add_zero, euler] using
      congrArg (fun x => (χ x : ℚ)) (show b.value = a.value from by simpa [relation] using h)
  | some q =>
    change b.value = a.value + q.value at h
    change (χ b.value : ℚ) = (χ a.value : ℚ) + (χ q.value : ℚ)
    rw [h, map_add, Int.cast_add]

include hstable in

theorem common_source (hzero : F 0 = ⊥)
    (hdrop : ∀ n l b, b ∈ F (n + 1) → β (Multiplicative.ofAdd l) b - b ∈ F n)
    (l : L) (a : Generator F) :
    ∃ (k : Generator F) (Q Q' : Option (Generator F)),
      relation F k a Q ∧ relation F k (action β F hstable (Multiplicative.ofAdd l) a) Q' ∧
      (∀ b ∈ Q, b.dimension < a.dimension) ∧ (∀ b ∈ Q', b.dimension < a.dimension) := by
  cases a with
  | mk d b hb =>
    cases d with
    | zero =>
      have hd := hdrop 0 l b hb
      rw [hzero, Submodule.mem_bot, sub_eq_zero] at hd
      refine ⟨⟨0, b, hb⟩, none, none, ?_, ?_, ?_, ?_⟩
      · simp [relation]
      · simpa [relation] using hd
      · simp
      · simp
    | succ n =>
      let q : Generator F :=
        ⟨n, β (Multiplicative.ofAdd l) b - b, hdrop (n + 1) l b hb⟩
      refine ⟨⟨n + 1, b, hb⟩, none, some q, ?_, ?_, ?_, ?_⟩
      · simp [relation]
      · change β (Multiplicative.ofAdd l) b = b + (β (Multiplicative.ofAdd l) b - b)
        abel
      · simp
      · intro c hc
        have heq : q = c := by simpa only [Option.mem_some_iff] using hc
        subst c
        exact Nat.lt_succ_self n

end PhilipponMultiplicity.FilteredTwistGenerators

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponDifferenceFiltration

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section

namespace PhilipponMultiplicity.DifferenceFiltration
universe u v
variable {L : Type u} [AddCommGroup L]
    {B : Type v} [AddCommGroup B] [Module ℤ B]
    (β : Multiplicative L →* (B ≃ₗ[ℤ] B))

def level : ℕ → Submodule ℤ B
  | 0 => ⊥
  | n + 1 => ⨅ l : L, (level n).comap (FilteredEuler.difference β l)

theorem mem_level_succ (n : ℕ) (b : B) :
    b ∈ level β (n + 1) ↔
      ∀ l : L, FilteredEuler.difference β l b ∈ level β n := by
  simp only [level, Submodule.mem_iInf, Submodule.mem_comap]

theorem level_le_succ (n : ℕ) : level β n ≤ level β (n + 1) := by
  induction n with
  | zero => exact bot_le
  | succ n ih =>
    intro b hb
    rw [mem_level_succ] at hb ⊢
    exact fun l => ih (hb l)

theorem difference_mem (n : ℕ) (l : L) (b : B)
    (hb : b ∈ level β (n + 1)) :
    β (Multiplicative.ofAdd l) b - b ∈ level β n :=
  (mem_level_succ β n b).mp hb l

theorem stable (l : Multiplicative L) (n : ℕ) (b : B)
    (hb : b ∈ level β n) : β l b ∈ level β n := by
  cases n with
  | zero =>
    have hb0 : b = 0 := by simpa [level] using hb
    simp [hb0]
  | succ n =>
    have hd := level_le_succ β n (difference_mem β n l.toAdd b hb)
    have heq : β l b = b + (β l b - b) := by abel
    rw [heq]
    exact (level β (n + 1)).add_mem hb hd

end PhilipponMultiplicity.DifferenceFiltration

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponPolynomialFunctionFiltration

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.PolynomialFunctionFiltration
open MvPolynomial
open scoped BigOperators
universe u
variable (L : Type u) [AddCommGroup L]

def shiftEquiv (l : L) : (L → ℤ) ≃ₗ[ℤ] (L → ℤ) where
  toFun f x := f (x + l)
  invFun f x := f (x - l)
  left_inv f := by funext x; simp
  right_inv f := by funext x; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def action : Multiplicative L →* ((L → ℤ) ≃ₗ[ℤ] (L → ℤ)) where
  toFun l := shiftEquiv L l.toAdd
  map_one' := by
    apply LinearEquiv.ext
    intro f
    funext x
    exact congrArg f (add_zero x)
  map_mul' l m := by
    apply LinearEquiv.ext
    intro f
    funext x
    exact congrArg f (add_assoc x l.toAdd m.toAdd).symm

variable {L}

def IsPolynomialAtMost (f : L → ℤ) (d : ℕ) : Prop :=
  ∀ (ι : Type u) [Fintype ι] (x : L) (v : ι → L),
    ∃ P : MvPolynomial ι ℚ, P.totalDegree ≤ d ∧
      ∀ z : ι → ℤ, eval (fun i => (z i : ℚ)) P = (f (x + ∑ i, z i • v i) : ℚ)

theorem eval_shift {ι : Type*} [Fintype ι] (D z : ι → ℚ)
    (P : MvPolynomial ι ℚ) :
    eval z (FiniteDifference.shift D P) = eval (fun i => z i - D i) P := by
  change ((eval z).comp (FiniteDifference.shift D).toRingHom) P = _
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [FiniteDifference.shift]
  · intro i
    simp [FiniteDifference.shift]

theorem zero_degree_invariant {f : L → ℤ} (hf : IsPolynomialAtMost f 0)
    (y x : L) : f (x + y) = f x := by
  obtain ⟨P, hd, he⟩ := hf PUnit.{u+1} x (fun _ => y)
  have hC : P = C (P.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hd)
  have h0 := he (fun _ => 0)
  have h1 := he (fun _ => 1)
  rw [hC] at h0 h1
  simp only [eval_C] at h0 h1
  have heq : (f (x + y) : ℚ) = (f x : ℚ) := by
    simpa using h1.symm.trans h0
  exact_mod_cast heq

theorem difference_polynomial {f : L → ℤ} {d : ℕ}
    (hf : IsPolynomialAtMost f (d + 1)) (y : L) :
    IsPolynomialAtMost (fun x => f (x + y) - f x) d := by
  classical
  intro ι inst x v
  let := inst
  obtain ⟨P, hd, he⟩ := hf (Option ι) x (fun i => i.elim y v)
  let D : Option ι → ℚ := fun i => i.elim (-1) (fun _ => 0)
  let R := FiniteDifference.shift D P - P
  let Q := (optionEquivLeft ℚ ι R).coeff 0
  refine ⟨Q, ?_, ?_⟩
  · have hR : R.totalDegree ≤ d := by
      have h := (FiniteDifference.top_difference D P (d + 1) (by omega) hd).1
      simpa only [R, ← neg_sub P, totalDegree_neg, Nat.add_sub_cancel] using h
    exact (totalDegree_coeff_optionEquivLeft_le ℚ ι R 0).trans hR
  · intro z
    have hQ : eval (fun i => (z i : ℚ)) Q =
        eval (fun i : Option ι => i.elim 0 (fun j => (z j : ℚ))) R := by
      rw [optionEquivLeft_elim_eval]
      simp [Q, ← Polynomial.coeff_zero_eq_eval_zero]
    rw [hQ, show R = FiniteDifference.shift D P - P from rfl, map_sub, eval_shift]
    have hplus : (fun i : Option ι => i.elim 0 (fun j => (z j : ℚ)) - D i) =
        (fun i : Option ι => ((i.elim 1 z : ℤ) : ℚ)) := by
      funext i
      cases i <;> simp [D]
    have hzero : (fun i : Option ι => i.elim 0 (fun j => (z j : ℚ))) =
        (fun i : Option ι => ((i.elim 0 z : ℤ) : ℚ)) := by
      funext i
      cases i <;> simp
    rw [hplus, hzero, he, he]
    simp only [Fintype.sum_option, Option.elim_none, Option.elim_some,
      one_smul, zero_smul, zero_add, Int.cast_sub]
    congr 2
    abel

theorem mem_level {f : L → ℤ} {d : ℕ} (hf : IsPolynomialAtMost f d) :
    f ∈ DifferenceFiltration.level (action L) (d + 1) := by
  induction d generalizing f with
  | zero =>
    rw [DifferenceFiltration.mem_level_succ]
    intro y
    change (fun x => f (x + y) - f x) ∈ (⊥ : Submodule ℤ (L → ℤ))
    rw [Submodule.mem_bot]
    funext x
    exact sub_eq_zero.mpr (zero_degree_invariant hf y x)
  | succ d ih =>
    rw [DifferenceFiltration.mem_level_succ]
    intro y
    exact ih (difference_polynomial hf y)

end PhilipponMultiplicity.PolynomialFunctionFiltration

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponSheafEulerFiltration

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.SchemeEuler
open AlgebraicGeometry CategoryTheory MonoidalCategory Topology
open scoped BigOperators
universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} (π : X ⟶ Spec (.of K))

theorem euler_iso {M N : X.Modules} (e : M ≅ N) (U : X.OrderedAffineCover) :
    (OModulePresheaf.ofModules π M).eulerChar U =
      (OModulePresheaf.ofModules π N).eulerChar U := by
  obtain ⟨⟨e0⟩, hS, -⟩ := OModulePresheaf.nonempty_cechEquiv_ofModules_of_iso π e U
  have h : ∀ i, (OModulePresheaf.ofModules π M).cechFinrank U i =
      (OModulePresheaf.ofModules π N).cechFinrank U i := by
    intro i
    cases i with
    | zero => exact e0.finrank_eq
    | succ j => obtain ⟨e⟩ := hS j; exact e.finrank_eq
  rw [OModulePresheaf.eulerChar_def, OModulePresheaf.eulerChar_def]
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

variable [IsProper π] (U : X.OrderedAffineCover)
    {L : Type u} [AddCommGroup L]
    (φ : Multiplicative L →* Skeleton X.Modules)
    (ℓ : L → X.Modules) (hℓ : ∀ l, Scheme.Modules.IsInvertible (ℓ l))
    (hclass : ∀ l, toSkeleton (ℓ l) = φ (Multiplicative.ofAdd l))

include φ hℓ hclass

theorem euler_function_polynomial (d : ℕ) (hd : topologicalKrullDim X ≤ d) :
    PolynomialFunctionFiltration.IsPolynomialAtMost
      (fun l => (OModulePresheaf.ofModules π (ℓ l)).eulerChar U) d := by
  classical
  intro ι inst x v
  let := inst
  obtain ⟨P, hP, he⟩ :=
    OModulePresheaf.exists_mvPolynomial_totalDegree_le_forall_eulerChar_tensor_eq_monoidalV2
      π U (ℓ x)
      (OModulePresheaf.isCoherent_ofModules_of_locallyTrivial π (ℓ x) (hℓ x).exists_trivialization)
      (OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial π (ℓ x)
        (hℓ x).exists_trivialization)
      ⊤ (supportedIn_top _) d (IsInducing.subtypeVal.topologicalKrullDim_le.trans hd)
      (fun i => ℓ (v i)) (fun i => hℓ (v i))
  refine ⟨P, hP, ?_⟩
  intro z
  have hnat (a : ι → ℕ) :
      (∏ i, toSkeleton (ℓ (v i)) ^ a i) = φ (Multiplicative.ofAdd (∑ i, a i • v i)) := by
    simp only [hclass, ofAdd_sum, map_prod, ofAdd_nsmul, map_pow]
  have hsum : (∑ i, z i • v i) + (∑ i, (-z i).toNat • v i) = ∑ i, (z i).toNat • v i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← natCast_zsmul, ← add_zsmul, ← natCast_zsmul]
    congr 1
    omega
  have hrel : toSkeleton (ℓ (∑ i, z i • v i)) *
      ∏ i, toSkeleton (ℓ (v i)) ^ (-z i).toNat = ∏ i, toSkeleton (ℓ (v i)) ^ (z i).toNat := by
    rw [hclass, hnat, hnat, ← map_mul, ← ofAdd_add, hsum]
  have hχ := he (fun i => (z i).toNat) (fun i => (-z i).toNat) (ℓ (∑ i, z i • v i)) hrel
  have hz : (fun i => ((z i).toNat : ℚ) - ((-z i).toNat : ℚ)) = (fun i => (z i : ℚ)) := by
    funext i
    have hi : ((z i).toNat : ℤ) - ((-z i).toNat : ℤ) = z i := by omega
    exact_mod_cast hi
  rw [hz] at hχ
  have heq : toSkeleton (ℓ x ⊗ ℓ (∑ i, z i • v i)) = toSkeleton (ℓ (x + ∑ i, z i • v i)) := by
    rw [Skeleton.toSkeleton_tensorObj, hclass, hclass, hclass, ofAdd_add, map_mul]
  obtain ⟨e⟩ := toSkeleton_eq_toSkeleton_iff.mp heq
  rw [euler_iso π e U] at hχ
  exact hχ.symm

end PhilipponMultiplicity.SchemeEuler

namespace PhilipponMultiplicity.ClosureScheme
open AlgebraicGeometry CategoryTheory
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] (G : EmbeddedGroupProduct K) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension (fun _ => 1)))

end PhilipponMultiplicity.ClosureScheme

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponHyperplaneEulerHilbert

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section

namespace PhilipponMultiplicity.SchemeEuler
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u

theorem eventually_euler_tensorPow_eq_sections {K : Type u} [Field K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsSeparated π]
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (N : ℕ) (p : L.ProjPresentation π N) (hp : IsFinite p.toProj) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ U : X.OrderedAffineCover,
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π (L.tensorPow d) ⊤
      (OModulePresheaf.ofModules π (L.tensorPow d)).eulerChar U =
        (Module.finrank K Γ(L.tensorPow d, ⊤) : ℤ) := by
  obtain ⟨d₀, hd₀⟩ :=
    Scheme.Modules.exists_forall_subsingleton_HSucc_tensorObj_tensorPow_of_isFinite_toProj_monoidalV2
      K π L hL N p hp (𝟙_ X.Modules) (Scheme.Modules.isInvertible_unit X)
  refine ⟨d₀, fun d hd U => ?_⟩
  have h := OModulePresheaf.finrank_sections_eq_eulerChar_of_iso_of_forall_subsingleton_HSucc
    π ((𝟙_ X.Modules) ⊗ L.tensorPow d) (L.tensorPow d) (λ_ (L.tensorPow d)).symm
    U (hd₀ d hd U)
  rw [euler_iso π (λ_ (L.tensorPow d)) U] at h
  exact h.symm

end PhilipponMultiplicity.SchemeEuler

namespace PhilipponMultiplicity.ClosureScheme
open AlgebraicGeometry CategoryTheory MvPolynomial ProjectiveTwistSheaf
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] (G : EmbeddedGroupProduct K) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension (fun _ => 1)))
    (V : Set (groupProjectiveClosure G))
attribute [local instance] MvPolynomial.gradedAlgebra

end PhilipponMultiplicity.ClosureScheme
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponVeroneseEulerHilbert

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section

namespace PhilipponMultiplicity.ClosureScheme
open AlgebraicGeometry CategoryTheory MvPolynomial ProjectiveTwistSheaf
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] (G : EmbeddedGroupProduct K) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension (fun _ => 1)))
    (D : G.FactorIndex → ℕ) (hD : ∀ i, 1 ≤ D i) {r : ℕ}
    (c : Module.Basis (projectiveSpace K r).Variable K
      (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension D))
    (V : Set (groupProjectiveClosure G))
attribute [local instance] MvPolynomial.gradedAlgebra

theorem eventually_veronese_euler_eq_hilbertFunction :
    let L := twistSheaf (closedSubschemeVeroneseEmbedding G b D hD c V) 1
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ U : (closedSubscheme G b V).OrderedAffineCover,
      (OModulePresheaf.ofModules (closedSubschemeι G b V ≫ structureMap G b)
        (L.tensorPow n)).eulerChar U =
        (Hilbert.hilbertFunction K G.ambient.factorCount G.ambient.ambientDimension
          (G.ambient.vanishingIdeal (Subtype.val '' V)) (fun i => n * D i) : ℤ) := by
  let φ := closedSubschemeVeroneseEmbedding G b D hD c V
  let L := twistSheaf φ 1
  let π := φ ≫ ProjSpace.π K r
  have hπ : π = closedSubschemeι G b V ≫ structureMap G b :=
    closedSubschemeVeroneseEmbedding_over G b D hD c V
  letI := closedSubschemeVeroneseEmbedding_isClosedImmersion G b D hD c V
  letI : IsProper π := hπ.symm ▸ closedSubscheme_isProper G b V
  obtain ⟨n₀, hn₀⟩ := SchemeEuler.eventually_euler_tensorPow_eq_sections π L
    (twistSheaf_isInvertible φ 1) r (presentation φ) (presentation_isFinite φ)
  obtain ⟨n₁, hn₁⟩ := eventually_veronese_sections_finrank_eq_hilbertFunction G b D hD c V
  refine ⟨max n₀ n₁, fun n hn U => ?_⟩
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π (L.tensorPow n) ⊤
  obtain ⟨e⟩ := tensorPow_sections_equiv_over (presentation φ) n ⊤
  have hχ := hn₀ n (le_trans (le_max_left _ _) hn) U
  have he : Module.finrank K Γ(L.tensorPow n, ⊤) =
      Module.finrank K (ProjSpace.twistObj π φ n ⊤) := e.finrank_eq
  have hdim : Module.finrank K (ProjSpace.twistObj π φ n ⊤) =
      Hilbert.hilbertFunction K G.ambient.factorCount G.ambient.ambientDimension
        (G.ambient.vanishingIdeal (Subtype.val '' V)) (fun i => n * D i) :=
    hn₁ n (le_trans (le_max_right _ _) hn)
  have hresult := hχ.trans (congrArg (fun m : ℕ => (m : ℤ)) (he.trans hdim))
  exact (congrArg (fun θ =>
    (OModulePresheaf.ofModules θ (L.tensorPow n)).eulerChar U) hπ).symm.trans hresult

end PhilipponMultiplicity.ClosureScheme
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProductTwistEulerHilbert

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section

namespace PhilipponMultiplicity.ProductHyperplanes
open AlgebraicGeometry CategoryTheory
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type u} [Field K] {X : Scheme.{u}} {ι : Type} [Fintype ι]
    (N : ι → ℕ)
    (φ : ∀ i, X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N i + 1)) K))

theorem twist_nsmul_iso (D : ι → ℕ) (n : ℕ) :
    Nonempty (twist N φ (n • D) ≅ (twist N φ D).tensorPow n) := by
  apply toSkeleton_eq_toSkeleton_iff.mp
  rw [tensorPow_class]
  exact (degreeClass N φ).map_pow (Multiplicative.ofAdd D) n

end PhilipponMultiplicity.ProductHyperplanes

namespace PhilipponMultiplicity.ClosureScheme
open AlgebraicGeometry CategoryTheory MvPolynomial ProductHyperplanes ProjectiveTwistSheaf
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] (G : EmbeddedGroupProduct K) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension (fun _ => 1)))
    (D : G.FactorIndex → ℕ) (hD : ∀ i, 1 ≤ D i) (V : Set (groupProjectiveClosure G))
attribute [local instance] MvPolynomial.gradedAlgebra

include hD in

theorem eventually_productTwist_tensorPow_euler_eq_hilbertFunction :
    let L := twist G.ambient.ambientDimension (closedSubschemeFactorMap G b V) D
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ U : (closedSubscheme G b V).OrderedAffineCover,
      (OModulePresheaf.ofModules (closedSubschemeι G b V ≫ structureMap G b)
        (L.tensorPow n)).eulerChar U =
        (Hilbert.hilbertFunction K G.ambient.factorCount G.ambient.ambientDimension
          (G.ambient.vanishingIdeal (Subtype.val '' V)) (fun i => n * D i) : ℤ) := by
  letI := closedSubscheme_isReduced G b V
  letI := closedSubschemeι_isClosedImmersion G b V
  obtain ⟨r, c, hc⟩ := Hilbert.SegreVeronese.exists_monomial_coordinate_basis G.ambient D
  obtain ⟨e⟩ := productTwist_veronese_iso G b D hD c (closedSubschemeι G b V) hc
  obtain ⟨n₀, hn₀⟩ := eventually_veronese_euler_eq_hilbertFunction G b D hD c V
  refine ⟨n₀, fun n hn U => ?_⟩
  have he := toSkeleton_eq_toSkeleton_iff.mpr ⟨e⟩
  have hepow : toSkeleton ((twist G.ambient.ambientDimension
      (closedSubschemeFactorMap G b V) D).tensorPow n) =
      toSkeleton ((twistSheaf (closedSubschemeVeroneseEmbedding G b D hD c V) 1).tensorPow n) := by
    rw [tensorPow_class, tensorPow_class]
    exact congrArg (fun s => s ^ n) he
  obtain ⟨en⟩ := toSkeleton_eq_toSkeleton_iff.mp hepow
  exact (SchemeEuler.euler_iso _ en U).trans (hn₀ n hn U)

include hD in

theorem eventually_productTwist_euler_eq_hilbertFunction :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ U : (closedSubscheme G b V).OrderedAffineCover,
      (OModulePresheaf.ofModules (closedSubschemeι G b V ≫ structureMap G b)
        (twist G.ambient.ambientDimension (closedSubschemeFactorMap G b V)
          (fun i => n * D i))).eulerChar U =
        (Hilbert.hilbertFunction K G.ambient.factorCount G.ambient.ambientDimension
          (G.ambient.vanishingIdeal (Subtype.val '' V)) (fun i => n * D i) : ℤ) := by
  obtain ⟨n₀, hn₀⟩ := eventually_productTwist_tensorPow_euler_eq_hilbertFunction G b D hD V
  refine ⟨n₀, fun n hn U => ?_⟩
  obtain ⟨e⟩ := twist_nsmul_iso G.ambient.ambientDimension (closedSubschemeFactorMap G b V) D n
  exact (SchemeEuler.euler_iso _ e U).trans (hn₀ n hn U)

end PhilipponMultiplicity.ClosureScheme
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponEulerSchemeIsomorphism

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.SchemeEuler
open AlgebraicGeometry CategoryTheory
universe u
variable {R : Type u} [CommRing R] [Nontrivial R] {X : Scheme.{u}} {π : X ⟶ Spec (.of R)}

theorem cechFinrank_eq_zero_of_card_le (F : OModulePresheaf π)
    (U : X.OrderedAffineCover) (n : ℕ) (hn : Fintype.card U.ι ≤ n) :
    F.cechFinrank U n = 0 := by
  have hidx : IsEmpty (U.Idx n) := ⟨fun s => by
    have h := Fintype.card_le_of_injective s.val s.property.injective
    rw [Fintype.card_fin] at h
    omega⟩
  cases n with
  | zero =>
      letI := hidx
      exact Module.finrank_zero_of_subsingleton
  | succ n =>
      letI := hidx
      exact Module.finrank_zero_of_subsingleton

theorem euler_eq_sum_range_of_card_le (F : OModulePresheaf π)
    (U : X.OrderedAffineCover) (n : ℕ) (hn : Fintype.card U.ι ≤ n) :
    F.eulerChar U = ∑ i ∈ Finset.range n, (-1 : ℤ) ^ i * (F.cechFinrank U i : ℤ) := by
  rw [OModulePresheaf.eulerChar_def]
  apply Finset.sum_subset (Finset.range_mono hn)
  intro i hi hin
  have hbound : Fintype.card U.ι ≤ i := by simpa only [Finset.mem_range, not_lt] using hin
  rw [cechFinrank_eq_zero_of_card_le F U i hbound, Nat.cast_zero, mul_zero]

theorem euler_pullback_iso {Y : Scheme.{u}} (πY : Y ⟶ Spec (.of R))
    [IsSeparated πY] (f : X ⟶ Y) [IsIso f] (M : Y.Modules)
    (hM : Scheme.Modules.IsInvertible M) (U : X.OrderedAffineCover)
    (W : Y.OrderedAffineCover) :
    (OModulePresheaf.ofModules (f ≫ πY) ((Scheme.Modules.pullback f).obj M)).eulerChar U =
      (OModulePresheaf.ofModules πY M).eulerChar W := by
  let n := max (Fintype.card U.ι) (Fintype.card W.ι)
  rw [euler_eq_sum_range_of_card_le _ U n (le_max_left _ _),
    euler_eq_sum_range_of_card_le _ W n (le_max_right _ _)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [OModulePresheaf.cechFinrank_ofModules_pullback_eq_of_isIso πY f M hM U W i]

theorem euler_pullback_iso_over {Y : Scheme.{u}} (πX : X ⟶ Spec (.of R))
    (πY : Y ⟶ Spec (.of R)) [IsSeparated πY] (f : X ⟶ Y) [IsIso f]
    (hf : f ≫ πY = πX) (M : Y.Modules) (hM : Scheme.Modules.IsInvertible M)
    (U : X.OrderedAffineCover) (W : Y.OrderedAffineCover) :
    (OModulePresheaf.ofModules πX ((Scheme.Modules.pullback f).obj M)).eulerChar U =
      (OModulePresheaf.ofModules πY M).eulerChar W := by
  exact (congrArg (fun θ =>
    (OModulePresheaf.ofModules θ ((Scheme.Modules.pullback f).obj M)).eulerChar U) hf).symm.trans
      (euler_pullback_iso πY f M hM U W)

end PhilipponMultiplicity.SchemeEuler
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponClosureSubschemeTranslations

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity
open AlgebraicGeometry CategoryTheory Topology

def subschemeIsoOfMapEq {X Y : Scheme} (I : X.IdealSheafData) (J : Y.IdealSheafData)
    (e : X ≅ Y) (h : I.map e.hom = J) : I.subscheme ≅ J.subscheme where
  hom := Scheme.IdealSheafData.subschemeMap I J e.hom h.ge
  inv := Scheme.IdealSheafData.subschemeMap J I e.inv (by
    rw [← h, ← Scheme.IdealSheafData.map_comp, e.hom_inv_id,
      Scheme.IdealSheafData.map_id])
  hom_inv_id := by
    apply (cancel_mono I.subschemeι).mp
    simp only [Category.assoc, Scheme.IdealSheafData.subschemeMap_subschemeι,
      Scheme.IdealSheafData.subschemeMap_subschemeι_assoc,
      e.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono J.subschemeι).mp
    simp only [Category.assoc, Scheme.IdealSheafData.subschemeMap_subschemeι,
      Scheme.IdealSheafData.subschemeMap_subschemeι_assoc,
      e.inv_hom_id, Category.comp_id, Category.id_comp]

@[reassoc (attr := simp)]
theorem subschemeIsoOfMapEq_hom_ι {X Y : Scheme}
    (I : X.IdealSheafData) (J : Y.IdealSheafData)
    (e : X ≅ Y) (h : I.map e.hom = J) :
    (subschemeIsoOfMapEq I J e h).hom ≫ J.subschemeι = I.subschemeι ≫ e.hom :=
  Scheme.IdealSheafData.subschemeMap_subschemeι I J e.hom h.ge

namespace ClosureScheme
universe u
variable {K : Type u} [Field K] (G : EmbeddedGroupProduct K) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension (fun _ => 1)))
    (t : groupProjectiveClosure G ≃ groupProjectiveClosure G)
    (e : scheme G b ≅ scheme G b)
    (he : ∀ x, e.hom (point G b x) = point G b (t x))

include he in
theorem closedLocus_image (V : Set (groupProjectiveClosure G)) :
    closedLocus G b (t '' V) =
      TopologicalSpace.Closeds.closure (e.hom '' (closedLocus G b V : Set (scheme G b))) := by
  apply TopologicalSpace.Closeds.ext
  change closure (point G b '' (t '' V)) = closure (e.hom '' closure (point G b '' V))
  have hcl : e.hom '' closure (point G b '' V) = closure (e.hom '' (point G b '' V)) :=
    e.hom.homeomorph.image_closure _
  rw [hcl, closure_closure]
  congr 1
  rw [← Set.image_comp, ← Set.image_comp]
  congr 1
  funext x
  exact (he x).symm

def closedSubschemeTranslation (V : Set (groupProjectiveClosure G)) :
    closedSubscheme G b V ≅ closedSubscheme G b (t '' V) :=
  subschemeIsoOfMapEq
    (Scheme.IdealSheafData.vanishingIdeal (closedLocus G b V))
    (Scheme.IdealSheafData.vanishingIdeal (closedLocus G b (t '' V))) e (by
      rw [Scheme.IdealSheafData.map_vanishingIdeal, closedLocus_image G b t e he V])

@[reassoc (attr := simp)]
theorem closedSubschemeTranslation_hom_ι (V : Set (groupProjectiveClosure G)) :
    (closedSubschemeTranslation G b t e he V).hom ≫ closedSubschemeι G b (t '' V) =
      closedSubschemeι G b V ≫ e.hom :=
  subschemeIsoOfMapEq_hom_ι _ _ _ _

theorem closedSubschemeTranslation_over (V : Set (groupProjectiveClosure G))
    (hπ : e.hom ≫ structureMap G b = structureMap G b) :
    (closedSubschemeTranslation G b t e he V).hom ≫
        (closedSubschemeι G b (t '' V) ≫ structureMap G b) =
      closedSubschemeι G b V ≫ structureMap G b := by
  rw [← Category.assoc, closedSubschemeTranslation_hom_ι, Category.assoc, hπ]

end ClosureScheme
end PhilipponMultiplicity

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponClosureTranslationEuler

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ClosureScheme
open AlgebraicGeometry CategoryTheory
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] (G : EmbeddedGroupProduct K) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension (fun _ => 1)))
    (t : groupProjectiveClosure G ≃ groupProjectiveClosure G)
    (e : scheme G b ≅ scheme G b)
    (he : ∀ x, e.hom (point G b x) = point G b (t x))

def translatedRestrictionIso (V : Set (groupProjectiveClosure G)) (M : (scheme G b).Modules) :
    (Scheme.Modules.pullback (closedSubschemeι G b V ≫ e.hom)).obj M ≅
      (Scheme.Modules.pullback (closedSubschemeTranslation G b t e he V).hom).obj
        ((Scheme.Modules.pullback (closedSubschemeι G b (t '' V))).obj M) :=
  (Scheme.Modules.pullbackCongr (closedSubschemeTranslation_hom_ι G b t e he V).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (closedSubschemeTranslation G b t e he V).hom
      (closedSubschemeι G b (t '' V))).app M).symm

include he in

theorem translatedRestriction_euler (hπ : e.hom ≫ structureMap G b = structureMap G b)
    (V : Set (groupProjectiveClosure G)) (M : (scheme G b).Modules)
    (hM : Scheme.Modules.IsInvertible M)
    (U : (closedSubscheme G b V).OrderedAffineCover)
    (W : (closedSubscheme G b (t '' V)).OrderedAffineCover) :
    (OModulePresheaf.ofModules (closedSubschemeι G b V ≫ structureMap G b)
      ((Scheme.Modules.pullback (closedSubschemeι G b V ≫ e.hom)).obj M)).eulerChar U =
    (OModulePresheaf.ofModules (closedSubschemeι G b (t '' V) ≫ structureMap G b)
      ((Scheme.Modules.pullback (closedSubschemeι G b (t '' V))).obj M)).eulerChar W := by
  letI := closedSubscheme_isProper G b (t '' V)
  refine (SchemeEuler.euler_iso _ (translatedRestrictionIso G b t e he V M) U).trans ?_
  exact SchemeEuler.euler_pullback_iso_over _ _
    (closedSubschemeTranslation G b t e he V).hom
    (closedSubschemeTranslation_over G b t e he V hπ) _
    (hM.pullback (closedSubschemeι G b (t '' V))) U W

end PhilipponMultiplicity.ClosureScheme
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponTranslatedProductHilbert

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ClosureScheme
open AlgebraicGeometry CategoryTheory ProductHyperplanes
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] (G : EmbeddedGroupProduct K) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension (fun _ => 1)))
    (t : groupProjectiveClosure G ≃ groupProjectiveClosure G)
    (e : scheme G b ≅ scheme G b)
    (he : ∀ x, e.hom (point G b x) = point G b (t x))
    (hπ : e.hom ≫ structureMap G b = structureMap G b)
    (D : G.FactorIndex → ℕ) (hD : ∀ i, 1 ≤ D i)
    (V : Set (groupProjectiveClosure G))

include he hπ hD in

theorem eventually_translated_productTwist_euler_eq_hilbertFunction :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ U : (closedSubscheme G b V).OrderedAffineCover,
      (OModulePresheaf.ofModules (closedSubschemeι G b V ≫ structureMap G b)
        ((Scheme.Modules.pullback (closedSubschemeι G b V ≫ e.hom)).obj
          (twist G.ambient.ambientDimension (factorMap G b) (fun i => n * D i)))).eulerChar U =
        (Hilbert.hilbertFunction K G.ambient.factorCount G.ambient.ambientDimension
          (G.ambient.vanishingIdeal (Subtype.val '' (t '' V))) (fun i => n * D i) : ℤ) := by
  obtain ⟨n₀, hn₀⟩ := eventually_productTwist_euler_eq_hilbertFunction G b D hD (t '' V)
  refine ⟨n₀, fun n hn U => ?_⟩
  let W := closedSubschemeOrderedCover G b (t '' V)
  obtain ⟨eW⟩ := twist_pullback_iso G.ambient.ambientDimension (factorMap G b)
    (fun i => n * D i) (closedSubschemeι G b (t '' V))
  exact (translatedRestriction_euler G b t e he hπ V _
    (twist_isInvertible G.ambient.ambientDimension (factorMap G b) _) U W).trans
      ((SchemeEuler.euler_iso _ eW W).trans (hn₀ n hn W))

end PhilipponMultiplicity.ClosureScheme
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponClosureTwistLattice

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section

namespace PhilipponMultiplicity.ClosureTwistLattice
open AlgebraicGeometry CategoryTheory
open ClosureScheme ProductHyperplanes InvertibleClassLattice
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] (G : EmbeddedGroupProduct K) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension (fun _ => 1)))
    (T : G.Point → (scheme G b ≅ scheme G b))

abbrev Lattice := FreeTwistAction.Lattice G.Point G.FactorIndex

def generator (s : G.Point × G.FactorIndex) : (scheme G b).Modules :=
  (Scheme.Modules.pullback (T (-s.1)).hom).obj (factorHyperplane G b s.2)

theorem generator_isInvertible (s : G.Point × G.FactorIndex) :
    Scheme.Modules.IsInvertible (generator G b T s) :=
  (factorHyperplane_isInvertible G b s.2).pullback (T (-s.1)).hom

abbrev classes : Multiplicative (Lattice G) →* Skeleton (scheme G b).Modules :=
  classHom (generator G b T) (generator_isInvertible G b T)

abbrev bundle (l : Lattice G) : (scheme G b).Modules :=
  representative (generator G b T) (generator_isInvertible G b T) l

theorem bundle_class (l : Lattice G) :
    toSkeleton (bundle G b T l) = classes G b T (Multiplicative.ofAdd l) :=
  representative_class _ _ l

theorem bundle_isInvertible (l : Lattice G) : Scheme.Modules.IsInvertible (bundle G b T l) :=
  representative_isInvertible _ _ l

variable (hzero : T 0 = Iso.refl _) (hadd : ∀ g h, T (g + h) = T h ≪≫ T g)

include hadd in

theorem classes_action (g : G.Point) (l : Lattice G) :
    classes G b T (Multiplicative.ofAdd (FreeTwistAction.action G.Point G.FactorIndex
      (Multiplicative.ofAdd g) l)) =
      pullbackClass (T (-g)).hom (classes G b T (Multiplicative.ofAdd l)) := by
  let q := unitHom (generator G b T) (generator_isInvertible G b T)
  let a := FreeTwistAction.action G.Point G.FactorIndex (Multiplicative.ofAdd g)
  have h : q.comp a.toAddMonoidHom.toMultiplicative =
      (Units.map (pullbackClass (T (-g)).hom)).comp q := by
    apply MonoidHom.toAdditiveRight.injective
    apply FreeAbelianGroup.lift_ext
    rintro ⟨h, i⟩
    apply Units.ext
    change classes G b T (Multiplicative.ofAdd (a (FreeAbelianGroup.of (h, i)))) =
      pullbackClass (T (-g)).hom (classes G b T (Multiplicative.ofAdd (FreeAbelianGroup.of (h, i))))
    rw [FreeTwistAction.action_generator]
    rw [classHom_generator, classHom_generator, pullbackClass_toSkeleton]
    apply toSkeleton_eq_toSkeleton_iff.mpr
    have hc : (T (-(g + h))).hom = (T (-g)).hom ≫ (T (-h)).hom := by
      have h := congrArg Iso.hom (hadd (-h) (-g))
      simpa only [Iso.trans_hom, neg_add_rev] using h
    exact ⟨(Scheme.Modules.pullbackCongr hc).app (factorHyperplane G b i) ≪≫
      ((Scheme.Modules.pullbackComp (T (-g)).hom (T (-h)).hom).app (factorHyperplane G b i)).symm⟩
  exact congrArg Units.val (DFunLike.congr_fun h (Multiplicative.ofAdd l))

include hzero in
theorem classes_factor (i : G.FactorIndex) :
    classes G b T (Multiplicative.ofAdd (FreeTwistAction.factor G.Point G.FactorIndex i)) =
      toSkeleton (factorHyperplane G b i) := by
  rw [FreeTwistAction.factor, classHom_generator]
  apply toSkeleton_eq_toSkeleton_iff.mpr
  dsimp only [generator]
  simp only [neg_zero, hzero, Iso.refl_hom]
  exact ⟨(Scheme.Modules.pullbackId _).app _⟩

include hzero in
theorem classes_degree (D : G.FactorIndex → ℕ) :
    classes G b T (Multiplicative.ofAdd
      (∑ i, (D i : ℤ) • FreeTwistAction.factor G.Point G.FactorIndex i)) =
      toSkeleton (twist G.ambient.ambientDimension (factorMap G b) D) := by
  rw [ofAdd_sum, map_prod, twist_class]
  apply Finset.prod_congr rfl
  intro i _
  rw [natCast_zsmul, ofAdd_nsmul, map_pow, classes_factor G b T hzero]

def restriction (V : Set (groupProjectiveClosure G)) (l : Lattice G) :
    (closedSubscheme G b V).Modules :=
  (Scheme.Modules.pullback (closedSubschemeι G b V)).obj (bundle G b T l)

def euler (V : Set (groupProjectiveClosure G)) (l : Lattice G) : ℤ :=
  (OModulePresheaf.ofModules (closedSubschemeι G b V ≫ structureMap G b)
    (restriction G b T V l)).eulerChar (closedSubschemeOrderedCover G b V)

theorem euler_polynomial (V : Set (groupProjectiveClosure G))
    (hV : letI := G.ambient.zariskiTopology; IsClosed V) :
    PolynomialFunctionFiltration.IsPolynomialAtMost (euler G b T V)
      (SectionThree.locusDimension G.ambient (Subtype.val '' V)) := by
  letI := closedSubscheme_isProper G b V
  apply SchemeEuler.euler_function_polynomial _ _
    ((pullbackClass (closedSubschemeι G b V)).comp (classes G b T))
    (restriction G b T V)
  · intro l
    exact (bundle_isInvertible G b T l).pullback (closedSubschemeι G b V)
  · intro l
    exact (pullbackClass_toSkeleton (closedSubschemeι G b V) (bundle G b T l)).symm.trans
      (congrArg (pullbackClass (closedSubschemeι G b V)) (bundle_class G b T l))
  · exact closedSubscheme_dimension_le G b V hV

end PhilipponMultiplicity.ClosureTwistLattice
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponClosureTwistLatticeHilbert

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ClosureTwistLattice
open AlgebraicGeometry CategoryTheory
open ClosureScheme ProductHyperplanes
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] (G : EmbeddedGroupProduct K) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension (fun _ => 1)))
    (T : G.Point → (scheme G b ≅ scheme G b))
    (hzero : T 0 = Iso.refl _) (hadd : ∀ g h, T (g + h) = T h ≪≫ T g)

def ray (g : G.Point) (D : G.FactorIndex → ℕ) (n : ℕ) : Lattice G :=
  n • FreeTwistAction.action G.Point G.FactorIndex (Multiplicative.ofAdd (-g))
    (∑ i, (D i : ℤ) • FreeTwistAction.factor G.Point G.FactorIndex i)

include hzero hadd in
theorem classes_ray (g : G.Point) (D : G.FactorIndex → ℕ) (n : ℕ) :
    classes G b T (Multiplicative.ofAdd (ray G g D n)) =
      pullbackClass (T g).hom
        (toSkeleton (twist G.ambient.ambientDimension (factorMap G b) (fun i => n * D i))) := by
  unfold ray
  rw [← map_nsmul, classes_action G b T hadd, neg_neg]
  congr 1
  rw [ofAdd_nsmul, map_pow, classes_degree G b T hzero]
  have he := toSkeleton_eq_toSkeleton_iff.mpr
    (twist_nsmul_iso G.ambient.ambientDimension (factorMap G b) D n)
  exact ((he.trans (tensorPow_class _ n))).symm

include hzero hadd in

theorem restriction_ray_iso (V : Set (groupProjectiveClosure G))
    (g : G.Point) (D : G.FactorIndex → ℕ) (n : ℕ) :
    Nonempty (restriction G b T V (ray G g D n) ≅
      (Scheme.Modules.pullback (closedSubschemeι G b V ≫ (T g).hom)).obj
        (twist G.ambient.ambientDimension (factorMap G b) (fun i => n * D i))) := by
  apply toSkeleton_eq_toSkeleton_iff.mp
  change toSkeleton ((Scheme.Modules.pullback (closedSubschemeι G b V)).obj _) = _
  rw [← pullbackClass_toSkeleton, bundle_class, classes_ray G b T hzero hadd]
  rw [pullbackClass_toSkeleton, pullbackClass_toSkeleton]
  exact congr_toSkeleton_of_iso ((Scheme.Modules.pullbackComp
    (closedSubschemeι G b V) (T g).hom).app _)

variable (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
    (hpoint : ∀ g x, (T g).hom (point G b x) = point G b (τ g x))
    (hπ : ∀ g, (T g).hom ≫ structureMap G b = structureMap G b)

include hzero hadd hpoint hπ in

theorem eventually_euler_ray_eq_hilbertFunction
    (V : Set (groupProjectiveClosure G)) (g : G.Point)
    (D : G.FactorIndex → ℕ) (hD : ∀ i, 1 ≤ D i) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      euler G b T V (ray G g D n) =
        (Hilbert.hilbertFunction K G.ambient.factorCount G.ambient.ambientDimension
          (G.ambient.vanishingIdeal (Subtype.val '' (τ g '' V))) (fun i => D i * n) : ℤ) := by
  obtain ⟨n₀, hn₀⟩ := eventually_translated_productTwist_euler_eq_hilbertFunction G b
    (τ g) (T g) (hpoint g) (hπ g) D hD V
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨e⟩ := restriction_ray_iso G b T hzero hadd V g D n
  have h := (SchemeEuler.euler_iso (closedSubschemeι G b V ≫ structureMap G b) e
    (closedSubschemeOrderedCover G b V)).trans (hn₀ n hn _)
  simpa only [euler, Nat.mul_comm] using h

end PhilipponMultiplicity.ClosureTwistLattice
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponClosureTwistEulerAction

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ClosureTwistLattice
open AlgebraicGeometry CategoryTheory
open ClosureScheme ProductHyperplanes
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] (G : EmbeddedGroupProduct K) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension (fun _ => 1)))
    (T : G.Point → (scheme G b ≅ scheme G b))
    (hadd : ∀ g h, T (g + h) = T h ≪≫ T g)

include hadd in
theorem bundle_action_iso (g : G.Point) (l : Lattice G) :
    Nonempty (bundle G b T (FreeTwistAction.action G.Point G.FactorIndex (Multiplicative.ofAdd g) l) ≅
      (Scheme.Modules.pullback (T (-g)).hom).obj (bundle G b T l)) := by
  apply toSkeleton_eq_toSkeleton_iff.mp
  rw [bundle_class, ← pullbackClass_toSkeleton, bundle_class]
  exact classes_action G b T hadd g l

variable (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
    (hpoint : ∀ g x, (T g).hom (point G b x) = point G b (τ g x))
    (hπ : ∀ g, (T g).hom ≫ structureMap G b = structureMap G b)

include hadd hpoint hπ in

theorem euler_action (V : Set (groupProjectiveClosure G)) (g : G.Point) (l : Lattice G) :
    euler G b T V (FreeTwistAction.action G.Point G.FactorIndex (Multiplicative.ofAdd g) l) =
      euler G b T (τ (-g) '' V) l := by
  obtain ⟨e⟩ := bundle_action_iso G b T hadd g l
  let eV := (Scheme.Modules.pullback (closedSubschemeι G b V)).mapIso e ≪≫
    (Scheme.Modules.pullbackComp (closedSubschemeι G b V) (T (-g)).hom).app (bundle G b T l)
  exact (SchemeEuler.euler_iso _ eV (closedSubschemeOrderedCover G b V)).trans
    (translatedRestriction_euler G b (τ (-g)) (T (-g)) (hpoint (-g)) (hπ (-g)) V
      (bundle G b T l) (bundle_isInvertible G b T l)
      (closedSubschemeOrderedCover G b V) (closedSubschemeOrderedCover G b (τ (-g) '' V)))

end PhilipponMultiplicity.ClosureTwistLattice
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponClosureNumericalQuotient

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ClosureTwistLattice
open AlgebraicGeometry CategoryTheory
open ClosureScheme
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] (G : EmbeddedGroupProduct K) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension (fun _ => 1)))
    (T : G.Point → (scheme G b ≅ scheme G b))

def numericalKernel : Submodule ℤ (Lattice G) where
  carrier := {l | ∀ V : Set (groupProjectiveClosure G), Function.Periodic (euler G b T V) l}
  zero_mem' := fun _ => Function.periodic_with_period_zero _
  add_mem' hl hm V := (hl V).add_period (hm V)
  smul_mem' n _ hl V := (hl V).zsmul n

abbrev NumericalQuotient := Lattice G ⧸ numericalKernel G b T

def numericalMap : Lattice G →ₗ[ℤ] NumericalQuotient G b T := (numericalKernel G b T).mkQ

theorem numericalMap_surjective : Function.Surjective (numericalMap G b T) :=
  (numericalKernel G b T).mkQ_surjective

theorem numericalMap_ker : LinearMap.ker (numericalMap G b T) = numericalKernel G b T :=
  Submodule.ker_mkQ _

variable (hadd : ∀ g h, T (g + h) = T h ≪≫ T g)
    (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
    (hpoint : ∀ g x, (T g).hom (point G b x) = point G b (τ g x))
    (hπ : ∀ g, (T g).hom ≫ structureMap G b = structureMap G b)

include hadd hpoint hπ in

theorem numericalKernel_stable (g : G.Point) (l : Lattice G)
    (hl : l ∈ numericalKernel G b T) :
    FreeTwistAction.action G.Point G.FactorIndex (Multiplicative.ofAdd g) l ∈
      numericalKernel G b T := by
  intro V x
  let a := FreeTwistAction.action G.Point G.FactorIndex (Multiplicative.ofAdd g)
  have h := euler_action G b T hadd τ hpoint hπ
  calc
    euler G b T V (x + a l) = euler G b T V (a (a.symm x + l)) := by
      rw [map_add, a.apply_symm_apply]
    _ = euler G b T (τ (-g) '' V) (a.symm x + l) := h V g _
    _ = euler G b T (τ (-g) '' V) (a.symm x) := hl _ _
    _ = euler G b T V (a (a.symm x)) := (h V g _).symm
    _ = euler G b T V x := by rw [a.apply_symm_apply]

end PhilipponMultiplicity.ClosureTwistLattice
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponKernelEulerFamilies

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section

namespace PhilipponMultiplicity.KernelEulerFamilies
open CategoryTheory
universe u v

variable {L : Type u} [AddCommGroup L] [Module ℤ L]
    {A : Type v} [AddCommGroup A] [Module ℤ A]
    {C : Type u} (q : L →ₗ[ℤ] A)
    (σ : Multiplicative L →* Equiv.Perm C) (e : C → ℤ)

theorem exists_families (K : Type u) [Field K]
    (hinvariant : ∀ l, q l = 0 → ∀ a, e (σ (Multiplicative.ofAdd l) a) = e a) :
    ∃ (ι : Type u) (X : ι → Type u) (top : ∀ i, TopologicalSpace (X i))
      (s t : ∀ i, X i) (p : ∀ i, X i → L),
      (∀ i, @ConnectedSpace (X i) (top i)) ∧
      (∀ i a x, ∃ U : Set (X i), @IsOpen (X i) (top i) U ∧ x ∈ U ∧
        ∃ r : ℤ → ℕ, Function.HasFiniteSupport r ∧
        ∃ V : U → CochainComplex (ModuleCat.{u} K) ℤ,
          (∀ z j, Module.Finite K ((V z).X j)) ∧
          (∀ z j, Module.finrank K ((V z).X j) = r j) ∧
          (∀ z : U, (e (σ (Multiplicative.ofAdd (p i z.val)) a) : ℚ) =
            ((V z).homologyEulerChar : ℚ))) ∧
      LinearMap.ker q =
        Submodule.span ℤ (Set.range (fun i => p i (t i) - p i (s i))) := by
  let X := ULift.{u} Bool
  letI : TopologicalSpace X := ⊤
  let p : LinearMap.ker q → X → L := fun l b => if b.down then l.val else 0
  have hp (l : LinearMap.ker q) (a : C) (b : X) :
      e (σ (Multiplicative.ofAdd (p l b)) a) = e a := by
    cases b with
    | up b =>
      cases b
      · simp [p]
      · exact hinvariant l.val l.property a
  have hconn : ConnectedSpace X := by
    apply connectedSpace_iff_univ.mpr
    rw [← closure_indiscrete (Set.singleton_nonempty (ULift.up false : X))]
    exact isConnected_singleton.closure
  refine ⟨LinearMap.ker q, (fun _ => X), (fun _ => ⊤),
    (fun _ => ULift.up false), (fun _ => ULift.up true), p,
    (fun _ => hconn), ?_, ?_⟩
  · intro i a
    have hlocal : IsLocallyConstant (fun x => e (σ (Multiplicative.ofAdd (p i x)) a)) := by
      have heq : (fun x => e (σ (Multiplicative.ofAdd (p i x)) a)) =
          (fun _ : X => e a) := funext (hp i a)
      rw [heq]
      exact IsLocallyConstant.const _
    exact ComplexEuler.local_complexes_of_integer_locally_constant K _ hlocal
  · have heq : Set.range (fun i : LinearMap.ker q =>
        p i (ULift.up true) - p i (ULift.up false)) = (LinearMap.ker q : Set L) := by
      simp only [p, Bool.false_eq_true, ↓reduceIte, sub_zero]
      exact Subtype.range_coe
    rw [heq, Submodule.span_eq]

end PhilipponMultiplicity.KernelEulerFamilies

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponFilteredTwistLocalModel

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section

namespace PhilipponMultiplicity.FilteredTwistGenerators
open CategoryTheory
universe u v
variable {L : Type u} [AddCommGroup L] [Module ℤ L]
    {A : Type v} [AddCommGroup A] [Module ℤ A]
    {B : Type u} [AddCommGroup B] [Module ℤ B]

theorem exists_local_model (K : Type u) [Field K]
    (q : L →ₗ[ℤ] A) (β : Multiplicative L →* (B ≃ₗ[ℤ] B)) (χ : B →ₗ[ℤ] ℤ)
    (F : ℕ → Submodule ℤ B) (hzero : F 0 = ⊥)
    (hstable : ∀ l n b, b ∈ F n → β l b ∈ F n)
    (hdrop : ∀ n l b, b ∈ F (n + 1) → β (Multiplicative.ofAdd l) b - b ∈ F n)
    (hinvariant : ∀ l, q l = 0 → ∀ b, χ (β (Multiplicative.ofAdd l) b) = χ b) :
    ∃ (C : Type u) (σ : Multiplicative L →* Equiv.Perm C)
      (d : C → ℕ) (e : C → ℚ) (S : C → C → Option C → Prop),
      (∀ l a b Q, S a b Q → S (σ l a) (σ l b) (Q.map (σ l))) ∧
      (∀ a b Q, S a b Q → e b = e a + Q.elim 0 e) ∧
      (∀ l a, ∃ (k : C) (Q Q' : Option C),
        S k a Q ∧ S k (σ (Multiplicative.ofAdd l) a) Q' ∧
        (∀ b ∈ Q, d b < d a) ∧ (∀ b ∈ Q', d b < d a)) ∧
      (∃ (ι : Type u) (X : ι → Type u) (top : ∀ i, TopologicalSpace (X i))
        (s t : ∀ i, X i) (p : ∀ i, X i → L),
        (∀ i, @ConnectedSpace (X i) (top i)) ∧
        (∀ i a x, ∃ U : Set (X i), @IsOpen (X i) (top i) U ∧ x ∈ U ∧
          ∃ r : ℤ → ℕ, Function.HasFiniteSupport r ∧
          ∃ V : U → CochainComplex (ModuleCat.{u} K) ℤ,
            (∀ z j, Module.Finite K ((V z).X j)) ∧
            (∀ z j, Module.finrank K ((V z).X j) = r j) ∧
            (∀ z : U, e (σ (Multiplicative.ofAdd (p i z.val)) a) =
              ((V z).homologyEulerChar : ℚ))) ∧
        LinearMap.ker q =
          Submodule.span ℤ (Set.range (fun i => p i (t i) - p i (s i)))) ∧
      ∀ n b, b ∈ F (n + 1) →
        ∃ a : C, d a = n ∧ ∀ l : L,
          e (σ (Multiplicative.ofAdd l) a) = (χ (β (Multiplicative.ofAdd l) b) : ℚ) := by
  refine ⟨Generator F, action β F hstable, Generator.dimension, euler F χ,
    relation F, relation_stable β F hstable, euler_additive F χ,
    common_source β F hstable hzero hdrop, ?_, ?_⟩
  · exact KernelEulerFamilies.exists_families q (action β F hstable)
      (fun a => χ a.value) K (fun l hl a => hinvariant l hl a.value)
  · intro n b hb
    exact ⟨⟨n, b, hb⟩, rfl, fun _ => rfl⟩

end PhilipponMultiplicity.FilteredTwistGenerators

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponNumericalEulerFunctions

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section

namespace PhilipponMultiplicity.NumericalEulerFunctions
open CategoryTheory
universe u v
variable {L : Type u} [AddCommGroup L] [Module ℤ L]
    {A : Type v} [AddCommGroup A] [Module ℤ A] (q : L →ₗ[ℤ] A)

def functions : Submodule ℤ (L → ℤ) where
  carrier := {f | ∀ x y, q x = q y → f x = f y}
  zero_mem' := fun _ _ _ => rfl
  add_mem' := fun hf hg x y h => by simp only [Pi.add_apply, hf x y h, hg x y h]
  smul_mem' := fun r f hf x y h => by simp only [Pi.smul_apply, hf x y h]

theorem shift_mem (l : Multiplicative L) (f : functions q) :
    PolynomialFunctionFiltration.action L l (f : L → ℤ) ∈ functions q := by
  intro x y h
  exact f.property (x + l.toAdd) (y + l.toAdd) (by rw [map_add, map_add, h])

def shiftEquiv (l : Multiplicative L) : functions q ≃ₗ[ℤ] functions q where
  toFun f := ⟨PolynomialFunctionFiltration.action L l f, shift_mem q l f⟩
  invFun f := ⟨PolynomialFunctionFiltration.action L l⁻¹ f, shift_mem q l⁻¹ f⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    change f.val (x + (-l.toAdd) + l.toAdd) = f.val x
    simp
  right_inv f := by
    apply Subtype.ext
    funext x
    change f.val (x + l.toAdd + (-l.toAdd)) = f.val x
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def action : Multiplicative L →* (functions q ≃ₗ[ℤ] functions q) where
  toFun := shiftEquiv q
  map_one' := by
    apply LinearEquiv.ext
    intro f
    apply Subtype.ext
    funext x
    exact congrArg (f : L → ℤ) (add_zero x)
  map_mul' l m := by
    apply LinearEquiv.ext
    intro f
    apply Subtype.ext
    funext x
    exact congrArg (f : L → ℤ) (add_assoc x l.toAdd m.toAdd).symm

def level (n : ℕ) : Submodule ℤ (functions q) :=
  (DifferenceFiltration.level (PolynomialFunctionFiltration.action L) n).comap
    (functions q).subtype

def euler : functions q →ₗ[ℤ] ℤ :=
  (LinearMap.proj 0).comp (functions q).subtype

theorem level_zero : level q 0 = ⊥ := by
  apply bot_unique
  intro f hf
  change f.val ∈ (⊥ : Submodule ℤ (L → ℤ)) at hf
  rw [Submodule.mem_bot] at hf ⊢
  exact Subtype.ext hf

theorem stable (l : Multiplicative L) (n : ℕ) (f : functions q) (hf : f ∈ level q n) :
    action q l f ∈ level q n :=
  DifferenceFiltration.stable (PolynomialFunctionFiltration.action L) l n f hf

theorem difference_mem (n : ℕ) (l : L) (f : functions q) (hf : f ∈ level q (n + 1)) :
    action q (Multiplicative.ofAdd l) f - f ∈ level q n :=
  DifferenceFiltration.difference_mem (PolynomialFunctionFiltration.action L) n l f hf

theorem euler_invariant (l : L) (hl : q l = 0) (f : functions q) :
    euler q (action q (Multiplicative.ofAdd l) f) = euler q f := by
  change f.val (0 + l) = f.val 0
  rw [zero_add]
  exact f.property l 0 (by rw [hl, map_zero])

theorem exists_local_model (K : Type u) [Field K] :
    ∃ (C : Type u) (σ : Multiplicative L →* Equiv.Perm C)
      (d : C → ℕ) (e : C → ℚ) (S : C → C → Option C → Prop),
      (∀ l a b Q, S a b Q → S (σ l a) (σ l b) (Q.map (σ l))) ∧
      (∀ a b Q, S a b Q → e b = e a + Q.elim 0 e) ∧
      (∀ l a, ∃ (k : C) (Q Q' : Option C),
        S k a Q ∧ S k (σ (Multiplicative.ofAdd l) a) Q' ∧
        (∀ b ∈ Q, d b < d a) ∧ (∀ b ∈ Q', d b < d a)) ∧
      (∃ (ι : Type u) (X : ι → Type u) (top : ∀ i, TopologicalSpace (X i))
        (s t : ∀ i, X i) (p : ∀ i, X i → L),
        (∀ i, @ConnectedSpace (X i) (top i)) ∧
        (∀ i a x, ∃ U : Set (X i), @IsOpen (X i) (top i) U ∧ x ∈ U ∧
          ∃ r : ℤ → ℕ, Function.HasFiniteSupport r ∧
          ∃ V : U → CochainComplex (ModuleCat.{u} K) ℤ,
            (∀ z j, Module.Finite K ((V z).X j)) ∧
            (∀ z j, Module.finrank K ((V z).X j) = r j) ∧
            (∀ z : U, e (σ (Multiplicative.ofAdd (p i z.val)) a) =
              ((V z).homologyEulerChar : ℚ))) ∧
        LinearMap.ker q =
          Submodule.span ℤ (Set.range (fun i => p i (t i) - p i (s i)))) ∧
      ∀ (f : L → ℤ) (n : ℕ),
        (∀ x y, q x = q y → f x = f y) →
        PolynomialFunctionFiltration.IsPolynomialAtMost f n →
        ∃ a : C, d a = n ∧ ∀ l : L, e (σ (Multiplicative.ofAdd l) a) = (f l : ℚ) := by
  obtain ⟨C, σ, d, e, S, hS, he, hcommon, hfamilies, hrealize⟩ :=
    FilteredTwistGenerators.exists_local_model K q (action q) (euler q) (level q)
      (level_zero q) (stable q) (difference_mem q) (euler_invariant q)
  refine ⟨C, σ, d, e, S, hS, he, hcommon, hfamilies, ?_⟩
  intro f n hf hp
  obtain ⟨a, ha, hv⟩ := hrealize n ⟨f, hf⟩ (PolynomialFunctionFiltration.mem_level hp)
  refine ⟨a, ha, ?_⟩
  intro l
  rw [hv l]
  change (f (0 + l) : ℚ) = (f l : ℚ)
  rw [zero_add]

end PhilipponMultiplicity.NumericalEulerFunctions

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponClosureLocalComplexReduction

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section

namespace PhilipponMultiplicity.ClosureTwistLattice
open AlgebraicGeometry CategoryTheory
open ClosureScheme
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] (G : EmbeddedGroupProduct K) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension (fun _ => 1)))
    (T : G.Point → (scheme G b ≅ scheme G b))

theorem exists_small_numerical_map [Module.Finite ℤ (NumericalQuotient G b T)] :
    ∃ (A : Type) (_ : AddCommGroup A) (_ : Module ℤ A) (_ : Module.Finite ℤ A)
      (q : Lattice G →ₗ[ℤ] A), Function.Surjective q ∧ LinearMap.ker q = numericalKernel G b T := by
  let A := Module.Finite.repr ℤ (NumericalQuotient G b T)
  let e : A ≃ₗ[ℤ] NumericalQuotient G b T := Module.Finite.reprEquiv ℤ _
  let q := e.symm.toLinearMap.comp (numericalMap G b T)
  refine ⟨A, inferInstance, inferInstance, Module.Finite.equiv e.symm, q,
    e.symm.surjective.comp (numericalMap_surjective G b T), ?_⟩
  ext l
  change e.symm (numericalMap G b T l) = 0 ↔ l ∈ numericalKernel G b T
  rw [map_eq_zero_iff e.symm e.symm.injective]
  exact SetLike.ext_iff.mp (numericalMap_ker G b T) l

end PhilipponMultiplicity.ClosureTwistLattice

namespace PhilipponMultiplicity
open AlgebraicGeometry CategoryTheory ClosureScheme ClosureTwistLattice
universe u

theorem closure_action_local_complex_of_finite_numerical_quotient
    (K : Type u) [Field K] [IsAlgClosed K] (G : EmbeddedGroupProduct K) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension (fun _ => 1)))
    (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
    (T : G.Point → (scheme G b ≅ scheme G b))
    (hzero : T 0 = Iso.refl _) (hadd : ∀ g h, T (g + h) = T h ≪≫ T g)
    (hpoint : ∀ g x, (T g).hom (point G b x) = point G b (τ g x))
    (hπ : ∀ g, (T g).hom ≫ structureMap G b = structureMap G b)
    [Module.Finite ℤ (NumericalQuotient G b T)] :
    ∃ (L : Type u) (_ : AddCommGroup L) (_ : Module ℤ L)
      (A : Type) (_ : AddCommGroup A) (_ : Module ℤ A) (_ : Module.Finite ℤ A)
      (q : L →ₗ[ℤ] A), Function.Surjective q ∧
      ∃ (ρ : Multiplicative G.Point →* (L ≃ₗ[ℤ] L)) (c : G.FactorIndex → L),
        (∀ g x, q x = 0 → q (ρ g x) = 0) ∧
        ∃ (C : Type u) (σ : Multiplicative L →* Equiv.Perm C)
          (d : C → ℕ) (e : C → ℚ) (S : C → C → Option C → Prop),
          (∀ l a b Q, S a b Q → S (σ l a) (σ l b) (Q.map (σ l))) ∧
          (∀ a b Q, S a b Q → e b = e a + Q.elim 0 e) ∧
          (∀ l a, ∃ (k : C) (Q Q' : Option C),
            S k a Q ∧ S k (σ (Multiplicative.ofAdd l) a) Q' ∧
            (∀ b ∈ Q, d b < d a) ∧ (∀ b ∈ Q', d b < d a)) ∧
          (∃ (ι : Type u) (X : ι → Type u) (top : ∀ i, TopologicalSpace (X i))
            (s t : ∀ i, X i) (p : ∀ i, X i → L),
            (∀ i, @ConnectedSpace (X i) (top i)) ∧
            (∀ i a x, ∃ U : Set (X i), @IsOpen (X i) (top i) U ∧ x ∈ U ∧
              ∃ r : ℤ → ℕ, Function.HasFiniteSupport r ∧
              ∃ V : U → CochainComplex (ModuleCat.{u} K) ℤ,
                (∀ z j, Module.Finite K ((V z).X j)) ∧
                (∀ z j, Module.finrank K ((V z).X j) = r j) ∧
                (∀ z : U, e (σ (Multiplicative.ofAdd (p i z.val)) a) =
                  ((V z).homologyEulerChar : ℚ))) ∧
            LinearMap.ker q =
              Submodule.span ℤ (Set.range (fun i => p i (t i) - p i (s i)))) ∧
          ∀ (V : Set (groupProjectiveClosure G)),
            @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V →
            ∃ a : C,
              d a ≤ SectionThree.locusDimension G.ambient (Subtype.val '' V) ∧
              ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
                ∃ N : ℕ, ∀ n ≥ N,
                  e (σ (Multiplicative.ofAdd
                    (n • ρ (Multiplicative.ofAdd (-g)) (∑ i, (D i : ℤ) • c i))) a) =
                    (Hilbert.hilbertFunction K G.ambient.factorCount G.ambient.ambientDimension
                      (G.ambient.vanishingIdeal (Subtype.val '' (τ g '' V)))
                      (fun i => D i * n) : ℚ) := by
  obtain ⟨A, instA, modA, finA, q, hq, hker⟩ := exists_small_numerical_map G b T
  letI := instA
  letI := modA
  letI := finA
  refine ⟨Lattice G, inferInstance, inferInstance, A, instA, modA, finA, q, hq,
    FreeTwistAction.action G.Point G.FactorIndex, FreeTwistAction.factor G.Point G.FactorIndex, ?_, ?_⟩
  · intro g l hl
    have hl' : l ∈ numericalKernel G b T := hker ▸ hl
    have hs := numericalKernel_stable G b T hadd τ hpoint hπ g.toAdd l hl'
    change _ ∈ LinearMap.ker q
    exact hker.symm ▸ hs
  · obtain ⟨C, σ, d, e, S, hS, he, hcommon, hfamily, hrealize⟩ :=
      NumericalEulerFunctions.exists_local_model q K
    refine ⟨C, σ, d, e, S, hS, he, hcommon, hfamily, ?_⟩
    intro V hV
    have hdesc : ∀ x y, q x = q y → ClosureTwistLattice.euler G b T V x =
        ClosureTwistLattice.euler G b T V y := by
      intro x y hxy
      have hmem : x - y ∈ numericalKernel G b T := by
        rw [← hker]
        change q (x - y) = 0
        rw [map_sub, hxy, sub_self]
      have h := hmem V y
      simpa [sub_eq_add_neg, add_left_comm, add_assoc] using h
    obtain ⟨a, ha, hvalue⟩ := hrealize (ClosureTwistLattice.euler G b T V) _ hdesc
      (euler_polynomial G b T V hV)
    refine ⟨a, ha.le, fun g D hD => ?_⟩
    obtain ⟨n₀, hn₀⟩ := eventually_euler_ray_eq_hilbertFunction G b T hzero hadd τ hpoint hπ V g D hD
    refine ⟨n₀, fun n hn => ?_⟩
    rw [hvalue]
    have h := congrArg (fun z : ℤ => (z : ℚ)) (hn₀ n hn)
    exact h.trans (Int.cast_natCast _)

end PhilipponMultiplicity
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponClosureNumericalFinitenessReduction

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section

namespace PhilipponMultiplicity.ClosureTwistLattice
open AlgebraicGeometry CategoryTheory ClosureScheme
universe u

theorem numericalQuotient_finite
    {K : Type u} [Field K] [IsAlgClosed K] (G : EmbeddedGroupProduct K) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension (fun _ => 1)))
    (T : G.Point → (scheme G b ≅ scheme G b)) :
    Module.Finite ℤ (NumericalQuotient G b T) := by
  letI := ClosureScheme.isProper G b
  obtain ⟨A, instA, modA, finA, q, hq, he⟩ :=
    OModulePresheaf.exists_finite_euler_quotient_of_isProper K (structureMap G b)
      (Lattice G) (classes G b T) (bundle G b T)
      (bundle_isInvertible G b T) (bundle_class G b T)
  letI := instA
  letI := modA
  letI := finA
  have hker : LinearMap.ker q ≤ numericalKernel G b T := by
    intro l hl V x
    apply he (x + l) x
    · rw [map_add, LinearMap.mem_ker.mp hl, add_zero]
    · exact closedSubschemeι_isClosedImmersion G b V
  letI : Module.Finite ℤ (Lattice G ⧸ LinearMap.ker q) :=
    Module.Finite.equiv (LinearMap.quotKerEquivOfSurjective q hq).symm
  exact Module.Finite.of_surjective (Submodule.factor hker) (Submodule.factor_surjective hker)

end PhilipponMultiplicity.ClosureTwistLattice
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponClosureLocalComplexSketch
set_option autoImplicit false
open scoped BigOperators Topology
universe u

set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace PhilipponMultiplicity
open AlgebraicGeometry CategoryTheory ClosureScheme

theorem closure_action_has_local_complex_model_reduction_proof
    (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K)
    (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
    (hzero : τ 0 = Equiv.refl _)
    (hadd : ∀ g h, τ (g+h) = (τ h).trans (τ g))
    (hregular : ∀ g, G.ambient.IsRegularAlong G.ambient
      (fun x : groupProjectiveClosure G => x.val) (fun x => (τ g x).val)) :
    ∃ (L : Type u) (_ : AddCommGroup L) (_ : Module ℤ L)
      (A : Type) (_ : AddCommGroup A) (_ : Module ℤ A) (_ : Module.Finite ℤ A)
      (q : L →ₗ[ℤ] A), Function.Surjective q ∧
      ∃ (ρ : Multiplicative G.Point →* (L ≃ₗ[ℤ] L)) (c : G.FactorIndex → L),
        (∀ g x, q x = 0 → q (ρ g x) = 0) ∧
        ∃ (C : Type u) (σ : Multiplicative L →* Equiv.Perm C)
          (d : C → ℕ) (e : C → ℚ) (S : C → C → Option C → Prop),
          (∀ l a b Q, S a b Q → S (σ l a) (σ l b) (Q.map (σ l))) ∧
          (∀ a b Q, S a b Q → e b = e a + Q.elim 0 e) ∧
          (∀ l a, ∃ (k : C) (Q Q' : Option C),
            S k a Q ∧ S k (σ (Multiplicative.ofAdd l) a) Q' ∧
            (∀ b ∈ Q, d b < d a) ∧ (∀ b ∈ Q', d b < d a)) ∧
          (∃ (ι : Type u) (X : ι → Type u) (top : ∀ i, TopologicalSpace (X i))
            (s t : ∀ i, X i) (p : ∀ i, X i → L),
            (∀ i, @ConnectedSpace (X i) (top i)) ∧
            (∀ i a x, ∃ U : Set (X i), @IsOpen (X i) (top i) U ∧ x ∈ U ∧
              ∃ r : ℤ → ℕ, Function.HasFiniteSupport r ∧
              ∃ V : U → CochainComplex (ModuleCat.{u} K) ℤ,
                (∀ z j, Module.Finite K ((V z).X j)) ∧
                (∀ z j, Module.finrank K ((V z).X j) = r j) ∧
                (∀ z : U, e (σ (Multiplicative.ofAdd (p i z.val)) a) =
                  ((V z).homologyEulerChar : ℚ))) ∧
            LinearMap.ker q =
              Submodule.span ℤ (Set.range (fun i => p i (t i) - p i (s i)))) ∧
          ∀ (V : Set (groupProjectiveClosure G)),
            @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V →
            ∃ a : C,
              d a ≤ SectionThree.locusDimension G.ambient (Subtype.val '' V) ∧
              ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
                ∃ N : ℕ, ∀ n ≥ N,
                  e (σ (Multiplicative.ofAdd
                    (n • ρ (Multiplicative.ofAdd (-g)) (∑ i, (D i : ℤ) • c i))) a) =
                    (Hilbert.hilbertFunction K G.ambient.factorCount G.ambient.ambientDimension
                      (G.ambient.vanishingIdeal (Subtype.val '' (τ g '' V)))
                      (fun i => D i * n) : ℚ) := by
  classical
  letI : IsAlgClosed K := hK.isAlgClosed
  obtain ⟨N, ⟨b⟩⟩ := Hilbert.SegreVeronese.exists_coordinate_basis G.ambient (fun _ => 1)
  obtain ⟨T, hπ, hpoint, hTzero, hTadd⟩ := ClosureScheme.exists_action G b τ hzero hadd hregular
  letI := ClosureTwistLattice.numericalQuotient_finite G b T
  exact closure_action_local_complex_of_finite_numerical_quotient K G b τ T hTzero hTadd hpoint hπ

end PhilipponMultiplicity
end
end

open PhilipponMultiplicity AlgebraicGeometry CategoryTheory
universe u

theorem solution
    (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K)
    (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
    (hzero : τ 0 = Equiv.refl _)
    (hadd : ∀ g h, τ (g+h) = (τ h).trans (τ g))
    (hregular : ∀ g, G.ambient.IsRegularAlong G.ambient
      (fun x : groupProjectiveClosure G => x.val) (fun x => (τ g x).val)) :
    ∃ (L : Type u) (_ : AddCommGroup L) (_ : Module ℤ L)
      (A : Type) (_ : AddCommGroup A) (_ : Module ℤ A) (_ : Module.Finite ℤ A)
      (q : L →ₗ[ℤ] A), Function.Surjective q ∧
      ∃ (ρ : Multiplicative G.Point →* (L ≃ₗ[ℤ] L)) (c : G.FactorIndex → L),
        (∀ g x, q x = 0 → q (ρ g x) = 0) ∧
        ∃ (C : Type u) (σ : Multiplicative L →* Equiv.Perm C)
          (d : C → ℕ) (e : C → ℚ) (S : C → C → Option C → Prop),
          (∀ l a b Q, S a b Q → S (σ l a) (σ l b) (Q.map (σ l))) ∧
          (∀ a b Q, S a b Q → e b = e a + Q.elim 0 e) ∧
          (∀ l a, ∃ (k : C) (Q Q' : Option C),
            S k a Q ∧ S k (σ (Multiplicative.ofAdd l) a) Q' ∧
            (∀ b ∈ Q, d b < d a) ∧ (∀ b ∈ Q', d b < d a)) ∧
          (∃ (ι : Type u) (X : ι → Type u) (top : ∀ i, TopologicalSpace (X i))
            (s t : ∀ i, X i) (p : ∀ i, X i → L),
            (∀ i, @ConnectedSpace (X i) (top i)) ∧
            (∀ i a x, ∃ U : Set (X i), @IsOpen (X i) (top i) U ∧ x ∈ U ∧
              ∃ r : ℤ → ℕ, Function.HasFiniteSupport r ∧
              ∃ V : U → CochainComplex (ModuleCat.{u} K) ℤ,
                (∀ z j, Module.Finite K ((V z).X j)) ∧
                (∀ z j, Module.finrank K ((V z).X j) = r j) ∧
                (∀ z : U, e (σ (Multiplicative.ofAdd (p i z.val)) a) =
                  ((V z).homologyEulerChar : ℚ))) ∧
            LinearMap.ker q =
              Submodule.span ℤ (Set.range (fun i => p i (t i) - p i (s i)))) ∧
          ∀ (V : Set (groupProjectiveClosure G)),
            @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V →
            ∃ a : C,
              d a ≤ SectionThree.locusDimension G.ambient (Subtype.val '' V) ∧
              ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
                ∃ N : ℕ, ∀ n ≥ N,
                  e (σ (Multiplicative.ofAdd
                    (n • ρ (Multiplicative.ofAdd (-g)) (∑ i, (D i : ℤ) • c i))) a) =
                    (Hilbert.hilbertFunction K G.ambient.factorCount G.ambient.ambientDimension
                      (G.ambient.vanishingIdeal (Subtype.val '' (τ g '' V)))
                      (fun i => D i * n) : ℚ) := by
  exact closure_action_has_local_complex_model_reduction_proof K hK G τ hzero hadd hregular
