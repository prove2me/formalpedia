-- Prove2me | solution 1 for PhilipponMultiplicity.closed_locus_has_hyperplane_hilbert_model
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-11T03:23:25.807629+00:00
-- url     : https://prove2.me/submissions/e0faef16-970a-4d33-9ddd-4e1293cf1840

import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
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
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Topology.JacobsonSpace
import Mathlib.Topology.KrullDimension
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_finrank_sections_eq_eulerChar_of_iso_of_forall_subsingleton_HSucc
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_linearMap_sections_tensorPow_twistObj_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_forall_subsingleton_HSucc_tensorObj_tensorPow_of_isFinite_toProj_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isInvertible_glueOfCocycle
import Theorems.Thm_PhilipponMultiplicity_Hilbert_idealDimension_antitone
import Theorems.Thm_PhilipponMultiplicity_Hilbert_relevant_prime_dimension_strict

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

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

end PhilipponMultiplicity.AffineClosedPoints

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

def affineScheme (I : Ideal (MvPolynomial σ K)) : Scheme.{u} :=
  Spec (CommRingCat.of (MvPolynomial σ K ⧸ I))

def structureMap (I : Ideal (MvPolynomial σ K)) : affineScheme I ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial σ K ⧸ I)))

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

def chartIdeal (I : Ideal (MvPolynomial σ K)) (j : σ) : Ideal (MvPolynomial σ K) :=
  HomogeneousQuotientGrading.normalizedIdeal I (X j)

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

end PhilipponMultiplicity.MultiProjectiveSpace

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

theorem normalize_represents (x : domain M b) (i : M.FactorIndex) :
    ∃ h : (fun j => (normalize M b x).val ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => (normalize M b x).val ⟨i, j⟩) h = x.val i := by
  refine ⟨block_ne_zero M b (normalize M b x) i, ?_⟩
  exact congrFun (congrArg Subtype.val (denormalize_normalize M b x)) i

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

def projectiveEmbedding : scheme G b ⟶ Proj (homogeneousSubmodule (Fin (N + 1)) K) :=
  quotientMap _ _ ≫ (renameProjIso (singleVariableEquiv (K := K) N)).hom

theorem projectiveEmbedding_isClosedImmersion : IsClosedImmersion (projectiveEmbedding G b) := by
  letI := quotientMap_isClosedImmersion
    (Hilbert.SegreVeronese.diagonalIdeal G.ambient (fun _ => 1) b (ideal G))
    (Hilbert.SegreVeronese.ordinaryIdeal_isHomogeneous N _
      (Hilbert.SegreVeronese.diagonalIdeal_homogeneous G.ambient (fun _ => 1) b
        (fun _ => le_rfl) (ideal G) (ideal_homogeneous G)))
  unfold projectiveEmbedding
  infer_instance

theorem projectiveEmbedding_over :
    projectiveEmbedding G b ≫ polynomialStructureMap = structureMap G b := by
  unfold projectiveEmbedding
  rw [Category.assoc, renameProjIso_hom_over, quotientMap_over]
  rfl

def closedSubschemeProjectiveEmbedding (V : Set (groupProjectiveClosure G)) :
    closedSubscheme G b V ⟶ Proj (homogeneousSubmodule (Fin (N + 1)) K) :=
  closedSubschemeι G b V ≫ projectiveEmbedding G b

theorem closedSubschemeProjectiveEmbedding_isClosedImmersion
    (V : Set (groupProjectiveClosure G)) : IsClosedImmersion (closedSubschemeProjectiveEmbedding G b V) := by
  letI := closedSubschemeι_isClosedImmersion G b V
  letI := projectiveEmbedding_isClosedImmersion G b
  unfold closedSubschemeProjectiveEmbedding
  infer_instance

theorem closedSubschemeProjectiveEmbedding_over (V : Set (groupProjectiveClosure G)) :
    closedSubschemeProjectiveEmbedding G b V ≫ polynomialStructureMap =
      closedSubschemeι G b V ≫ structureMap G b := by
  rw [closedSubschemeProjectiveEmbedding, Category.assoc, projectiveEmbedding_over]

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

theorem presentation_isClosedImmersion [IsClosedImmersion φ] :
    IsClosedImmersion (presentation φ).toProj := inferInstanceAs (IsClosedImmersion φ)

theorem presentation_isFinite [IsFinite φ] :
    IsFinite (presentation φ).toProj := inferInstanceAs (IsFinite φ)

end PhilipponMultiplicity.ProjectiveTwistSheaf
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

def embeddingPolynomial : MvPolynomial (Fin (N + 1)) K →ₐ[K] G.ambient.CoordinateRing :=
  (substitution G.ambient (fun _ => 1) b).comp
    (MvPolynomial.rename (singleVariableEquiv (K := K) N).symm)

theorem embeddingPolynomial_homogeneous (F : MvPolynomial (Fin (N + 1)) K)
    (d : ℕ) (hF : F.IsHomogeneous d) :
    G.ambient.IsHomogeneous (embeddingPolynomial G b F) (fun _ => d) := by
  apply (G.ambient.degreePiece_iff _ _).mp
  simpa only [mul_one, embeddingPolynomial, AlgHom.comp_apply, Hilbert.degreePiece,
    MvPolynomial.mem_weightedHomogeneousSubmodule] using
    (substitution_homogeneous G.ambient (fun _ => 1) b d
      (MvPolynomial.rename (singleVariableEquiv (K := K) N).symm F) hF.rename_isHomogeneous)

theorem projectiveEmbedding_point_mem_basicOpen (x : groupProjectiveClosure G)
    (F : MvPolynomial (Fin (N + 1)) K) (d : ℕ) (hF : F.IsHomogeneous d) (hd : 0 < d) :
    projectiveEmbedding G b (point G b x) ∈ Proj.basicOpen _ F ↔
      G.ambient.eval (embeddingPolynomial G b F) x.val ≠ 0 := by
  let J := diagonalIdeal G.ambient (fun _ => 1) b (ideal G)
  let hJ := diagonalIdeal_homogeneous G.ambient (fun _ => 1) b
    (fun _ => le_rfl) (ideal G) (ideal_homogeneous G)
  let p := Hilbert.SegreVeronese.locusEquiv G.ambient b (ideal G) (ideal_homogeneous G)
    (locusEquiv G x)
  change ProjectivePointComparison.point N J hJ p ∈
      polynomialOpen J (ProjectivePointComparison.ordinaryHomogeneous N J hJ)
        (MvPolynomial.rename (singleVariableEquiv (K := K) N).symm F) ↔ _
  rw [ProjectivePointComparison.point_mem_polynomialOpen _ _ _ _ _ d
    hF.rename_isHomogeneous hd]
  exact (pointMap_eval_eq_zero_iff G.ambient (fun _ => 1) b x.val _ (fun _ => d)
    ((MultiProjectiveSpace.projective_homogeneous_iff N _ d).mpr hF.rename_isHomogeneous)).not

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

theorem closedSubschemeProjectiveEmbedding_preimage_eq_bot_iff
    (V : Set (groupProjectiveClosure G)) (F : MvPolynomial (Fin (N + 1)) K)
    (d : ℕ) (hF : F.IsHomogeneous d) (hd : 0 < d) :
    closedSubschemeProjectiveEmbedding G b V ⁻¹ᵁ Proj.basicOpen _ F = ⊥ ↔
      embeddingPolynomial G b F ∈ G.ambient.vanishingIdeal (Subtype.val '' V) := by
  rw [closedSubschemeProjectiveEmbedding, Scheme.Hom.comp_preimage]
  rw [closedSubscheme_preimage_eq_bot_iff]
  have he : (∀ x ∈ V, point G b x ∉ projectiveEmbedding G b ⁻¹ᵁ Proj.basicOpen _ F) ↔
      ∀ x ∈ V, G.ambient.eval (embeddingPolynomial G b F) x.val = 0 := by
    simp only [Scheme.Hom.mem_preimage, projectiveEmbedding_point_mem_basicOpen G b _ F d hF hd,
      not_not]
  rw [he]
  constructor
  · intro h
    apply Ideal.subset_span
    refine ⟨⟨fun _ => d, embeddingPolynomial_homogeneous G b F d hF⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  · intro h x hx
    exact G.ambient.eval_eq_zero_of_mem_vanishingIdeal h ⟨x, hx, rfl⟩

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

theorem embeddingPolynomial_degreePiece (d : ℕ) :
    (homogeneousSubmodule (Fin (N + 1)) K d).map (embeddingPolynomial G b).toLinearMap =
      Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension (fun _ => d) := by
  change (homogeneousSubmodule (Fin (N + 1)) K d).map
    ((substitution G.ambient (fun _ => 1) b).toLinearMap.comp
      (MvPolynomial.rename (singleVariableEquiv (K := K) N).symm).toLinearMap) = _
  rw [Submodule.map_comp, rename_homogeneousSubmodule,
    ← Hilbert.ordinary_degreePiece_eq, substitution_degreePiece]
  simp only [mul_one]

def embeddingQuotientMap (V : Set (groupProjectiveClosure G)) (d : ℕ) :
    homogeneousSubmodule (Fin (N + 1)) K d →ₗ[K]
      G.ambient.CoordinateRing ⧸ G.ambient.vanishingIdeal (Subtype.val '' V) :=
  ((Ideal.Quotient.mkₐ K (G.ambient.vanishingIdeal (Subtype.val '' V))).comp
    (embeddingPolynomial G b)).toLinearMap.domRestrict _

theorem embeddingQuotientMap_eq_zero_iff (V : Set (groupProjectiveClosure G)) (d : ℕ)
    (F : homogeneousSubmodule (Fin (N + 1)) K d) :
    embeddingQuotientMap G b V d F = 0 ↔
      embeddingPolynomial G b F.val ∈ G.ambient.vanishingIdeal (Subtype.val '' V) :=
  Ideal.Quotient.eq_zero_iff_mem

theorem embeddingQuotientMap_range (V : Set (groupProjectiveClosure G)) (d : ℕ) :
    LinearMap.range (embeddingQuotientMap G b V d) =
      Hilbert.quotientPiece K G.ambient.factorCount G.ambient.ambientDimension
        (G.ambient.vanishingIdeal (Subtype.val '' V)) (fun _ => d) := by
  rw [embeddingQuotientMap, LinearMap.range_domRestrict]
  change (homogeneousSubmodule (Fin (N + 1)) K d).map
    ((Ideal.Quotient.mkₐ K (G.ambient.vanishingIdeal (Subtype.val '' V))).toLinearMap.comp
      (embeddingPolynomial G b).toLinearMap) = _
  rw [Submodule.map_comp, embeddingPolynomial_degreePiece]
  rfl

end PhilipponMultiplicity.ClosureScheme

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
-- Reused implementation: Solutions.PhilipponClosureSectionHilbertComparison

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ClosureScheme
open AlgebraicGeometry CategoryTheory MvPolynomial ProjectiveSections
universe u
variable {K : Type u} [Field K] (G : EmbeddedGroupProduct K) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension (fun _ => 1)))
    (V : Set (groupProjectiveClosure G))
attribute [local instance] MvPolynomial.gradedAlgebra

theorem polynomialSectionMap_kernel (d : ℕ) (hd : 0 < d) :
    LinearMap.ker (polynomialSectionMap (closedSubschemeProjectiveEmbedding G b V) d) =
      LinearMap.ker (embeddingQuotientMap G b V d) := by
  letI := closedSubscheme_isReduced G b V
  ext F
  rw [LinearMap.mem_ker, LinearMap.mem_ker,
    polynomialSectionMap_eq_zero_iff_preimage,
    closedSubschemeProjectiveEmbedding_preimage_eq_bot_iff G b V F.val d F.property hd,
    embeddingQuotientMap_eq_zero_iff]

theorem eventually_quotientPiece_sections_equiv :
    ∃ d₀ : ℕ, ∀ d ≥ d₀,
      Nonempty (Hilbert.quotientPiece K G.ambient.factorCount G.ambient.ambientDimension
          (G.ambient.vanishingIdeal (Subtype.val '' V)) (fun _ => d) ≃ₗ[K]
        ProjSpace.twistObj
          (closedSubschemeProjectiveEmbedding G b V ≫ ProjSpace.π K N)
          (closedSubschemeProjectiveEmbedding G b V) d ⊤) := by
  let φ := closedSubschemeProjectiveEmbedding G b V
  letI := closedSubschemeProjectiveEmbedding_isClosedImmersion G b V
  obtain ⟨d₀, hd₀⟩ := polynomialSectionMap_eventually_surjective φ
  refine ⟨max d₀ 1, fun d hd => ?_⟩
  have hpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ _) hd)
  have hsurj := hd₀ d (le_trans (le_max_left _ _) hd)
  let e := (embeddingQuotientMap G b V d).quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ (polynomialSectionMap_kernel G b V d hpos).symm).trans
      ((polynomialSectionMap φ d).quotKerEquivOfSurjective hsurj))
  rw [embeddingQuotientMap_range G b V d] at e
  exact ⟨e⟩

theorem eventually_sections_finrank_eq_hilbertFunction :
    ∃ d₀ : ℕ, ∀ d ≥ d₀,
      Module.finrank K (ProjSpace.twistObj
        (closedSubschemeProjectiveEmbedding G b V ≫ ProjSpace.π K N)
        (closedSubschemeProjectiveEmbedding G b V) d ⊤) =
      Hilbert.hilbertFunction K G.ambient.factorCount G.ambient.ambientDimension
        (G.ambient.vanishingIdeal (Subtype.val '' V)) (fun _ => d) := by
  obtain ⟨d₀, hd₀⟩ := eventually_quotientPiece_sections_equiv G b V
  refine ⟨d₀, fun d hd => ?_⟩
  obtain ⟨e⟩ := hd₀ d hd
  exact e.finrank_eq.symm

end PhilipponMultiplicity.ClosureScheme
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
-- Reused implementation: Solutions.PhilipponGroupPrimeComponents

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity

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

omit [IsAlgClosed K] in
theorem projectiveEmbedding_structureMap :
    closedSubschemeProjectiveEmbedding G b V ≫ ProjSpace.π K N =
      closedSubschemeι G b V ≫ structureMap G b := by
  have h : ProjSpace.π K N =
      ProjectiveCoordinateScheme.polynomialStructureMap (K := K) (σ := Fin (N + 1)) := rfl
  rw [h, closedSubschemeProjectiveEmbedding_over]

theorem eventually_hyperplane_euler_eq_hilbertFunction :
    let L := twistSheaf (closedSubschemeProjectiveEmbedding G b V) 1
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ U : (closedSubscheme G b V).OrderedAffineCover,
      (OModulePresheaf.ofModules (closedSubschemeι G b V ≫ structureMap G b)
        (L.tensorPow d)).eulerChar U =
        (Hilbert.hilbertFunction K G.ambient.factorCount G.ambient.ambientDimension
          (G.ambient.vanishingIdeal (Subtype.val '' V)) (fun _ => d) : ℤ) := by
  let φ := closedSubschemeProjectiveEmbedding G b V
  let L := twistSheaf φ 1
  let π := φ ≫ ProjSpace.π K N
  have hπ : π = closedSubschemeι G b V ≫ structureMap G b :=
    projectiveEmbedding_structureMap G b V
  letI := closedSubschemeProjectiveEmbedding_isClosedImmersion G b V
  letI : IsProper π := hπ.symm ▸ closedSubscheme_isProper G b V
  obtain ⟨d₀, hd₀⟩ := SchemeEuler.eventually_euler_tensorPow_eq_sections π L
    (twistSheaf_isInvertible φ 1) N (presentation φ) (presentation_isFinite φ)
  obtain ⟨d₁, hd₁⟩ := eventually_sections_finrank_eq_hilbertFunction G b V
  refine ⟨max d₀ d₁, fun d hd U => ?_⟩
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π (L.tensorPow d) ⊤
  obtain ⟨e⟩ := tensorPow_sections_equiv_over (presentation φ) d ⊤
  have hχ := hd₀ d (le_trans (le_max_left _ _) hd) U
  have he : Module.finrank K Γ(L.tensorPow d, ⊤) =
      Module.finrank K (ProjSpace.twistObj π φ d ⊤) := e.finrank_eq
  have hdim : Module.finrank K (ProjSpace.twistObj π φ d ⊤) =
      Hilbert.hilbertFunction K G.ambient.factorCount G.ambient.ambientDimension
        (G.ambient.vanishingIdeal (Subtype.val '' V)) (fun _ => d) :=
    hd₁ d (le_trans (le_max_right _ _) hd)
  have hresult := hχ.trans (congrArg (fun n : ℕ => (n : ℤ)) (he.trans hdim))
  exact (congrArg (fun θ =>
    (OModulePresheaf.ofModules θ (L.tensorPow d)).eulerChar U) hπ).symm.trans hresult

end PhilipponMultiplicity.ClosureScheme
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponClosedLocusHilbertModel

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity
open AlgebraicGeometry CategoryTheory Topology
universe u

theorem closed_locus_has_hyperplane_hilbert_model_proof
    (K : Type u) [Field K] [IsAlgClosed K] (G : EmbeddedGroupProduct K)
    (V : Set (groupProjectiveClosure G))
    (hV : @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V) :
    letI := G.ambient.zariskiTopology
    ∃ (X : Scheme.{u}) (π : X ⟶ Spec (.of K))
      (_ : V ≃ₜ {x : X | IsClosed {x}}) (L : X.Modules),
      IsProper π ∧ IsReduced X ∧
      topologicalKrullDim X ≤
        (SectionThree.locusDimension G.ambient (Subtype.val '' V) : WithBot ℕ∞) ∧
      Scheme.Modules.IsInvertible L ∧
      ∃ (N : ℕ) (p : L.ProjPresentation π N), IsClosedImmersion p.toProj ∧
        ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ U : X.OrderedAffineCover,
          (OModulePresheaf.ofModules π (L.tensorPow d)).eulerChar U =
            (Hilbert.hilbertFunction K G.ambient.factorCount G.ambient.ambientDimension
              (G.ambient.vanishingIdeal (Subtype.val '' V)) (fun _ => d) : ℤ) := by
  letI := G.ambient.zariskiTopology
  obtain ⟨N, ⟨b⟩⟩ := Hilbert.SegreVeronese.exists_coordinate_basis G.ambient (fun _ => 1)
  let φ := ClosureScheme.closedSubschemeProjectiveEmbedding G b V
  let π := φ ≫ ProjSpace.π K N
  let L := ProjectiveTwistSheaf.twistSheaf φ 1
  have hπ : π = ClosureScheme.closedSubschemeι G b V ≫ ClosureScheme.structureMap G b :=
    ClosureScheme.projectiveEmbedding_structureMap G b V
  letI := ClosureScheme.closedSubschemeProjectiveEmbedding_isClosedImmersion G b V
  have hproper : IsProper π := hπ.symm ▸ ClosureScheme.closedSubscheme_isProper G b V
  refine ⟨ClosureScheme.closedSubscheme G b V, π,
    ClosureScheme.closedSubschemeClosedPointHomeomorph G b V hV, L, hproper,
    ClosureScheme.closedSubscheme_isReduced G b V,
    ClosureScheme.closedSubscheme_dimension_le G b V hV,
    ProjectiveTwistSheaf.twistSheaf_isInvertible φ 1,
    N, ProjectiveTwistSheaf.presentation φ,
    ProjectiveTwistSheaf.presentation_isClosedImmersion φ, ?_⟩
  obtain ⟨d₀, hd₀⟩ := ClosureScheme.eventually_hyperplane_euler_eq_hilbertFunction G b V
  refine ⟨d₀, fun d hd U => ?_⟩
  exact (congrArg (fun θ =>
    (OModulePresheaf.ofModules θ (L.tensorPow d)).eulerChar U) hπ).trans (hd₀ d hd U)

end PhilipponMultiplicity
end
end

open PhilipponMultiplicity AlgebraicGeometry CategoryTheory
universe u

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] (G : EmbeddedGroupProduct K)
    (V : Set (groupProjectiveClosure G))
    (hV : @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V) :
    letI := G.ambient.zariskiTopology
    ∃ (X : Scheme.{u}) (π : X ⟶ Spec (.of K))
      (_ : V ≃ₜ {x : X | IsClosed {x}}) (L : X.Modules),
      IsProper π ∧ IsReduced X ∧
      topologicalKrullDim X ≤
        (SectionThree.locusDimension G.ambient (Subtype.val '' V) : WithBot ℕ∞) ∧
      Scheme.Modules.IsInvertible L ∧
      ∃ (N : ℕ) (p : L.ProjPresentation π N), IsClosedImmersion p.toProj ∧
        ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ U : X.OrderedAffineCover,
          (OModulePresheaf.ofModules π (L.tensorPow d)).eulerChar U =
            (Hilbert.hilbertFunction K G.ambient.factorCount G.ambient.ambientDimension
              (G.ambient.vanishingIdeal (Subtype.val '' V)) (fun _ => d) : ℤ) := by
  exact closed_locus_has_hyperplane_hilbert_model_proof K G V hV
