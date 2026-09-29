-- Prove2me | solution 1 for WeierstrassProjModel.exists_dominant_field_point_selfPullback_of_isElliptic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/1cc2ebd3-a3d6-586f-91fb-dbcffe9be5fd

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Theorems.Thm_WeierstrassProjModel_isIntegral_selfPullback_of_isElliptic_field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_exists_dominant_field_point_selfPullback_of_isElliptic
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X"

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

set_option maxHeartbeats 12800000 in
theorem solution
    (K : Type) [Field K] (W : WeierstrassCurve K) [W.IsElliptic] :
    let π := projModelStrCR W.toProjective
    ∃ (F : Type) (_ : Field F) (_ : Algebra K F)
      (ι : Spec (CommRingCat.of F) ⟶ pullback π π),
      IsSchemeTheoreticallyDominant ι ∧
      ι ≫ pullback.fst π π ≫ π = Spec.map (CommRingCat.ofHom (algebraMap K F)) := by
  intro π
  let E2 := pullback π π
  let τ : E2 ⟶ Spec (CommRingCat.of K) := pullback.fst π π ≫ π
  haveI hintE2 : IsIntegral E2 :=
    WeierstrassProjModel.isIntegral_selfPullback_of_isElliptic_field K W

  let F : Type := E2.functionField
  letI instF : Field F := inferInstance
  let ι₀ : Spec E2.functionField ⟶ E2 := E2.fromSpecStalk (genericPoint E2)
  let ι : Spec (CommRingCat.of F) ⟶ E2 := Spec.map (𝟙 _) ≫ ι₀
  have hι_eq : ι = ι₀ := by simp only [ι, Spec.map_id, Category.id_comp]

  let φ : CommRingCat.of K ⟶ E2.functionField := by
    first
    | exact (Scheme.Spec.preimage (ι₀ ≫ τ)).unop
    | exact Scheme.Spec.preimage (ι₀ ≫ τ) |>.unop
    | exact (Scheme.Spec.fullyFaithful.preimage (ι₀ ≫ τ)).unop
    | exact Spec.preimage (ι₀ ≫ τ)
    | exact ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (Scheme.Γ.map (ι₀ ≫ τ).op)
        ≫ (Scheme.ΓSpecIso E2.functionField).hom)
  let algMap : K →+* F := φ.hom
  letI instAlg : Algebra K F := algMap.toAlgebra
  have hφ_eq : CommRingCat.ofHom algMap = φ := by
    first | exact CommRingCat.ofHom_hom φ | rfl | ext; rfl
  have halg : ι ≫ τ = Spec.map (CommRingCat.ofHom algMap) := by
    rw [hι_eq, hφ_eq]
    first
    | exact (Scheme.Spec.map_preimage (ι₀ ≫ τ)).symm
    | · have h := Scheme.Spec.map_preimage (ι₀ ≫ τ)
        rw [← h]; first | rfl | simp [Spec.map, φ]
    | · show ι₀ ≫ τ = Spec.map φ; exact (Spec.map_preimage _).symm

  haveI hdom₀ : IsDominant ι₀ := by
    constructor
    have hη : genericPoint (E2 : Scheme) ∈ Set.range (ι₀.base) := by
      first
      | exact ⟨IsLocalRing.closedPoint _, Scheme.fromSpecStalk_closedPoint⟩
      | exact ⟨IsLocalRing.closedPoint _, by
          first
          | exact Scheme.fromSpecStalk_closedPoint
          | exact LocallyRingedSpace.fromSpecStalk_closedPoint
          | simp [Scheme.fromSpecStalk_closedPoint]⟩
      | · refine ⟨genericPoint _, ?_⟩
          have : Subsingleton (Spec E2.functionField) := by
            first | infer_instance | exact PrimeSpectrum.instSubsingleton
          rw [Subsingleton.elim (genericPoint _) (IsLocalRing.closedPoint _)]
          exact Scheme.fromSpecStalk_closedPoint
    have hdense : Dense ({genericPoint (E2:Scheme)} : Set E2) := by
      first
      | · rw [dense_iff_closure_eq]; exact genericPoint_spec E2
      | · rw [dense_iff_closure_eq]
          exact (genericPoint_spec (E2:Scheme)).closure_eq
      | exact (genericPoint_spec (E2:Scheme)).dense
      | · rw [dense_iff_closure_eq]
          exact IrreducibleSpace.isGenericPoint_genericPoint.closure_eq
    exact hdense.mono (Set.singleton_subset_iff.mpr hη)
  haveI hdom : IsDominant ι := by rw [hι_eq]; exact hdom₀

  haveI hredE2 : IsReduced E2 := inferInstance
  haveI hqc : QuasiCompact ι := by
    first
    | infer_instance
    | · haveI : IsNoetherianRing F := inferInstance
        infer_instance
    | · haveI : IsAffine (Spec (CommRingCat.of F)) := inferInstance
        infer_instance
    | · refine ⟨fun U _ _ => ?_⟩
        haveI : NoetherianSpace (Spec (CommRingCat.of F)) := by
          first | infer_instance | exact PrimeSpectrum.instNoetherianSpace
        exact NoetherianSpace.isCompact _
  haveI hschdom : IsSchemeTheoreticallyDominant ι := by
    first
    | infer_instance
    | exact (isSchemeTheoreticallyDominant_iff_isDominant (f := ι)).mpr hdom
    | exact IsDominant.isSchemeTheoreticallyDominant
    | exact isSchemeTheoreticallyDominant_of_isDominant
  exact ⟨F, instF, instAlg, ι, hschdom, halg⟩

end S_WeierstrassProjModel_exists_dominant_field_point_selfPullback_of_isElliptic
end P2MW
export P2MW.S_WeierstrassProjModel_exists_dominant_field_point_selfPullback_of_isElliptic (solution)
