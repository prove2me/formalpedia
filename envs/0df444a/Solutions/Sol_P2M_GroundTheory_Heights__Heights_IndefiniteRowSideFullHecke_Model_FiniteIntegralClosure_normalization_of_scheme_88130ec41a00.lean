-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_FiniteIntegralClosure_normalization_of_scheme_88130ec41a00
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:48:30.169588+00:00
-- url     : https://prove2.me/submissions/0e0b666c-f762-4cd7-a093-f8b01e8c66c8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteTypeSectionsOfIsFiniteTypeOverZ
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genericSpecMap_closedPoint_6aa880cac864
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genericSpecMap_app_iso_6054cb9c6d0f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
open CategoryTheory Opposite AlgebraicGeometry
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
namespace FiniteIntegralClosure
theorem _root_.solution
    (h : ∀ (X : Scheme.{0}) [IsIntegral X], IsFiniteTypeOverZ X →
      ∀ (L : Type) [Field L] [Algebra X.functionField L] [FiniteDimensional X.functionField L]
        (U : X.Opens), IsAffineOpen U → ∀ hU : Nonempty U,
        let : Algebra Γ(X, U) L :=
          ((algebraMap X.functionField L).comp (@algebraMap Γ(X, U) X.functionField _ _ (by
            haveI := hU; infer_instance))).toAlgebra
        Module.Finite Γ(X, U) (integralClosure Γ(X, U) L)) :
    _root_.GroundTheory.Heights₂.Heights.Model.FiniteNormalization.Statement := by
  intro Z _ f _ _ L _ _ _
  have e : f = toSpecZ Z := specZ_hom_ext _ _
  have hX : IsFiniteTypeOverZ Z := ⟨e ▸ ‹LocallyOfFiniteType f›, e ▸ ‹QuasiCompact f›⟩
  set g := _root_.GroundTheory.Heights₂.Heights.Model.genericSpecMap Z L with hg
  refine { finite_app := fun U hU => ?_ }
  let := (g.app U).hom.toAlgebra
  rw [g.fromNormalization_app hU, CommRingCat.hom_comp]
  refine RingHom.Finite.comp ?_ ?_
  · exact RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (g.normalizationObjIso hU).inv).2
  refine RingHom.finite_algebraMap.2 ?_
  rcases isEmpty_or_nonempty U with hU0 | hU0
  · have hb : U = ⊥ := SetLike.coe_injective (by simpa using Set.isEmpty_coe_sort.mp hU0)
    subst hb
    have : Subsingleton (integralClosure Γ(Z, ⊥) Γ(Spec (CommRingCat.of L), g ⁻¹ᵁ ⊥)) :=
      Module.subsingleton Γ(Z, ⊥) _
    exact ⟨⟨∅, Subsingleton.elim _ _⟩⟩
  have hη : genericPoint Z ∈ U :=
    ((genericPoint_spec Z).mem_open_set_iff U.isOpen).mpr (by simpa using hU0)
  have hmem : g (IsLocalRing.closedPoint L) ∈ U := by
    rw [hg, genericSpecMap_closedPoint]; exact hη
  have key := genericSpecMap_app_iso Z L U hη hmem
  let : Algebra Γ(Z, U) L :=
    ((algebraMap Z.functionField L).comp (algebraMap Γ(Z, U) Z.functionField)).toAlgebra
  let eR := ((Spec (CommRingCat.of L)).presheaf.mapIso (eqToIso
        (Scheme.preimage_eq_top_of_closedPoint_mem _ hmem).symm).op ≪≫
        Scheme.ΓSpecIso (CommRingCat.of L)).commRingCatIsoToRingEquiv
  let eA : Γ(Spec (CommRingCat.of L), g ⁻¹ᵁ U) ≃ₐ[Γ(Z, U)] L :=
    AlgEquiv.ofRingEquiv (f := eR) fun x => congrArg (fun φ => φ.hom x) key
  have hfin := h Z hX L U hU hU0
  exact Module.Finite.equiv eA.mapIntegralClosure.symm.toLinearEquiv
end FiniteIntegralClosure
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
