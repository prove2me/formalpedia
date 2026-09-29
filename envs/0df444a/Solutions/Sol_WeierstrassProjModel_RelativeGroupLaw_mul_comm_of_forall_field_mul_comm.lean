-- Prove2me | solution 1 for WeierstrassProjModel.RelativeGroupLaw.mul_comm_of_forall_field_mul_comm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/11b1df29-6faa-5c9b-8b03-188dae4818e5

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Theorems.Thm_AlgebraicGeometry_isCommMonObj_of_isProper_of_flat_of_geometricallyIntegral
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_isProper
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_smoothOfRelativeDimension_one
import Theorems.Thm_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_RelativeGroupLaw_mul_comm_of_forall_field_mul_comm
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial AdicCompletion.instIsLocalRingMaximalIdeal WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X"

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

universe u

set_option maxHeartbeats 4800000 in
theorem solution
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R)
    [V.toAffine.IsElliptic]
    (hbc : ∀ (K : Type u) [Field K] [Algebra R K],
        Nonempty (pullback (projModelStrCR V)
            (Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ≅ projModelCR (V.baseChange K)))
    (G : RelativeGroupLaw R (projModelStrCR V))
    (hcomm : ∀ (K : Type u) [Field K] [Algebra R K]
        (P Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R K))) (projModelStrCR V)),
      G.mul (Spec.map (CommRingCat.ofHom (algebraMap R K))) P Q
        = G.mul (Spec.map (CommRingCat.ofHom (algebraMap R K))) Q P) :
    ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (projModelStrCR V)),
      G.mul t x y = G.mul t y x := by

  clear hcomm
  intro T t x y

  haveI := WeierstrassProjModel.projModelStrCR_isProper V
  haveI hsm : SmoothOfRelativeDimension 1 (projModelStrCR V) := by
    first
      | exact WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one V
      | { haveI : V.IsElliptic := ‹V.toAffine.IsElliptic›
          exact WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one V }
      | { haveI : V.IsElliptic := by exact_mod_cast ‹V.toAffine.IsElliptic›
          exact WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one V }
  haveI : Smooth (projModelStrCR V) := SmoothOfRelativeDimension.smooth 1 (projModelStrCR V)
  haveI : Flat (projModelStrCR V) := by first | infer_instance | exact Smooth.flat _
  haveI : LocallyOfFinitePresentation (projModelStrCR V) := by
    first | infer_instance | exact Smooth.locallyOfFinitePresentation _
  haveI : GeometricallyIntegral (projModelStrCR V) := by
    first
      | exact WeierstrassProjModel.kw_hgi_geometricallyIntegral_of_baseChangeIso V.toAffine hbc
      | exact WeierstrassProjModel.kw_hgi_geometricallyIntegral_of_baseChangeIso V.toAffine
          (fun K _ _ => hbc K)
      | { have h := WeierstrassProjModel.kw_hgi_geometricallyIntegral_of_baseChangeIso
            (R := R) V.toAffine
          first | exact h hbc | exact h (fun K _ _ => hbc K) }

  let G' : GoodReductionJacobian.RelativeGroupLaw R (projModelStrCR V) :=
    { mul := G.mul, one := G.one, inv := G.inv,
      mul_assoc := G.mul_assoc, one_mul := G.one_mul, mul_one := G.mul_one,
      inv_mul_cancel := G.inv_mul_cancel, mul_natural := G.mul_natural }

  letI := G'.grpObjOverMk
  haveI : IsProper (Over.mk (projModelStrCR V)).hom := ‹IsProper (projModelStrCR V)›
  haveI : Flat (Over.mk (projModelStrCR V)).hom := ‹Flat (projModelStrCR V)›
  haveI : LocallyOfFinitePresentation (Over.mk (projModelStrCR V)).hom :=
    ‹LocallyOfFinitePresentation (projModelStrCR V)›
  haveI : GeometricallyIntegral (Over.mk (projModelStrCR V)).hom :=
    ‹GeometricallyIntegral (projModelStrCR V)›

  haveI hc : IsCommMonObj (Over.mk (projModelStrCR V)) :=
    AlgebraicGeometry.isCommMonObj_of_isProper_of_flat_of_geometricallyIntegral
      (Over.mk (projModelStrCR V))

  exact G'.isCommMonObj_grpObjOverMk_iff_mul_comm.mp hc t x y

end S_WeierstrassProjModel_RelativeGroupLaw_mul_comm_of_forall_field_mul_comm
end P2MW
export P2MW.S_WeierstrassProjModel_RelativeGroupLaw_mul_comm_of_forall_field_mul_comm (solution)
