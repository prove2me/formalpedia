-- Prove2me | solution 1 for WeierstrassProjModel.projModel_pullback_iso_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/697ecd2d-f07f-57e7-8fdd-ae9543dd895d

import Definitions.Def_WeierstrassCurve_ProjModel
import Theorems.Thm_WeierstrassProjModel_projModel_isPullback_baseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_projModel_pullback_iso_baseChange
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X"

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

universe u

theorem solution
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R) :
    ∀ (K : Type u) [Field K] [Algebra R K],
      Nonempty (pullback (projModelStrCR V)
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))
        ≅ projModelCR (V.baseChange K)) := by
  intro K _ _
  obtain ⟨α, hpb⟩ := WeierstrassProjModel.projModel_isPullback_baseChange V K
  exact ⟨hpb.isoPullback.symm⟩

end S_WeierstrassProjModel_projModel_pullback_iso_baseChange
end P2MW
export P2MW.S_WeierstrassProjModel_projModel_pullback_iso_baseChange (solution)
