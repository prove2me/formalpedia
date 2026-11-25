-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_GradedPres_proof_b3e19960dbe1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:38:04.506609+00:00
-- url     : https://prove2.me/submissions/0a653dcf-4f99-4e0e-beda-40c715cf7fdc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsPres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGradedPres
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GradedPres_freeBasis_mem_820eb7053f2b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GradedPres_genMap_basis_f97c744f41c8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GradedPres_exists_homogeneous_generators_86a8a5977c01

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace GradedPres
theorem _root_.solution : GradedPres.Statement.{u, v} := by
  intro S _ _ N M _ _ _ _ 𝓜 hfin
  classical
  obtain ⟨r, m, d, hm, hspan⟩ := GradedPres.exists_homogeneous_generators 𝓜 hfin
  let g := GradedPres.genMap.{u, max u v} 𝓜 d m hm
  have : Module.Finite (Poly S N) (ULift.{max u v} (Fin r → Poly S N)) :=
    Module.Finite.equiv (ULift.moduleEquiv (R := Poly S N)).symm
  refine ⟨ULift.{max u v} (Fin r → Poly S N), inferInstance, inferInstance, inferInstance,
    inferInstance, LinearMap.ker g.toLin, inferInstance, inferInstance, inferInstance, inferInstance,
    GradedPres.freeGraded N d, GradedPres.kerGraded g, r, GradedPres.freeBasis S N r, d,
    GradedPres.kerIncl g, g, GradedPres.freeBasis_mem d, inferInstance, ?_, ?_,
    LinearMap.exact_subtype_ker_map _⟩
  · exact Subtype.val_injective
  · rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact ⟨_, GradedPres.genMap_basis 𝓜 d m hm j⟩
end GradedPres
end GroundTheory.Heights₂.Heights.Kleiman
