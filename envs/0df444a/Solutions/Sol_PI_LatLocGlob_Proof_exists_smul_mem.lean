-- Prove2me | solution 1 for PI.LatLocGlob.Proof.exists_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:23.126004+00:00
-- url     : https://prove2.me/submissions/c1d5cded-954d-4754-b93f-b890b4f9f409

import Definitions.Def_Formalism_PeriodIntegrals_LatLocGlob
import Definitions.Def_Lemmata_GeneralBFactThirdBisAlt_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalGlobalLattice_ExistsSmulMemOfLocal
import Theorems.Thm_Bl_general_b_fact_third_bis_other_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LatLocGlob PI.LatLocGlob.Proof
open PI.LatLocGlob
variable {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace PI.LatLocGlob.Proof
theorem _root_.solution (N : Submodule R V) {v : V} (hv : v ∈ Submodule.span K (N : Set V)) :
    ∃ c : R, c ≠ 0 ∧ c • v ∈ N := by
  first | exact Bl.general_b_fact_third_bis_other.goal1 .. | (apply Bl.general_b_fact_third_bis_other.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_third_bis_other.goal1 <;> assumption) | (apply @Bl.general_b_fact_third_bis_other.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_third_bis_other.goal1 <;> assumption) | (apply @Bl.general_b_fact_third_bis_other.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_third_bis_other.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› N v hv | exact @Bl.general_b_fact_third_bis_other.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› N v | exact @Bl.general_b_fact_third_bis_other.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› N | exact @Bl.general_b_fact_third_bis_other.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_third_bis_other.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_third_bis_other.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_third_bis_other.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_third_bis_other.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_third_bis_other.goal1 R K V ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_third_bis_other.goal1 R K V ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_third_bis_other.goal1 R K V ‹_› ‹_› | exact @Bl.general_b_fact_third_bis_other.goal1 R K V ‹_› | exact @Bl.general_b_fact_third_bis_other.goal1 R K V | exact @Bl.general_b_fact_third_bis_other.goal1 R K | exact @Bl.general_b_fact_third_bis_other.goal1 R
end PI.LatLocGlob.Proof
