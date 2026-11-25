-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesGenIndexPi_relIndex_pi_ee181e7e4ed0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:36:54.634456+00:00
-- url     : https://prove2.me/submissions/19b3406e-978e-4cf6-a017-9c330688428a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesGenIndexPi
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesGenIndexPi_index_pi_dep_99660b24698e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesGenIndexPi_piIncl_surjective_ccd437386011

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.KLinesGenIndexPi
open AddSubgroup
variable {η : Type} {G : Type} [AddCommGroup G]
namespace GroundTheory.Heights₂.Heights.KLinesGenIndexPi
theorem _root_.solution [Fintype η] (H K : η → AddSubgroup G) :
    (AddSubgroup.pi Set.univ H).relIndex (AddSubgroup.pi Set.univ K) =
      ∏ i, (H i).relIndex (K i) := by
  have hc : ((AddSubgroup.pi Set.univ H).addSubgroupOf (AddSubgroup.pi Set.univ K)).comap
      (piIncl K) = AddSubgroup.pi Set.univ fun i => (H i).addSubgroupOf (K i) := by
    ext x
    simp [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi, piIncl]
  unfold AddSubgroup.relIndex
  rw [← AddSubgroup.index_comap_of_surjective _ (piIncl_surjective K), hc, index_pi_dep]
end GroundTheory.Heights₂.Heights.KLinesGenIndexPi
