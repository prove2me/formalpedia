-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutIKillsIdeal_proof_5dd502db2c77
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:02:57.759335+00:00
-- url     : https://prove2.me/submissions/4ebcd978-6e68-41b8-a623-287b891bcdc7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutIKillsIdeal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_rootPsum_isHomogeneous_4f395669457a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_restTransport_isHomogeneous_e751977fd44f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KRest_homogeneousComponent_mul_left_b27e51f058a8


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
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
namespace RestCutIKillsIdeal
theorem _root_.solution (h₁ : RestCutIdealSum.Statement)
    (h₂ : RestCutTransportPsum.Statement) : RestCutIKillsIdeal.Statement := by
  intro f j k N e I hI A hA hhom
  obtain ⟨G, hG⟩ := h₁ f N A hA
  have hT := restTransport_isHomogeneous f j k N e hhom
  have hC := homogeneousComponent_of_mem (m := flagDim f j k) hT
  rw [if_pos rfl] at hC
  rw [← hC]
  rw [hG, map_sum, map_sum, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_mul, h₂, KRest.homogeneousComponent_mul_left (rootPsum_isHomogeneous f j k _ i.2)]
  split_ifs with hle
  · exact hI.kills _ _ _ (Nat.succ_le_succ (Nat.zero_le _)) hle
      (homogeneousComponent_isHomogeneous _ _)
  · exact map_zero I
end RestCutIKillsIdeal
end GroundTheory.Heights₂.Heights
