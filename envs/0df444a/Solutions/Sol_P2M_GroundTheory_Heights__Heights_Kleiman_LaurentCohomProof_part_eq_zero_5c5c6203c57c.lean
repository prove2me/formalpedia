-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_part_eq_zero_5c5c6203c57c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:30:23.501631+00:00
-- url     : https://prove2.me/submissions/97136efb-8eb3-42a2-a3a7-9dc73a25bd93

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurentCohom
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_mem_negSet_131f8e45df3d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_part_apply_c050aba19709
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_mem_exps_3fdef6a3d557

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
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Kleiman.LaurentCohomProof
variable {S : Type u} [CommRing S] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.Kleiman.LaurentCohomProof
theorem _root_.solution {c : ℤ} {J : Finset (Fin (N + 1))} {I : StdCell N} {f : Laurent S N}
    (hf : f ∈ laurentDeg S N c I) (hJ : ¬ J ⊆ I.1) : part S J f = 0 := by
  ext a
  rw [part_apply, Finsupp.zero_apply]
  split_ifs with h
  · by_contra h'
    apply hJ
    intro j hj
    by_contra hjI
    have h1 := (mem_exps hf h').2 j hjI
    rw [← h, mem_negSet] at hj
    omega
  · rfl
end GroundTheory.Heights₂.Heights.Kleiman.LaurentCohomProof
