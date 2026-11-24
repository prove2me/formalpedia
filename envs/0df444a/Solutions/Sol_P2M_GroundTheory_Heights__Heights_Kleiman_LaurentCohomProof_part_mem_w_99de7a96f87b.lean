-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_part_mem_w_99de7a96f87b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:02:53.742625+00:00
-- url     : https://prove2.me/submissions/e32f1ab8-2b41-4dfa-b658-53b919b4f0e9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurentCohom
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
    (hf : f ∈ laurentDeg S N c I) : part S J f ∈ wPart S N c J := by
  refine (Finsupp.mem_supported' S _).mpr fun a ha => ?_
  rw [part_apply]
  split_ifs with h
  · by_contra h'
    exact ha ⟨h, (mem_exps hf h').1⟩
  · rfl
end GroundTheory.Heights₂.Heights.Kleiman.LaurentCohomProof
