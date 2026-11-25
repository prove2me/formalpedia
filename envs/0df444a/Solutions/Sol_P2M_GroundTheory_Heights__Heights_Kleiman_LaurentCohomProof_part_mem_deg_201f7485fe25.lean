-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_part_mem_deg_201f7485fe25
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:02:17.975246+00:00
-- url     : https://prove2.me/submissions/bde3366e-264b-45a1-a875-ffa89502ca65

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurentCohom
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_part_mem_w_99de7a96f87b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_part_eq_zero_5c5c6203c57c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_mem_deg_of_w_5673bc6b73c7

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
    (hf : f ∈ laurentDeg S N c I) : part S J f ∈ laurentDeg S N c I :=
  mem_deg_of_w (part_mem_w hf) (part_eq_zero hf)
end GroundTheory.Heights₂.Heights.Kleiman.LaurentCohomProof
