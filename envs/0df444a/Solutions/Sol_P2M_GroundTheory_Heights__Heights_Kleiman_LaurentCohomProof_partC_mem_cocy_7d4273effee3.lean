-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_partC_mem_cocy_7d4273effee3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:38:16.148389+00:00
-- url     : https://prove2.me/submissions/8d0fe27f-d4ae-4854-b8c6-61d2e34b05b2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurentCohom
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_part_mem_deg_201f7485fe25
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_partC_d_b9ed291a3cb0

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
theorem _root_.solution {c : ℤ} {i : ℕ} (J : Finset (Fin (N + 1))) {z : Cech.Cochain (G S N) i}
    (hz : z ∈ Cech.cocyDeg (G S N) (laurentDeg S N c) (ρ S N) i) :
    partC S J i z ∈ Cech.cocyDeg (G S N) (laurentDeg S N c) (ρ S N) i :=
  ⟨LinearMap.mem_ker.mpr (by rw [partC_d, LinearMap.mem_ker.mp hz.1, map_zero]),
    fun I _ => part_mem_deg (hz.2 I (Set.mem_univ _))⟩
end GroundTheory.Heights₂.Heights.Kleiman.LaurentCohomProof
