-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_part_univ_eq_zero_4f68cd74c221
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:02:19.44954+00:00
-- url     : https://prove2.me/submissions/fc188a83-fd1a-4604-8bea-a8999bf4a852

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
theorem _root_.solution {c : ℤ} (hc : 0 ≤ c) {I : StdCell N} {f : Laurent S N}
    (hf : f ∈ laurentDeg S N c I) : part S Finset.univ f = 0 := by
  ext a
  rw [part_apply, Finsupp.zero_apply]
  split_ifs with h
  · by_contra h'
    have hneg : ∀ j ∈ Finset.univ, a j < 0 := fun j _ => mem_negSet.mp (h ▸ Finset.mem_univ j)
    have := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty hneg
    rw [Finset.sum_const_zero, (mem_exps hf h').1] at this
    omega
  · rfl
end GroundTheory.Heights₂.Heights.Kleiman.LaurentCohomProof
