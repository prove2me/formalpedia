-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagProdPrimesDvd_proof_30c2c3fcc710
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:04:32.262053+00:00
-- url     : https://prove2.me/submissions/73c5fa50-7dd7-43cd-ae8b-976f9696e0c0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagProdPrimesDvd

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
open GroundTheory.Heights₂.Heights.RestTerms
open Finset
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace FlagProdPrimesDvd
theorem _root_.solution : FlagProdPrimesDvd.Statement := by
  intro R _ _ ι s p x
  classical
  induction s using Finset.induction_on with
  | empty => intro _ _ _; simp
  | @insert t s ht ih =>
    intro hp hne hdvd
    have hs : (∏ i ∈ s, p i) ∣ x :=
      ih (fun i hi => hp i (mem_insert_of_mem hi))
        (fun i hi j hj hij => hne i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hij)
        (fun i hi => hdvd i (mem_insert_of_mem hi))
    obtain ⟨y, hy⟩ := hs
    have hpt : Prime (p t) := hp t (mem_insert_self t s)
    have hnd : ¬ p t ∣ ∏ i ∈ s, p i := by
      rw [Prime.dvd_finsetProd_iff hpt]
      rintro ⟨j, hj, hdj⟩
      refine hne t (mem_insert_self t s) j (mem_insert_of_mem hj) ?_ hdj
      rintro rfl
      exact ht hj
    have hty : p t ∣ y := by
      have h := hdvd t (mem_insert_self t s)
      rw [hy] at h
      exact (hpt.dvd_or_dvd h).resolve_left hnd
    rw [prod_insert ht, hy, mul_comm (p t)]
    exact mul_dvd_mul_left _ hty
end FlagProdPrimesDvd
end GroundTheory.Heights₂.Heights.RestTerms
