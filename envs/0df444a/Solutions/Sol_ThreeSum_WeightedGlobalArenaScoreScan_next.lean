-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaScoreScan.next
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T22:21:09.778432+00:00
-- url     : https://prove2.me/submissions/d6221fd3-4f84-406f-bf7c-b8208d5b2e84

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaScoreScan
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_KeepInputs_trans
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_cell_lt
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_cell_ge
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_cell_ne
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_cell_protected_ne
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_store_other
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_store_read
import Theorems.Thm_Light_Ends_store


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaScoreScan
open LightWeightedGlobalControllerFactory LightWeightedGlobalSeedScoreFactory
open WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
set_option maxHeartbeats 2000000
variable {p r : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalArenaScoreScan
theorem _root_.solution {I : Input} {A : Inputs} {D : Family (config p r I A 0)}
    {K i : ℕ} {μ ν ξ : ℕ→ℤ} (hcapacity : 106 ≤ I.capacity) (hi : i < I.capacity)
    (h : Invariant I (values D K) μ i ν) (done : (D.candidate i).Done K ν ξ) :
    Invariant I (values D K) μ (i+1) ξ := by
  obtain ⟨ζ,hkeep,rfl⟩ := done
  change Invariant I (values D K) μ (i+1) (store I i (values D K i) ζ)
  constructor
  · intro x hx
    rw [store_other (fun c hc => cell_protected_ne hc hi hx)]
    exact (hkeep x hx.2.1 hx.2.2).trans (h.1 x hx)
  · intro j hj c
    by_cases hji : j=i
    · subst j
      exact store_read hi _ _ c
    · have hjlt : j < i := by omega
      rw [store_other (fun d _ => cell_ne (lt_trans hjlt hi) hi (Or.inr hji))]
      have hbelow : cell I c j < addr I.free I.capacity 16 := by
        have hh := cell_lt (I:=I) (c:=c.val) (lt_trans hjlt hi)
        have hm := Nat.mul_le_mul_right I.capacity (show 10+c.val ≤ 16 by omega)
        unfold addr at *
        omega
      have hheader : cell I c j ≠ addr I.free I.capacity 1+104 := by
        have hh := cell_ge I c.val j
        unfold addr at *
        have hm : 1*I.capacity ≤ (9+c.val)*I.capacity := Nat.mul_le_mul_right _ (by omega)
        nlinarith
      rw [hkeep _ hbelow hheader]
      exact h.2 j hjlt c
end ThreeSum.WeightedGlobalArenaScoreScan
