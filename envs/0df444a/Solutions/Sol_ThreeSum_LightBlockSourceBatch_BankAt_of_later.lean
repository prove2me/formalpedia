-- Prove2me | solution 1 for ThreeSum.LightBlockSourceBatch.BankAt.of_later
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:45:12.398999+00:00
-- url     : https://prove2.me/submissions/d1716f2f-cf9b-41a3-8dd5-ad3ba260b0e9

import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatchStep
import Definitions.Def_Submission_ThreeSum_BlockSourceSharing
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatch
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_banks_le_left_cell
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_banks_le_right_cell
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_header_end_le_slot
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_left_cell_lt_later
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_right_cell_lt_later


set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceBatch
open Light BlockEncoding GlobalEncoding BlockIndex BlockCoefficientRows
open SubsetAddress LocalCoverBounds BlockSourceEncoding LightBlockSourceBatchLayout
set_option maxHeartbeats 3500000
set_option maxRecDepth 16000
namespace ThreeSum.LightBlockSourceBatch
namespace BankAt
theorem _root_.solution {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    {h J base count cut i k : ℕ} {μ ν : ℕ → ℤ} {P shift : ℤ}
    {B : Finset β} {b : β → ℤ} {A : Finset γ} {a : γ → ℤ} {q : GlobalOutput h J}
    (H : BankAt μ base count cut i P shift B b A a q)
    (K : KeptBut μ ν (slot base count (J*(512*h)) cut k) (base+2*k) 2)
    (hik : i < k) (hk : k < count) : BankAt ν base count cut i P shift B b A a q := by
  have hhead := header_end_le_slot (base := base) (W := J*(512*h)) (cut := cut) hk
  refine ⟨?_,?_,?_,?_⟩
  · intro j hj S hS
    have hb := banks_le_left_cell base count (J*(512*h)) cut i j S
    unfold banks at hb
    exact (K _ ⟨left_cell_lt_later hik hj hS,Or.inr (by omega)⟩).trans (H.left j hj S hS)
  · intro j hj S hS
    have hb := banks_le_right_cell base count (J*(512*h)) cut i j S
    unfold banks at hb
    exact (K _ ⟨right_cell_lt_later hik hj hS,Or.inr (by omega)⟩).trans (H.right j hj S hS)
  · exact (K _ ⟨by omega,Or.inl (by omega)⟩).trans H.headerLeft
  · exact (K _ ⟨by omega,Or.inl (by omega)⟩).trans H.headerRight
end BankAt
end ThreeSum.LightBlockSourceBatch
