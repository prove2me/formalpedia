-- Prove2me | solution 1 for ThreeSum.LightBlockSourceBatch.BankAt.reuse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:57:34.117194+00:00
-- url     : https://prove2.me/submissions/1e7af65a-fafa-4fa5-97c8-ae0e3c151266

import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatchStep
import Definitions.Def_Submission_ThreeSum_BlockSourceSharing
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatch
import Theorems.Thm_ThreeSum_BlockSourceSharing_stored_left_reuse
import Theorems.Thm_ThreeSum_BlockSourceSharing_stored_right_reuse


set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceBatch
open Light BlockEncoding GlobalEncoding BlockIndex BlockCoefficientRows
open SubsetAddress LocalCoverBounds BlockSourceEncoding LightBlockSourceBatchLayout
set_option maxHeartbeats 3500000
set_option maxRecDepth 16000
namespace ThreeSum.LightBlockSourceBatch
namespace BankAt
theorem _root_.solution {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    {h J base count cut i : ℕ} {μ : ℕ → ℤ} {P shift : ℤ}
    {B : Finset β} {b : β → ℤ} {A : Finset γ} {a : γ → ℤ} {q q' : GlobalOutput h J}
    (H : BankAt μ base count cut i P shift B b A a q)
    (ho : outputOccurrences q = outputOccurrences q') :
    BankAt μ base count cut i P shift B b A a q' :=
  ⟨BlockSourceSharing.stored_left_reuse P B b ho H.left,
    BlockSourceSharing.stored_right_reuse P shift A a ho H.right,H.headerLeft,H.headerRight⟩
end BankAt
end ThreeSum.LightBlockSourceBatch
