-- Prove2me | solution 1 for OutpatientWalkIn.SmallCap.blockProb_pos
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T16:40:01.287566+00:00
-- url     : https://prove2.me/submissions/4e7aa7c0-5f22-41b5-8ba4-4a8a95b748d1

import Mathlib
import Definitions.Def_OutpatientWalkIn_SmallCap_MD1Queue
import Theorems.Thm_OutpatientWalkIn_SmallCap_proposition_C_2_delta
import Theorems.Thm_OutpatientWalkIn_SmallCap_thm2_proof_rate_bounds

open OutpatientWalkIn.SmallCap

theorem solution (lam : ℝ) (hlam : 0 < lam) (μS : ℝ) (hμS : 0 < μS) (δ : ℝ) (hδ : 0 ≤ δ) :
    0 < blockProb lam δ μS := by
  have h1 := (proposition_C_2_delta lam hlam μS hμS).1 (Set.mem_Ici.2 hδ)
    (Set.mem_Ici.2 (by linarith : (0:ℝ) ≤ δ + 1)) (by linarith : δ < δ + 1)
  have h2 := (thm2_proof_rate_bounds lam hlam (δ + 1) (by linarith) μS hμS).2
  have h3 : 0 ≤ blockProb lam (δ + 1) μS := by nlinarith
  simp only at h1
  linarith
