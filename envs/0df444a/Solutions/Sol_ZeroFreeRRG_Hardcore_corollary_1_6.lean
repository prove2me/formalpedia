-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.corollary_1_6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T04:58:34.337008+00:00
-- url     : https://prove2.me/submissions/2e4ff425-4293-4e8b-8a3c-d1f5eb536ed5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ZeroFreeRRG_Hardcore_ising_rsb_threshold
import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_positive_zero_free
open scoped Classical
open ZeroFreeRRG.Hardcore

theorem solution (d : ℕ) (hd : 3 ≤ d) (δ : ℝ) (hδ : 0 < δ)
    (hδmax : δ < 2 / (Real.sqrt ((d : ℝ) - 1) + 1)) :
    ∃ η : ℝ, 0 < η ∧
      PottsRapidMixing.WithHighProb d (fun n G =>
        ∀ β ∈ nbhd (realSegment
          ((Real.sqrt ((d : ℝ) - 1) - 1) / (Real.sqrt ((d : ℝ) - 1) + 1) + δ) 1) η,
          pottsZ 2 G β ≠ 0) := by
  have hd' : (3:ℝ) ≤ d := by exact_mod_cast hd
  have hden : Real.sqrt ((d : ℝ)-1) + 1 ≠ 0 := by positivity
  have heq : 1 - betaRSB d 2 = 2 / (Real.sqrt ((d : ℝ)-1) + 1) := by
    rw [ising_rsb_threshold d hd]
    field_simp
    <;> ring
  have h := potts_positive_zero_free d 2 hd (by norm_num) δ hδ (by rw [heq]; exact hδmax)
  simpa [ising_rsb_threshold d hd] using h
