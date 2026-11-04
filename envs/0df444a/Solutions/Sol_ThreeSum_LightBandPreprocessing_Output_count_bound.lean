-- Prove2me | solution 1 for ThreeSum.LightBandPreprocessing.Output.count_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:48:47.045731+00:00
-- url     : https://prove2.me/submissions/59524989-1354-449e-8976-7abb471387d4

import Definitions.Def_Submission_ThreeSum_LightBandPreprocessing
import Definitions.Def_Submission_ThreeSum_BandPreprocessingCorrectness
import Theorems.Thm_ThreeSum_BandPartition_size_mono
import Theorems.Thm_ThreeSum_LightBandEnumeration_count_mono


set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPreprocessing
open Light ThreeSum.BandPartition
namespace ThreeSum.LightBandPreprocessing
namespace Output
theorem _root_.solution {μ : ℕ → ℤ} {av ae bv be cv ce dst g : ℕ} {hg : 0 < g}
    {originalA originalB originalC : List ℤ} {r : ℤ}
    (h : Output μ av ae bv be cv ce dst g hg originalA originalB originalC r) :
    0 ≤ r ∧ r ≤ (LightBandEnumeration.count (size originalA.length g)
      (size originalB.length g) (size originalC.length g) : ℤ) := by
  obtain ⟨A,hsA,B,hsB,C,hsC,hr,hA,hB,hC,_⟩ := h
  rw [hr]
  exact ⟨Int.natCast_nonneg _,Int.ofNat_le.mpr
    (LightBandEnumeration.count_mono (size_mono hA.2.1) (size_mono hB.2.1) (size_mono hC.2.1))⟩
end Output
end ThreeSum.LightBandPreprocessing
