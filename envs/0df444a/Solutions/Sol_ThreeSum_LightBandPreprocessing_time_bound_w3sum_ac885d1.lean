-- Prove2me | solution 1 for ThreeSum.LightBandPreprocessing.time_bound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:30:16.515659+00:00
-- url     : https://prove2.me/submissions/ccd8ee8f-0404-4bc1-b582-d58f0d97e47a

import Definitions.Def_Submission_ThreeSum_LightBandPreprocessing
import Definitions.Def_Submission_ThreeSum_BandPreprocessingCorrectness
import Theorems.Thm_ThreeSum_BandPartition_size_le
import Theorems.Thm_ThreeSum_LightBandEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightBandPartition_time_bound
import Theorems.Thm_ThreeSum_LightKaratsuba_time_bound
import Theorems.Thm_ThreeSum_LightNormalize_time_bound
import Theorems.Thm_ThreeSum_LightSmallDivide_time_bound
import Theorems.Thm_ThreeSum_LightSortedBands_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPreprocessing
open Light ThreeSum.BandPartition
namespace ThreeSum.LightBandPreprocessing
theorem _root_.solution (a b c g : ℕ) :
    time a b c g ≤
      2100*(a+b+c+1)*(Nat.clog 2 (a+b+c)+1)+
      1000*(LightBandEnumeration.count (size a g) (size b g) (size c g)+a+b+c+1)*
        (LightBandEnumeration.width (size a g) (size b g) (size c g)+1)+400 := by
  have hn (n : ℕ) (hn : n ≤ a+b+c) :
      LightSortedBands.time n ≤ 700*(a+b+c+1)*(Nat.clog 2 (a+b+c)+1) := by
    apply (LightSortedBands.time_bound n).trans
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 700 (by omega))
      (Nat.add_le_add_right (Nat.clog_mono_right 2 hn) 1)
  have ha := hn a (by omega)
  have hb := hn b (by omega)
  have hc := hn c (by omega)
  have henum := LightBandEnumeration.time_bound (size a g) (size b g) (size c g)
  have henum' : LightBandEnumeration.time (size a g) (size b g) (size c g) ≤
      1000*(LightBandEnumeration.count (size a g) (size b g) (size c g)+a+b+c+1)*
        (LightBandEnumeration.width (size a g) (size b g) (size c g)+1) := by
    apply henum.trans
    have hsum : size a g+size b g+size c g ≤ a+b+c :=
      Nat.add_le_add (Nat.add_le_add (size_le a g) (size_le b g)) (size_le c g)
    apply Nat.mul_le_mul_right
    apply Nat.mul_le_mul_left
    omega
  unfold time LightHeaderBands.time
  nlinarith
end ThreeSum.LightBandPreprocessing
