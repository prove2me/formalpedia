-- Prove2me | solution 1 for Sendov.B18_20.P_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:26:01.265955+00:00
-- url     : https://prove2.me/submissions/520b2ce6-0e92-4b8e-b616-500d4f4eada2

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree18_20

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B18_20
set_option maxHeartbeats 2000000
namespace Sendov.B18_20
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 19 / 2) :
    0 < 1996938880799635773 + 5327542416376042533 * α + 6168567333266685756 * α ^ 2 + 4015726419901684032 * α ^ 3 + 1568562341575363317 * α ^ 4 + 336439630979056719 * α ^ 5 - 5059047712773960 * α ^ 6 - 94154641040290584 * α ^ 7 + 14305270642714822 * α ^ 8 + 337895936432856 * α ^ 9 - 7990669279488 * α ^ 10 - 2592154628256 * α ^ 11 - 177335477376 * α ^ 12 - 6421337472 * α ^ 13 - 134803968 * α ^ 14 - 1555968 * α ^ 15 - 7680 * α ^ 16 := by
  have hu : (0 : ℝ) ≤ 19 - 2 * α := by linarith
  have h0 : (0:ℝ) ≤ 1996938880799635773 * (19 - 2 * α) ^ 16 :=
    mul_nonneg (by norm_num) (pow_nonneg hu 16)
  have h1 : (0:ℝ) ≤ 165125350096733152863 * α ^ 1 * (19 - 2 * α) ^ 15 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 1)) (pow_nonneg hu 15)
  have h2 : (0:ℝ) ≤ 6222082647427442972766 * α ^ 2 * (19 - 2 * α) ^ 14 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 2)) (pow_nonneg hu 14)
  have h3 : (0:ℝ) ≤ 141355820787428498073516 * α ^ 3 * (19 - 2 * α) ^ 13 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 3)) (pow_nonneg hu 13)
  have h4 : (0:ℝ) ≤ 2157735283869217913370909 * α ^ 4 * (19 - 2 * α) ^ 12 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 4)) (pow_nonneg hu 12)
  have h5 : (0:ℝ) ≤ 23307179713209861652797525 * α ^ 5 * (19 - 2 * α) ^ 11 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 5)) (pow_nonneg hu 11)
  have h6 : (0:ℝ) ≤ 181491504176132704398182238 * α ^ 6 * (19 - 2 * α) ^ 10 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 6)) (pow_nonneg hu 10)
  have h7 : (0:ℝ) ≤ 947234591820259386271884708 * α ^ 7 * (19 - 2 * α) ^ 9 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 7)) (pow_nonneg hu 9)
  have h8 : (0:ℝ) ≤ 3056114849066116568052366478 * α ^ 8 * (19 - 2 * α) ^ 8 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 8)) (pow_nonneg hu 8)
  have h9 : (0:ℝ) ≤ 5409419472435810969555104008 * α ^ 9 * (19 - 2 * α) ^ 7 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 9)) (pow_nonneg hu 7)
  have h10 : (0:ℝ) ≤ 3773674627041183640344074704 * α ^ 10 * (19 - 2 * α) ^ 6 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 10)) (pow_nonneg hu 6)
  have h11 : (0:ℝ) ≤ 2563877062588931411214853312 * α ^ 11 * (19 - 2 * α) ^ 5 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 11)) (pow_nonneg hu 5)
  have h12 : (0:ℝ) ≤ 27502208508532453123433891776 * α ^ 12 * (19 - 2 * α) ^ 4 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 12)) (pow_nonneg hu 4)
  have h13 : (0:ℝ) ≤ 85133541744770676359382205696 * α ^ 13 * (19 - 2 * α) ^ 3 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 13)) (pow_nonneg hu 3)
  have h14 : (0:ℝ) ≤ 113617195875176526046213373440 * α ^ 14 * (19 - 2 * α) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 14)) (pow_nonneg hu 2)
  have h15 : (0:ℝ) ≤ 68841959775014032750000000000 * α ^ 15 * (19 - 2 * α) ^ 1 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 15)) (pow_nonneg hu 1)
  have h16 : (0:ℝ) ≤ 13908254927398975000000000000 * α ^ 16 :=
    mul_nonneg (by norm_num) (pow_nonneg hα 16)
  have hid : (19 : ℝ) ^ 16 * (1996938880799635773 + 5327542416376042533 * α + 6168567333266685756 * α ^ 2 + 4015726419901684032 * α ^ 3 + 1568562341575363317 * α ^ 4 + 336439630979056719 * α ^ 5 - 5059047712773960 * α ^ 6 - 94154641040290584 * α ^ 7 + 14305270642714822 * α ^ 8 + 337895936432856 * α ^ 9 - 7990669279488 * α ^ 10 - 2592154628256 * α ^ 11 - 177335477376 * α ^ 12 - 6421337472 * α ^ 13 - 134803968 * α ^ 14 - 1555968 * α ^ 15 - 7680 * α ^ 16) = 1996938880799635773 * (19 - 2 * α) ^ 16 + 165125350096733152863 * α ^ 1 * (19 - 2 * α) ^ 15 + 6222082647427442972766 * α ^ 2 * (19 - 2 * α) ^ 14 + 141355820787428498073516 * α ^ 3 * (19 - 2 * α) ^ 13 + 2157735283869217913370909 * α ^ 4 * (19 - 2 * α) ^ 12 + 23307179713209861652797525 * α ^ 5 * (19 - 2 * α) ^ 11 + 181491504176132704398182238 * α ^ 6 * (19 - 2 * α) ^ 10 + 947234591820259386271884708 * α ^ 7 * (19 - 2 * α) ^ 9 + 3056114849066116568052366478 * α ^ 8 * (19 - 2 * α) ^ 8 + 5409419472435810969555104008 * α ^ 9 * (19 - 2 * α) ^ 7 + 3773674627041183640344074704 * α ^ 10 * (19 - 2 * α) ^ 6 + 2563877062588931411214853312 * α ^ 11 * (19 - 2 * α) ^ 5 + 27502208508532453123433891776 * α ^ 12 * (19 - 2 * α) ^ 4 + 85133541744770676359382205696 * α ^ 13 * (19 - 2 * α) ^ 3 + 113617195875176526046213373440 * α ^ 14 * (19 - 2 * α) ^ 2 + 68841959775014032750000000000 * α ^ 15 * (19 - 2 * α) ^ 1 + 13908254927398975000000000000 * α ^ 16 := by
    ring
  rcases le_total α (19 / (2 * 2)) with h | h
  · have hpos : (0 : ℝ) < 1996938880799635773 * (19 - 2 * α) ^ 16 :=
      mul_pos (by norm_num) (pow_pos (by linarith) 16)
    linarith
  · have hpos : (0 : ℝ) < 13908254927398975000000000000 * α ^ 16 :=
      mul_pos (by norm_num) (pow_pos (by linarith) 16)
    linarith
end Sendov.B18_20
