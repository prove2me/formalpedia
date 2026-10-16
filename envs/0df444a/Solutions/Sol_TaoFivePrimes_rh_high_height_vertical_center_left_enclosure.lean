-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_vertical_center_left_enclosure
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T12:37:52.903041+00:00
-- url     : https://prove2.me/submissions/1f75571f-1219-4c38-8731-e59ccf5e1ab2

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighVerticalCenterValuesLeft
import Definitions.Def_TaoFivePrimes_RHHighVerticalAnalyticValues
import Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_center_semantic
import Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_center_sum_left
import Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_center_left_packet00
import Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_center_left_packet01
import Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_center_left_packet02
import Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_center_left_packet03
import Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_center_left_packet04
import Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_center_left_packet05
import Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_center_left_packet06
import Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_center_left_packet07
import Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_center_left_packet08
import Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_center_left_packet09
import Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_center_left_packet10
import Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_center_left_packet11
import Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_center_left_packet12
import Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_center_left_packet13
import Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_center_left_packet14
import Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_center_left_packet15
import Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_center_left_packet16
import Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_center_left_packet17
import Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_center_left_packet18
import Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_center_left_packet19
import Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_center_left_packet20
import Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_center_left_packet21
import Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_center_left_packet22
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHHighBundledVerticalCenterLeft
theorem packet23 : RHHighVerticalCenter.packet ⟨0,by decide⟩ 23=((RHHighVerticalCenterLeft.rows[23]?).getD []) := by decide +kernel
theorem packet24 : RHHighVerticalCenter.packet ⟨0,by decide⟩ 24=((RHHighVerticalCenterLeft.rows[24]?).getD []) := by decide +kernel
theorem packet25 : RHHighVerticalCenter.packet ⟨0,by decide⟩ 25=((RHHighVerticalCenterLeft.rows[25]?).getD []) := by decide +kernel
theorem packet26 : RHHighVerticalCenter.packet ⟨0,by decide⟩ 26=((RHHighVerticalCenterLeft.rows[26]?).getD []) := by decide +kernel
theorem packet27 : RHHighVerticalCenter.packet ⟨0,by decide⟩ 27=((RHHighVerticalCenterLeft.rows[27]?).getD []) := by decide +kernel
theorem packet28 : RHHighVerticalCenter.packet ⟨0,by decide⟩ 28=((RHHighVerticalCenterLeft.rows[28]?).getD []) := by decide +kernel
theorem packet29 : RHHighVerticalCenter.packet ⟨0,by decide⟩ 29=((RHHighVerticalCenterLeft.rows[29]?).getD []) := by decide +kernel
theorem packet30 : RHHighVerticalCenter.packet ⟨0,by decide⟩ 30=((RHHighVerticalCenterLeft.rows[30]?).getD []) := by decide +kernel
theorem packet31 : RHHighVerticalCenter.packet ⟨0,by decide⟩ 31=((RHHighVerticalCenterLeft.rows[31]?).getD []) := by decide +kernel
end RHHighBundledVerticalCenterLeft
theorem solution (n : Nat) (hn:n<55) :
 let p:=((RHHighVerticalCenterValuesLeft.values[n]?).getD (0,0))
 ‖((p.1:ℂ)+(p.2:ℂ)*Complex.I)/(2:ℂ)^128-RHHighVerticalAnalyticValues.center ⟨0,by decide⟩ n‖≤2048/10^18 := by
 have hl:RHHighVerticalCenterLeft.rows.length=32:=by decide +kernel
 have hp (b : Nat) (hb:b<32) : RHHighVerticalCenter.packet ⟨0,by decide⟩ b=(RHHighVerticalCenterLeft.rows[b]?).getD [] := by
  interval_cases b
  · exact TaoFivePrimes.rh_high_height_vertical_center_left_packet00
  · exact TaoFivePrimes.rh_high_height_vertical_center_left_packet01
  · exact TaoFivePrimes.rh_high_height_vertical_center_left_packet02
  · exact TaoFivePrimes.rh_high_height_vertical_center_left_packet03
  · exact TaoFivePrimes.rh_high_height_vertical_center_left_packet04
  · exact TaoFivePrimes.rh_high_height_vertical_center_left_packet05
  · exact TaoFivePrimes.rh_high_height_vertical_center_left_packet06
  · exact TaoFivePrimes.rh_high_height_vertical_center_left_packet07
  · exact TaoFivePrimes.rh_high_height_vertical_center_left_packet08
  · exact TaoFivePrimes.rh_high_height_vertical_center_left_packet09
  · exact TaoFivePrimes.rh_high_height_vertical_center_left_packet10
  · exact TaoFivePrimes.rh_high_height_vertical_center_left_packet11
  · exact TaoFivePrimes.rh_high_height_vertical_center_left_packet12
  · exact TaoFivePrimes.rh_high_height_vertical_center_left_packet13
  · exact TaoFivePrimes.rh_high_height_vertical_center_left_packet14
  · exact TaoFivePrimes.rh_high_height_vertical_center_left_packet15
  · exact TaoFivePrimes.rh_high_height_vertical_center_left_packet16
  · exact TaoFivePrimes.rh_high_height_vertical_center_left_packet17
  · exact TaoFivePrimes.rh_high_height_vertical_center_left_packet18
  · exact TaoFivePrimes.rh_high_height_vertical_center_left_packet19
  · exact TaoFivePrimes.rh_high_height_vertical_center_left_packet20
  · exact TaoFivePrimes.rh_high_height_vertical_center_left_packet21
  · exact TaoFivePrimes.rh_high_height_vertical_center_left_packet22
  · exact RHHighBundledVerticalCenterLeft.packet23
  · exact RHHighBundledVerticalCenterLeft.packet24
  · exact RHHighBundledVerticalCenterLeft.packet25
  · exact RHHighBundledVerticalCenterLeft.packet26
  · exact RHHighBundledVerticalCenterLeft.packet27
  · exact RHHighBundledVerticalCenterLeft.packet28
  · exact RHHighBundledVerticalCenterLeft.packet29
  · exact RHHighBundledVerticalCenterLeft.packet30
  · exact RHHighBundledVerticalCenterLeft.packet31
 have h:=TaoFivePrimes.rh_high_height_vertical_center_semantic ⟨0,by decide⟩ RHHighVerticalCenterLeft.rows hl hp n hn
 change (let p:=(RHHighVerticalCenterLeft.coefficients[n]?).getD (0,0)
  ‖((p.1:ℂ)+(p.2:ℂ)*Complex.I)/(2:ℂ)^128-
  RHHighVerticalAnalyticValues.center ⟨0,by decide⟩ n‖≤2048/10^18) at h
 rw[TaoFivePrimes.rh_high_height_vertical_center_sum_left.1] at h
 exact h
#print axioms solution
