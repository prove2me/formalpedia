-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_vertical_center_right_enclosure
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T12:37:51.088989+00:00
-- url     : https://prove2.me/submissions/a7e2ab05-ee97-4ca4-b030-adab3c7f61d5

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighVerticalCenterValuesRight
import Definitions.Def_TaoFivePrimes_RHHighVerticalAnalyticValues
import Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_center_semantic
import Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_center_sum_right
import Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_center_right_packet00
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHHighBundledVerticalCenterRight
theorem packet01 : RHHighVerticalCenter.packet ⟨2,by decide⟩ 1=((RHHighVerticalCenterRight.rows[1]?).getD []) := by decide +kernel
theorem packet02 : RHHighVerticalCenter.packet ⟨2,by decide⟩ 2=((RHHighVerticalCenterRight.rows[2]?).getD []) := by decide +kernel
theorem packet03 : RHHighVerticalCenter.packet ⟨2,by decide⟩ 3=((RHHighVerticalCenterRight.rows[3]?).getD []) := by decide +kernel
theorem packet04 : RHHighVerticalCenter.packet ⟨2,by decide⟩ 4=((RHHighVerticalCenterRight.rows[4]?).getD []) := by decide +kernel
theorem packet05 : RHHighVerticalCenter.packet ⟨2,by decide⟩ 5=((RHHighVerticalCenterRight.rows[5]?).getD []) := by decide +kernel
theorem packet06 : RHHighVerticalCenter.packet ⟨2,by decide⟩ 6=((RHHighVerticalCenterRight.rows[6]?).getD []) := by decide +kernel
theorem packet07 : RHHighVerticalCenter.packet ⟨2,by decide⟩ 7=((RHHighVerticalCenterRight.rows[7]?).getD []) := by decide +kernel
theorem packet08 : RHHighVerticalCenter.packet ⟨2,by decide⟩ 8=((RHHighVerticalCenterRight.rows[8]?).getD []) := by decide +kernel
theorem packet09 : RHHighVerticalCenter.packet ⟨2,by decide⟩ 9=((RHHighVerticalCenterRight.rows[9]?).getD []) := by decide +kernel
theorem packet10 : RHHighVerticalCenter.packet ⟨2,by decide⟩ 10=((RHHighVerticalCenterRight.rows[10]?).getD []) := by decide +kernel
theorem packet11 : RHHighVerticalCenter.packet ⟨2,by decide⟩ 11=((RHHighVerticalCenterRight.rows[11]?).getD []) := by decide +kernel
theorem packet12 : RHHighVerticalCenter.packet ⟨2,by decide⟩ 12=((RHHighVerticalCenterRight.rows[12]?).getD []) := by decide +kernel
theorem packet13 : RHHighVerticalCenter.packet ⟨2,by decide⟩ 13=((RHHighVerticalCenterRight.rows[13]?).getD []) := by decide +kernel
theorem packet14 : RHHighVerticalCenter.packet ⟨2,by decide⟩ 14=((RHHighVerticalCenterRight.rows[14]?).getD []) := by decide +kernel
theorem packet15 : RHHighVerticalCenter.packet ⟨2,by decide⟩ 15=((RHHighVerticalCenterRight.rows[15]?).getD []) := by decide +kernel
theorem packet16 : RHHighVerticalCenter.packet ⟨2,by decide⟩ 16=((RHHighVerticalCenterRight.rows[16]?).getD []) := by decide +kernel
theorem packet17 : RHHighVerticalCenter.packet ⟨2,by decide⟩ 17=((RHHighVerticalCenterRight.rows[17]?).getD []) := by decide +kernel
theorem packet18 : RHHighVerticalCenter.packet ⟨2,by decide⟩ 18=((RHHighVerticalCenterRight.rows[18]?).getD []) := by decide +kernel
theorem packet19 : RHHighVerticalCenter.packet ⟨2,by decide⟩ 19=((RHHighVerticalCenterRight.rows[19]?).getD []) := by decide +kernel
theorem packet20 : RHHighVerticalCenter.packet ⟨2,by decide⟩ 20=((RHHighVerticalCenterRight.rows[20]?).getD []) := by decide +kernel
theorem packet21 : RHHighVerticalCenter.packet ⟨2,by decide⟩ 21=((RHHighVerticalCenterRight.rows[21]?).getD []) := by decide +kernel
theorem packet22 : RHHighVerticalCenter.packet ⟨2,by decide⟩ 22=((RHHighVerticalCenterRight.rows[22]?).getD []) := by decide +kernel
theorem packet23 : RHHighVerticalCenter.packet ⟨2,by decide⟩ 23=((RHHighVerticalCenterRight.rows[23]?).getD []) := by decide +kernel
theorem packet24 : RHHighVerticalCenter.packet ⟨2,by decide⟩ 24=((RHHighVerticalCenterRight.rows[24]?).getD []) := by decide +kernel
theorem packet25 : RHHighVerticalCenter.packet ⟨2,by decide⟩ 25=((RHHighVerticalCenterRight.rows[25]?).getD []) := by decide +kernel
theorem packet26 : RHHighVerticalCenter.packet ⟨2,by decide⟩ 26=((RHHighVerticalCenterRight.rows[26]?).getD []) := by decide +kernel
theorem packet27 : RHHighVerticalCenter.packet ⟨2,by decide⟩ 27=((RHHighVerticalCenterRight.rows[27]?).getD []) := by decide +kernel
theorem packet28 : RHHighVerticalCenter.packet ⟨2,by decide⟩ 28=((RHHighVerticalCenterRight.rows[28]?).getD []) := by decide +kernel
theorem packet29 : RHHighVerticalCenter.packet ⟨2,by decide⟩ 29=((RHHighVerticalCenterRight.rows[29]?).getD []) := by decide +kernel
theorem packet30 : RHHighVerticalCenter.packet ⟨2,by decide⟩ 30=((RHHighVerticalCenterRight.rows[30]?).getD []) := by decide +kernel
theorem packet31 : RHHighVerticalCenter.packet ⟨2,by decide⟩ 31=((RHHighVerticalCenterRight.rows[31]?).getD []) := by decide +kernel
end RHHighBundledVerticalCenterRight
theorem solution (n : Nat) (hn:n<55) :
 let p:=((RHHighVerticalCenterValuesRight.values[n]?).getD (0,0))
 ‖((p.1:ℂ)+(p.2:ℂ)*Complex.I)/(2:ℂ)^128-RHHighVerticalAnalyticValues.center ⟨2,by decide⟩ n‖≤2048/10^18 := by
 have hl:RHHighVerticalCenterRight.rows.length=32:=by decide +kernel
 have hp (b : Nat) (hb:b<32) : RHHighVerticalCenter.packet ⟨2,by decide⟩ b=(RHHighVerticalCenterRight.rows[b]?).getD [] := by
  interval_cases b
  · exact TaoFivePrimes.rh_high_height_vertical_center_right_packet00
  · exact RHHighBundledVerticalCenterRight.packet01
  · exact RHHighBundledVerticalCenterRight.packet02
  · exact RHHighBundledVerticalCenterRight.packet03
  · exact RHHighBundledVerticalCenterRight.packet04
  · exact RHHighBundledVerticalCenterRight.packet05
  · exact RHHighBundledVerticalCenterRight.packet06
  · exact RHHighBundledVerticalCenterRight.packet07
  · exact RHHighBundledVerticalCenterRight.packet08
  · exact RHHighBundledVerticalCenterRight.packet09
  · exact RHHighBundledVerticalCenterRight.packet10
  · exact RHHighBundledVerticalCenterRight.packet11
  · exact RHHighBundledVerticalCenterRight.packet12
  · exact RHHighBundledVerticalCenterRight.packet13
  · exact RHHighBundledVerticalCenterRight.packet14
  · exact RHHighBundledVerticalCenterRight.packet15
  · exact RHHighBundledVerticalCenterRight.packet16
  · exact RHHighBundledVerticalCenterRight.packet17
  · exact RHHighBundledVerticalCenterRight.packet18
  · exact RHHighBundledVerticalCenterRight.packet19
  · exact RHHighBundledVerticalCenterRight.packet20
  · exact RHHighBundledVerticalCenterRight.packet21
  · exact RHHighBundledVerticalCenterRight.packet22
  · exact RHHighBundledVerticalCenterRight.packet23
  · exact RHHighBundledVerticalCenterRight.packet24
  · exact RHHighBundledVerticalCenterRight.packet25
  · exact RHHighBundledVerticalCenterRight.packet26
  · exact RHHighBundledVerticalCenterRight.packet27
  · exact RHHighBundledVerticalCenterRight.packet28
  · exact RHHighBundledVerticalCenterRight.packet29
  · exact RHHighBundledVerticalCenterRight.packet30
  · exact RHHighBundledVerticalCenterRight.packet31
 have h:=TaoFivePrimes.rh_high_height_vertical_center_semantic ⟨2,by decide⟩ RHHighVerticalCenterRight.rows hl hp n hn
 change (let p:=(RHHighVerticalCenterRight.coefficients[n]?).getD (0,0)
  ‖((p.1:ℂ)+(p.2:ℂ)*Complex.I)/(2:ℂ)^128-
  RHHighVerticalAnalyticValues.center ⟨2,by decide⟩ n‖≤2048/10^18) at h
 rw[TaoFivePrimes.rh_high_height_vertical_center_sum_right.1] at h
 exact h
#print axioms solution
