-- Prove2me | solution 1 for RHX100000.segment
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T01:54:16.081382+00:00
-- url     : https://prove2.me/submissions/8e911224-ccb1-47fb-a882-d880ba6e3825

import Definitions.Def_RHX100000_BandData
import Theorems.Thm_Arb4_H1000_E_T121_hAH
import Theorems.Thm_Arb4_H1000_S_L121_clear
import Theorems.Thm_Arb4_k6side_of_B
import Theorems.Thm_Arb4_slabOK_sound
import Theorems.Thm_BandGlue_BandData_CapGeom_of_sqrt
import Theorems.Thm_H11K_boxCert_of_parts_sharp
import Theorems.Thm_H11K_edge_sound_of_split
import Theorems.Thm_H11K_validS_of_B
import Theorems.Thm_H65K_Platform_Bridge520_zeros
import Theorems.Thm_H65K_Platform_High_zeros
import Theorems.Thm_H65K_Platform_Low121_zeros
import Theorems.Thm_H65K_Platform_Low_zeros
import Theorems.Thm_RH1E5_group_000
import Theorems.Thm_RH1E5_group_001
import Theorems.Thm_RH1E5_group_002
import Theorems.Thm_RH1E5_group_003
import Theorems.Thm_RH1E5_group_004
import Theorems.Thm_RH1E5_group_005
import Theorems.Thm_RH1E5_group_006
import Theorems.Thm_RH1E5_group_007
import Theorems.Thm_RH1E5_group_008
import Theorems.Thm_RH1E5_group_009
import Theorems.Thm_RH1E5_group_010
import Theorems.Thm_RH1E5_group_011
import Theorems.Thm_RH1E5_group_012
import Theorems.Thm_RH1E5_group_013
import Theorems.Thm_RH1E5_group_014
import Theorems.Thm_RH1E5_group_015
import Theorems.Thm_RH1E5_group_016
import Theorems.Thm_RH1E5_group_017
import Theorems.Thm_RH1E5_group_018
import Theorems.Thm_RH1E5_group_019
import Theorems.Thm_RH1E5_group_020
import Theorems.Thm_RH1E5_group_021
import Theorems.Thm_RH1E5_group_022
import Theorems.Thm_RH1E5_group_023
import Theorems.Thm_RH1E5_group_024
import Theorems.Thm_RH1E5_group_025
import Theorems.Thm_RH1E5_group_026
import Theorems.Thm_RH1E5_group_027
import Theorems.Thm_RH1E5_group_028
import Theorems.Thm_RH1E5_group_029
import Theorems.Thm_RH1E5_group_030
import Theorems.Thm_RH1E5_group_031
import Theorems.Thm_RH1E5_group_032
import Theorems.Thm_RH1E5_group_033
import Theorems.Thm_RH1E5_group_034
import Theorems.Thm_RH1E5_group_035
import Theorems.Thm_RH1E5_group_036
import Theorems.Thm_RH1E5_group_037
import Theorems.Thm_RH1E5_group_038
import Theorems.Thm_RH1E5_group_039
import Theorems.Thm_RH1E5_group_040
import Theorems.Thm_RH1E5_group_041
import Theorems.Thm_RH1E5_group_042
import Theorems.Thm_RH1E5_group_043
import Theorems.Thm_RH1E5_group_044
import Theorems.Thm_RH1E5_group_045
import Theorems.Thm_RH1E5_group_046
import Theorems.Thm_RH1E5_group_047
import Theorems.Thm_RH1E5_group_048
import Theorems.Thm_RH1E5_group_049
import Theorems.Thm_RH1E5_group_050
import Theorems.Thm_RH1E5_group_051
import Theorems.Thm_RHX100000_Count_chk
import Theorems.Thm_RHX100000_Edge_hAH
import Theorems.Thm_RHX100000_Edge_piece_00
import Theorems.Thm_RHX100000_Edge_piece_01
import Theorems.Thm_RHX100000_Edge_piece_02
import Theorems.Thm_RHX100000_Edge_piece_03
import Theorems.Thm_RHX100000_Edge_piece_04
import Theorems.Thm_RHX100000_Edge_piece_05
import Theorems.Thm_RHX100000_Edge_piece_06
import Theorems.Thm_RHX100000_Edge_piece_07
import Theorems.Thm_RHX100000_Edge_piece_08
import Theorems.Thm_RHX100000_Edge_piece_09
import Theorems.Thm_RHX100000_Edge_piece_10
import Theorems.Thm_RHX100000_Edge_piece_11
import Theorems.Thm_RHX100000_Edge_piece_12
import Theorems.Thm_RHX100000_Edge_piece_13
import Theorems.Thm_RHX100000_Edge_piece_14
import Theorems.Thm_RHX100000_Edge_piece_15
import Theorems.Thm_RHX100000_Edge_piece_16
import Theorems.Thm_RHX100000_Edge_piece_17
import Theorems.Thm_RHX100000_Edge_piece_18
import Theorems.Thm_RHX100000_Edge_piece_19
import Theorems.Thm_RHX100000_Edge_piece_20
import Theorems.Thm_RHX100000_Edge_piece_21
import Theorems.Thm_RHX100000_Edge_piece_22
import Theorems.Thm_RHX100000_Edge_piece_23
import Theorems.Thm_RHX100000_Edge_piece_24
import Theorems.Thm_RHX100000_Edge_piece_25
import Theorems.Thm_RHX100000_Edge_piece_26
import Theorems.Thm_RHX100000_Edge_piece_27
import Theorems.Thm_RHX100000_Edge_piece_28
import Theorems.Thm_RHX100000_Edge_piece_29
import Theorems.Thm_RHX100000_Edge_piece_30
import Theorems.Thm_RHX100000_Edge_piece_31
import Theorems.Thm_RHX100000_Edge_piece_32
import Theorems.Thm_RHX100000_Edge_piece_33
import Theorems.Thm_RHX100000_Edge_piece_34
import Theorems.Thm_RHX100000_Edge_piece_35
import Theorems.Thm_RHX100000_Edge_piece_36
import Theorems.Thm_RHX100000_Edge_piece_37
import Theorems.Thm_RHX100000_Edge_piece_38
import Theorems.Thm_RHX100000_Edge_piece_39
import Theorems.Thm_RHX100000_Edge_piece_40
import Theorems.Thm_RHX100000_Edge_rest
import Theorems.Thm_RHX100000_Slab_cell_0
import Theorems.Thm_RHX100000_Slab_cell_1
import Theorems.Thm_RHX100000_Slab_cell_2
import Theorems.Thm_RHX100000_Slab_cell_3
import Theorems.Thm_RHX100000_Slab_cell_4
import Theorems.Thm_RHX100000_Slab_cell_5
import Theorems.Thm_RHX100000_Slab_cell_6
import Theorems.Thm_RHX100000_Slab_cell_7
import Theorems.Thm_RHX100000_Slab_clear
import Theorems.Thm_RHX100000_bands
import Theorems.Thm_RHX_cellOK_of
import Theorems.Thm_RHX_edgeRest_of
import Theorems.Thm_RHX_pieceJ_of
import Theorems.Thm_RHX_pieceOK_of
import Theorems.Thm_RHX_slabOK_of
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_BandZeros_hLine
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_ZeroFreeBridge_dlvpRateC_lower
import Theorems.Thm_ZetaZeroConfinement_zero_in_band

/-! All nontrivial zeros of the Riemann zeta function with `121 ≤ Im ρ ≤ 100000` lie on the critical line.
    Composition of the published band, count, edge and slab theorems (heights 121 to 65000) with the
    certificates produced here for 65000 to 100000. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Complex Arb4 Arb4.Q BandGlue BandGlue.BandData

namespace RHX100000

theorem bands_121 : RS5.BandZeros 121 100000 138031 := by
  have h1 := RS5.BandZeros.glue (by norm_num) (by norm_num) H65K.Platform.Low121.zeros
    H65K.Platform.Bridge520.zeros
  have h2 := RS5.BandZeros.glue (by norm_num) (by norm_num) h1 H65K.Platform.Low.zeros
  have h3 := RS5.BandZeros.glue (by norm_num) (by norm_num) h2 H65K.Platform.High.zeros
  have h4 := RS5.BandZeros.glue (by norm_num) (by norm_num) h3 RHX100000.bands
  convert h4 using 2 <;> norm_num

theorem chk_valid : H11K.validBS (Q.ofNat 121) (Q.ofNat 100000) (Q.frac 100121 2)
    (Q.frac 9975814658 4) 138031 RHX100000.Count.E = true := by
  have h := RHX100000.Count.chk
  simp only [Bool.and_eq_true] at h
  exact h.1

theorem chk_k6 : k6sideB RHX100000.Count.G0 RHX100000.Count.G1 RHX100000.Count.E = true := by
  have h := RHX100000.Count.chk
  simp only [Bool.and_eq_true] at h
  exact h.2

theorem box : BoxCert (1 / 4000000) (3999999 / 4000000) 121 100000 := by
  have hV := H11K.validS_of_B band (Q.ofNat 121) (Q.ofNat 100000) (Q.frac 100121 2) (Q.frac 9975814658 4)
    RHX100000.Count.E (by simp [band, Q.val, Q.ofNat]) (by simp [band, Q.val, Q.ofNat])
    (by simp [band, Q.val, Q.frac]; norm_num) (by simp [band, Q.val, Q.frac]; norm_num) chk_valid
  have hG : band.CapGeom (5773 / 100000) (3 / 1000) :=
    BandGlue.BandData.CapGeom.of_sqrt 121 100000 ((100121 : ℝ) / 2) ((9975814658 : ℝ) / 4)
      rfl rfl rfl rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hL : band.LineHyp := RS5.BandZeros.hLine bands_121
  have hs0 : EdgeClearGlue.SlabClear (band.T0 - 5773 / 100000) band.T0 := Arb4.H1000.S_L121_clear
  have hs1 : EdgeClearGlue.SlabClear band.T1 (band.T1 + 3 / 1000) := RHX100000.Slab.clear
  have hS := Arb4.k6side_of_B band RHX100000.Count.G0 RHX100000.Count.G1 RHX100000.Count.E
    (by simp [band, RHX100000.Count.G0, Q.val, Q.ofNat]) (by simp [band, RHX100000.Count.G1, Q.val, Q.ofNat]) chk_k6
  have hH1 : DiffractionCore.argChangeHoriz riemannZeta band.T1 2 (-1) ∈
      Set.Icc RHX100000.Count.E.L2.val RHX100000.Count.E.H2.val := RHX100000.Edge.hAH
  have hH0 : DiffractionCore.argChangeHoriz riemannZeta band.T0 2 (-1) ∈
      Set.Icc RHX100000.Count.E.L3.val RHX100000.Count.E.H3.val := Arb4.H1000.E_T121_hAH
  exact H11K.boxCert_of_parts_sharp (lo := 121) (hi := 100000) band RHX100000.Count.E le_rfl le_rfl
    hV hG hL hs0 hs1 hS hH1 hH0

theorem log_le : Real.log 100000 ≤ 12 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h12 : Real.exp 12 = Real.exp 1 ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h12]
  have : (2.7182818283 : ℝ) ^ 12 ≤ Real.exp 1 ^ 12 := pow_le_pow_left₀ (by norm_num) h1.le 12
  nlinarith [this]

/-- **All zeros with `121 ≤ Im ρ ≤ 100000` are on the critical line.** -/
theorem segment : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (121 : ℝ) ≤ ρ.im →
    ρ.im ≤ 100000 → ρ.re = 1 / 2 := by
  intro ρ hz him0 h121 hT
  have hlog0 : 0 < Real.log 100000 := Real.log_pos (by norm_num)
  have haC : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 100000 := by
    rw [le_div_iff₀ hlog0]
    have := ZeroFreeBridge.dlvpRateC_lower
    nlinarith [log_le]
  have hre := ZetaZeroConfinement.zero_in_band (1 / 4000000) 100000 haC (by norm_num) (by norm_num) hz him0 hT
    (by rw [abs_of_pos him0]; linarith)
  obtain ⟨d, hlo, hhi, hS, hI⟩ := box
  exact hS hI.1 hI.2 ρ ⟨hre.1, by linarith [hre.2]⟩ ⟨by linarith, by linarith⟩ hz

end RHX100000

/-- The platform leaf `TaoFivePrimes.rh_verified_block_1e4_1e5`, from `RHX100000.segment`. -/
theorem RHX100000.block_1e4_1e5 (s : ℂ) (hs : riemannZeta s = 0) (h0 : 0 < s.re) (h1 : s.re < 1)
    (ha : 10 ^ 4 ≤ s.im) (hb : s.im ≤ 10 ^ 5) : s.re = 1 / 2 :=
  RHX100000.segment s hs (by linarith) (by norm_num at ha; linarith) (by norm_num at hb; linarith)

/-- The platform leaf `TaoFivePrimes.rh_verified_block_1e4_75k`. -/
theorem RHX100000.block_1e4_75k (s : ℂ) (hs : riemannZeta s = 0) (h0 : 0 < s.re) (h1 : s.re < 1)
    (ha : 10 ^ 4 ≤ s.im) (hb : s.im ≤ 75000) : s.re = 1 / 2 :=
  RHX100000.segment s hs (by linarith) (by norm_num at ha; linarith) (by linarith)
open Complex Arb4 Arb4.Q BandGlue BandGlue.BandData RHX100000 in
theorem solution : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (121 : ℝ) ≤ ρ.im →
    ρ.im ≤ 100000 → ρ.re = 1 / 2 := by
  apply RHX100000.segment <;> assumption
