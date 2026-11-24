-- Prove2me | solution 1 for ZeroCount.low_band_count
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-24T03:42:32.19265+00:00
-- url     : https://prove2.me/submissions/5938b315-7587-426e-aa7f-27d6abe4d248

import Theorems.Thm_Arb4_H1000_S_L121_clear
import Theorems.Thm_Arb4_Q_cv_frac
import Theorems.Thm_Arb4_Q_cv_nat
import Theorems.Thm_Arb4_k6side_of_B
import Theorems.Thm_Arb4_edgeOK_sound
import Theorems.Thm_BandGlue_BandData_CapGeom_of_sqrt
import Theorems.Thm_H11K_validS_of_B
import Theorems.Thm_ZeroCount_count_le_of_parts
import Theorems.Thm_TaoFivePrimes_zeta_ne_zero_strip_im_two_to_fourteen
import Theorems.Thm_zeta_ne_zero_of_mem_strip_of_abs_im_le_two
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Complex Arb4 Arb4.Q

namespace ZeroCount.LowBand
noncomputable def E_T10 : EdgeD where
  tn := 10
  tq := 0
  N := 12
  L := (Q.frac (1243) 500)
  m := 11
  x := fun j => [(Q.frac (2) 1), (Q.frac (7) 4), (Q.frac (5) 4), (Q.frac (3) 4), (Q.frac (1) 4), (Q.frac (0) 1), (Q.frac (-1) 4), (Q.frac (-1) 2), (Q.frac (-5) 8), (Q.frac (-3) 4), (Q.frac (-7) 8), (Q.frac (-1) 1)].getD j (Q.frac (-1) 1)
  pc := fun j => [{ a := 2, b := 0, q := 1, rn := 1, rd := 4, kk := (0), FN := 12598917, FD := 125000000, aQ := (Q.frac (4899) 500), U := (Q.frac (16403) 1000), ga := 0, gb := 0, gq := 16, Gn := 1, Gd := 1, ea := 28, eb := 0, eqd := 16, Rn := 13554, Rd := 1048576, xhi := (Q.frac (9) 4), sigs := (Q.frac (9) 4), Qr := 335200000000000, E := (Q.frac (93) 31250000000000) },
    { a := 3, b := 0, q := 2, rn := 1, rd := 4, kk := (0), FN := 25369299, FD := 250000000, aQ := (Q.frac (9761) 1000), U := (Q.frac (16009) 1000), ga := 0, gb := 0, gq := 16, Gn := 1, Gd := 1, ea := 20, eb := 0, eqd := 16, Rn := 46950, Rd := 1048576, xhi := (Q.frac (7) 4), sigs := (Q.frac (7) 4), Qr := 253900000000000, E := (Q.frac (4051) 500000000000000) },
    { a := 1, b := 0, q := 1, rn := 1, rd := 4, kk := (0), FN := 50842103, FD := 500000000, aQ := (Q.frac (9749) 1000), U := (Q.frac (7811) 500), ga := 0, gb := 0, gq := 16, Gn := 1, Gd := 1, ea := 12, eb := 0, eqd := 16, Rn := 162636, Rd := 1048576, xhi := (Q.frac (5) 4), sigs := (Q.frac (5) 4), Qr := 194000000000000, E := (Q.frac (4457) 200000000000000) },
    { a := 1, b := 0, q := 2, rn := 1, rd := 4, kk := (0), FN := 50713141, FD := 500000000, aQ := (Q.frac (9761) 1000), U := (Q.frac (15241) 1000), ga := 0, gb := 0, gq := 16, Gn := 1, Gd := 1, ea := 4, eb := 0, eqd := 16, Rn := 563386, Rd := 1048576, xhi := (Q.frac (3) 4), sigs := (Q.frac (3) 4), Qr := 149800000000000, E := (Q.frac (62041) 1000000000000000) },
    { a := 1, b := 0, q := 8, rn := 1, rd := 8, kk := (0), FN := 48691577, FD := 1000000000, aQ := (Q.frac (1239) 125), U := (Q.frac (374) 25), ga := 0, gb := 0, gq := 16, Gn := 1, Gd := 1, ea := 0, eb := 0, eqd := 16, Rn := 1048577, Rd := 1048576, xhi := (Q.frac (1) 4), sigs := (Q.frac (1) 4), Qr := 117000000000000, E := (Q.frac (46033) 500000000000000) },
    { a := 0, b := 1, q := 8, rn := 1, rd := 8, kk := (0), FN := 66113757, FD := 1000000000, aQ := (Q.frac (9937) 1000), U := (Q.frac (374) 25), ga := 0, gb := 2, gq := 16, Gn := 1430533, Gd := 1048576, ea := 0, eb := 4, eqd := 16, Rn := 1951621, Rd := 1048576, xhi := (Q.frac (0) 1), sigs := (Q.frac (1) 4), Qr := 117000000000000, E := (Q.frac (174999) 1000000000000000) },
    { a := 0, b := 3, q := 8, rn := 1, rd := 8, kk := (0), FN := 122346993, FD := 1000000000, aQ := (Q.frac (1246) 125), U := (Q.frac (15147) 1000), ga := 0, gb := 6, gq := 16, Gn := 2662522, Gd := 1048576, ea := 0, eb := 8, eqd := 16, Rn := 3632375, Rd := 1048576, xhi := (Q.frac (-1) 4), sigs := (Q.frac (1) 2), Qr := 132200000000000, E := (Q.frac (15041) 40000000000000) },
    { a := 0, b := 9, q := 16, rn := 1, rd := 16, kk := (0), FN := 5989557, FD := 62500000, aQ := (Q.frac (10057) 1000), U := (Q.frac (1911) 125), ga := 0, gb := 9, gq := 16, Gn := 4242673, Gd := 1048576, ea := 0, eb := 10, eqd := 16, Rn := 4955510, Rd := 1048576, xhi := (Q.frac (-1) 2), sigs := (Q.frac (5) 8), Qr := 140600000000000, E := (Q.frac (551587) 1000000000000000) },
    { a := 0, b := 11, q := 16, rn := 1, rd := 16, kk := (0), FN := 130262041, FD := 1000000000, aQ := (Q.frac (10077) 1000), U := (Q.frac (15383) 1000), ga := 0, gb := 11, gq := 16, Gn := 5788115, Gd := 1048576, ea := 0, eb := 12, eqd := 16, Rn := 6760611, Rd := 1048576, xhi := (Q.frac (-5) 8), sigs := (Q.frac (3) 4), Qr := 149800000000000, E := (Q.frac (25333) 31250000000000) },
    { a := 0, b := 13, q := 16, rn := 1, rd := 16, kk := (0), FN := 88498003, FD := 500000000, aQ := (Q.frac (10099) 1000), U := (Q.frac (7739) 500), ga := 0, gb := 13, gq := 16, Gn := 7896502, Gd := 1048576, ea := 0, eb := 14, eqd := 16, Rn := 9223241, Rd := 1048576, xhi := (Q.frac (-3) 4), sigs := (Q.frac (7) 8), Qr := 159600000000000, E := (Q.frac (595769) 500000000000000) },
    { a := 0, b := 1, q := 1, rn := 1, rd := 8, kk := (0), FN := 567209783, FD := 1000000000, aQ := (Q.frac (1259) 125), U := (Q.frac (7811) 500), ga := 0, gb := 16, gq := 16, Gn := 12582913, Gd := 1048576, ea := 0, eb := 18, eqd := 16, Rn := 17166385, Rd := 1048576, xhi := (Q.frac (-7) 8), sigs := (Q.frac (9) 8), Qr := 181700000000000, E := (Q.frac (2582831) 1000000000000000) }].getD j { a := 0, b := 1, q := 1, rn := 1, rd := 8, kk := (0), FN := 567209783, FD := 1000000000, aQ := (Q.frac (1259) 125), U := (Q.frac (7811) 500), ga := 0, gb := 16, gq := 16, Gn := 12582913, Gd := 1048576, ea := 0, eb := 18, eqd := 16, Rn := 17166385, Rd := 1048576, xhi := (Q.frac (-7) 8), sigs := (Q.frac (9) 8), Qr := 181700000000000, E := (Q.frac (2582831) 1000000000000000) }
  D0 := 1000000000
  reLo0 := (1195781904)
  reHi0 := (1200183097)
  imLo0 := (-81371088)
  imHi0 := (-76969896)
  Qp0 := 291384041691072
  Rn0 := 29826163
  Rd0 := 4294967296
  qlo0 := (Q.frac (-68049) 1000000)
  qhi0 := (Q.frac (-64131) 1000000)
  D1 := 1000000000
  reLo1 := (2418182936)
  reHi1 := (2425028205)
  imLo1 := (67133658)
  imHi1 := (73978927)
  Qp1 := 66768286059150
  Rn1 := 51539607553
  Rd1 := 4294967296
  qlo1 := (Q.frac (27683) 1000000)
  qhi1 := (Q.frac (30593) 1000000)
  Lo := (Q.frac (91719) 1000000)
  Hi := (Q.frac (49321) 500000)
noncomputable def E_T1 : EdgeD where
  tn := 3871
  tq := 5
  N := 37
  L := (Q.frac (3611) 1000)
  m := 10
  x := fun j => [(Q.frac (2) 1), (Q.frac (7) 4), (Q.frac (5) 4), (Q.frac (3) 4), (Q.frac (1) 4), (Q.frac (0) 1), (Q.frac (-1) 4), (Q.frac (-1) 2), (Q.frac (-3) 4), (Q.frac (-7) 8), (Q.frac (-1) 1)].getD j (Q.frac (-1) 1)
  pc := fun j => [{ a := 2, b := 0, q := 1, rn := 1, rd := 4, kk := (0), FN := 7548123, FD := 200000000, aQ := (Q.frac (120721) 1000), U := (Q.frac (121667) 1000), ga := 0, gb := 0, gq := 16, Gn := 1, Gd := 1, ea := 28, eb := 0, eqd := 16, Rn := 1891, Rd := 1048576, xhi := (Q.frac (9) 4), sigs := (Q.frac (9) 4), Qr := 1232000000000000000000000000, E := (Q.frac (2066546379) 1000000000000000) },
    { a := 3, b := 0, q := 2, rn := 1, rd := 4, kk := (-1), FN := 37749321, FD := 1000000000, aQ := (Q.frac (60359) 500), U := (Q.frac (60807) 500), ga := 0, gb := 0, gq := 16, Gn := 1, Gd := 1, ea := 20, eb := 0, eqd := 16, Rn := 11492, Rd := 1048576, xhi := (Q.frac (7) 4), sigs := (Q.frac (7) 4), Qr := 1228000000000000000000000000, E := (Q.frac (3247608971) 250000000000000) },
    { a := 1, b := 0, q := 1, rn := 1, rd := 4, kk := (-1), FN := 37816079, FD := 1000000000, aQ := (Q.frac (120717) 1000), U := (Q.frac (30391) 250), ga := 0, gb := 0, gq := 16, Gn := 1, Gd := 1, ea := 12, eb := 0, eqd := 16, Rn := 69897, Rd := 1048576, xhi := (Q.frac (5) 4), sigs := (Q.frac (5) 4), Qr := 1224000000000000000000000000, E := (Q.frac (81841840417) 1000000000000000) },
    { a := 1, b := 0, q := 2, rn := 1, rd := 4, kk := (-2), FN := 19124487, FD := 500000000, aQ := (Q.frac (60359) 500), U := (Q.frac (30379) 250), ga := 0, gb := 0, gq := 16, Gn := 1, Gd := 1, ea := 4, eb := 0, eqd := 16, Rn := 425159, Rd := 1048576, xhi := (Q.frac (3) 4), sigs := (Q.frac (3) 4), Qr := 1220000000000000000000000000, E := (Q.frac (129110256939) 250000000000000) },
    { a := 1, b := 0, q := 8, rn := 1, rd := 8, kk := (-3), FN := 1091033, FD := 250000000, aQ := (Q.frac (24169) 200), U := (Q.frac (121481) 1000), ga := 0, gb := 0, gq := 16, Gn := 1, Gd := 1, ea := 0, eb := 0, eqd := 16, Rn := 1048577, Rd := 1048576, xhi := (Q.frac (1) 4), sigs := (Q.frac (1) 4), Qr := 1217000000000000000000000000, E := (Q.frac (1297045697763) 1000000000000000) },
    { a := 0, b := 1, q := 8, rn := 1, rd := 8, kk := (-4), FN := 8084901, FD := 1000000000, aQ := (Q.frac (120847) 1000), U := (Q.frac (121481) 1000), ga := 0, gb := 2, gq := 16, Gn := 1646742, Gd := 1048576, ea := 0, eb := 4, eqd := 16, Rn := 2586131, Rd := 1048576, xhi := (Q.frac (0) 1), sigs := (Q.frac (1) 4), Qr := 1217000000000000000000000000, E := (Q.frac (326699785773) 100000000000000) },
    { a := 0, b := 3, q := 8, rn := 1, rd := 8, kk := (-4), FN := 20123703, FD := 1000000000, aQ := (Q.frac (2417) 20), U := (Q.frac (15188) 125), ga := 0, gb := 6, gq := 16, Gn := 4061400, Gd := 1048576, ea := 0, eb := 8, eqd := 16, Rn := 6378240, Rd := 1048576, xhi := (Q.frac (-1) 4), sigs := (Q.frac (1) 2), Qr := 1218000000000000000000000000, E := (Q.frac (8239406364393) 1000000000000000) },
    { a := 0, b := 5, q := 8, rn := 1, rd := 8, kk := (-4), FN := 10024383, FD := 200000000, aQ := (Q.frac (120853) 1000), U := (Q.frac (15191) 125), ga := 0, gb := 10, gq := 16, Gn := 10016732, Gd := 1048576, ea := 0, eb := 12, eqd := 16, Rn := 15730816, Rd := 1048576, xhi := (Q.frac (-1) 2), sigs := (Q.frac (3) 4), Qr := 1220000000000000000000000000, E := (Q.frac (20806746565729) 1000000000000000) },
    { a := 0, b := 13, q := 16, rn := 1, rd := 16, kk := (-4), FN := 57277551, FD := 1000000000, aQ := (Q.frac (60459) 500), U := (Q.frac (60773) 500), ga := 0, gb := 13, gq := 16, Gn := 19713505, Gd := 1048576, ea := 0, eb := 14, eqd := 16, Rn := 24704522, Rd := 1048576, xhi := (Q.frac (-3) 4), sigs := (Q.frac (7) 8), Qr := 1221000000000000000000000000, E := (Q.frac (33070268228673) 1000000000000000) },
    { a := 0, b := 1, q := 1, rn := 1, rd := 8, kk := (-4), FN := 197144931, FD := 1000000000, aQ := (Q.frac (120859) 1000), U := (Q.frac (30391) 250), ga := 0, gb := 16, gq := 16, Gn := 38797313, Gd := 1048576, ea := 0, eb := 18, eqd := 16, Rn := 60929395, Rd := 1048576, xhi := (Q.frac (-7) 8), sigs := (Q.frac (9) 8), Qr := 1223000000000000000000000000, E := (Q.frac (41786854355881) 500000000000000) }].getD j { a := 0, b := 1, q := 1, rn := 1, rd := 8, kk := (-4), FN := 197144931, FD := 1000000000, aQ := (Q.frac (120859) 1000), U := (Q.frac (30391) 250), ga := 0, gb := 16, gq := 16, Gn := 38797313, Gd := 1048576, ea := 0, eb := 18, eqd := 16, Rn := 60929395, Rd := 1048576, xhi := (Q.frac (-7) 8), sigs := (Q.frac (9) 8), Qr := 1223000000000000000000000000, E := (Q.frac (41786854355881) 500000000000000) }
  D0 := 1000000000
  reLo0 := (892194427)
  reHi0 := (896060226)
  imLo0 := (-265198016)
  imHi0 := (-261332217)
  Qp0 := 45361121596189295761841218345067374891302103957
  Rn0 := 3137304
  Rd0 := 4294967296
  qlo0 := (Q.frac (-297243) 1000000)
  qhi0 := (Q.frac (-58329) 200000)
  D1 := 1000000000
  reLo1 := (-78354251254)
  reHi1 := (-78090893754)
  imLo1 := (8899933202)
  imHi1 := (9163290702)
  Qp1 := 44586612212686949816384396026605898705430634057
  Rn1 := 158913789953
  Rd1 := 4294967296
  qlo1 := (Q.frac (-58671) 500000)
  qhi1 := (Q.frac (-22717) 200000)
  Lo := (Q.frac (-2975559) 1000000)
  Hi := (Q.frac (-591489) 200000)

def G0 : GamD := ⟨Q.ofNat 10, 5, 13, 5, 13, 1, 3, 1, 3⟩
def G1 : GamD := ⟨Q.frac 3871 32, 12, 13, 12, 13, 1, 3, 1, 3⟩
noncomputable def E : EnclQ := ⟨Q.frac (-249) 250, Q.frac 249 250, E_T1.Lo, E_T1.Hi, E_T10.Lo, E_T10.Hi,
  Q.frac 121148 1000, Q.frac 121203 1000, Q.frac 121080 1000, Q.frac 121133 1000⟩

theorem ok10 : edgeOK E_T10 = true := by decide +kernel
theorem ok1 : edgeOK E_T1 = true := by decide +kernel
theorem chk : (H11K.validBS (Q.ofNat 10) (Q.frac 3871 32) (Q.frac 4191 64)
    (Q.frac 1577352637 512000) 38 E && k6sideB G0 G1 E) = true := by decide +kernel

noncomputable def cB : ℂ := ⟨1 / 2, 4191 / 64⟩
noncomputable def RB : ℝ := Real.sqrt (1577352637 / 512000)

theorem hs1B : (1 : ℂ) ∉ Metric.ball cB RB := by
  rw [Metric.mem_ball, Complex.dist_eq_re_im]
  unfold cB RB
  intro hlt
  simp only [Complex.one_re, Complex.one_im] at hlt
  have hle : Real.sqrt (1577352637 / 512000 : ℝ) ≤
      Real.sqrt (((1 : ℝ) - (1 / 2)) ^ 2 + ((0 : ℝ) - 4191 / 64) ^ 2) :=
    Real.sqrt_le_sqrt (by norm_num)
  linarith [hlt, hle]

noncomputable def band : BandGlue.BandData :=
  ⟨10, 3871 / 32, 38, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cB, RB, hs1B⟩

theorem slab0 : EdgeClearGlue.SlabClear (band.T0 - 1 / 40) band.T0 := by
  intro x y hx0 hx1 hy0 hy1
  have h1 : band.T0 = 10 := rfl
  rw [h1] at hy0 hy1
  apply TaoFivePrimes.zeta_ne_zero_strip_im_two_to_fourteen <;> simp <;> linarith

theorem slab1 : EdgeClearGlue.SlabClear band.T1 (band.T1 + 1 / 40) := by
  intro x y hx0 hx1 hy0 hy1
  have h1 : band.T1 = 3871 / 32 := rfl
  rw [h1] at hy0 hy1
  exact Arb4.H1000.S_L121_clear x y hx0 hx1 (by linarith) (by linarith)

theorem hH1 : DiffractionCore.argChangeHoriz riemannZeta band.T1 2 (-1) ∈
    Set.Icc E.L2.val E.H2.val := by
  have h := edgeOK_sound E_T1 ok1
  have hT : E_T1.T = band.T1 := by
    show (3871 : ℝ) / 2 ^ 5 = 3871 / 32
    norm_num
  rw [hT] at h
  exact h

theorem hH0 : DiffractionCore.argChangeHoriz riemannZeta band.T0 2 (-1) ∈
    Set.Icc E.L3.val E.H3.val := by
  have h := edgeOK_sound E_T10 ok10
  have hT : E_T10.T = band.T0 := by
    show ((10 : ℕ) : ℝ) / 2 ^ 0 = 10
    norm_num
  rw [hT] at h
  exact h

end ZeroCount.LowBand

open ZeroCount.LowBand in
theorem solution (U : Finset ℂ)
    (hU : ∀ ρ ∈ U, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ 121) :
    ∑ ρ ∈ U, analyticOrderNatAt riemannZeta ρ ≤ 38 := by
  have hc := chk
  rw [Bool.and_eq_true] at hc
  have hT0 : band.T0 = (Q.ofNat 10).val := (Q.cv_nat 10).symm
  have hT1 : band.T1 = (Q.frac 3871 32).val := (Q.cv_frac 3871 32).symm
  have hcc : band.c = (⟨1 / 2, (Q.frac 4191 64).val⟩ : ℂ) := by rw [Q.cv_frac 4191 64]; rfl
  have hR : band.R = Real.sqrt (Q.frac 1577352637 512000).val := by
    rw [Q.cv_frac 1577352637 512000]; rfl
  have hG : band.CapGeom (1 / 40) (1 / 40) :=
    BandGlue.BandData.CapGeom.of_sqrt 10 (3871 / 32) (4191 / 64) (1577352637 / 512000) rfl rfl rfl rfl
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hG0 : band.T0 = G0.T.val := hT0
  have hG1 : band.T1 = G1.T.val := hT1
  refine ZeroCount.count_le_of_parts band E
    (H11K.validS_of_B _ _ _ _ _ E hT0 hT1 hcc hR hc.1) hG slab0 slab1
    (k6side_of_B _ G0 G1 E hG0 hG1 hc.2) hH1 hH0 U ?_
  intro ρ hρ
  obtain ⟨hz, h0, h1, h2, h3⟩ := hU ρ hρ
  refine ⟨hz, h0, h1, ?_, ?_⟩
  · show (10 : ℝ) ≤ ρ.im
    by_contra hlt
    push Not at hlt
    have hs : ρ = ((ρ.re : ℝ) : ℂ) + ((ρ.im : ℝ) : ℂ) * I := (Complex.re_add_im ρ).symm
    rcases le_or_gt ρ.im 2 with hle | hgt
    · exact zeta_ne_zero_of_mem_strip_of_abs_im_le_two ρ h0 h1
        (by rw [abs_of_pos h2]; exact hle) hz
    · exact TaoFivePrimes.zeta_ne_zero_strip_im_two_to_fourteen ρ h0 h1 hgt.le (by linarith) hz
  · show ρ.im ≤ 3871 / 32
    by_contra hlt
    push Not at hlt
    have hs : ρ = ((ρ.re : ℝ) : ℂ) + ((ρ.im : ℝ) : ℂ) * I := (Complex.re_add_im ρ).symm
    apply Arb4.H1000.S_L121_clear ρ.re ρ.im h0 h1 (by linarith) h3
    rw [← hs]; exact hz
