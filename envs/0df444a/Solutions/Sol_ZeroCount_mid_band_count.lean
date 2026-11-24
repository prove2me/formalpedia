-- Prove2me | solution 1 for ZeroCount.mid_band_count
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-24T03:41:56.117863+00:00
-- url     : https://prove2.me/submissions/2a679b76-7089-4a93-85c8-90ab47677d6b

import Theorems.Thm_Arb4_H1000_E_T121_hAH
import Theorems.Thm_Arb4_H1000_S_L121_clear
import Theorems.Thm_Arb4_Q_cv_frac
import Theorems.Thm_Arb4_Q_cv_nat
import Theorems.Thm_Arb4_k6side_of_B
import Theorems.Thm_BandGlue_BandData_CapGeom_of_sqrt
import Theorems.Thm_H11K_validS_of_B
import Theorems.Thm_H65K_Count121_chk
import Theorems.Thm_H65K_Edge_hAH
import Theorems.Thm_H65K_Slab_clear
import Theorems.Thm_ZeroCount_count_le_of_parts
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Complex Arb4 Arb4.Q

namespace ZeroCount.MidBand

noncomputable def cB : ℂ := ⟨1 / 2, 65121 / 2⟩
noncomputable def RB : ℝ := Real.sqrt (4209284657 / 4)

theorem hs1B : (1 : ℂ) ∉ Metric.ball cB RB := by
  rw [Metric.mem_ball, Complex.dist_eq_re_im]
  unfold cB RB
  intro hlt
  simp only [Complex.one_re, Complex.one_im] at hlt
  have hle : Real.sqrt (4209284657 / 4 : ℝ) ≤
      Real.sqrt (((1 : ℝ) - (1 / 2)) ^ 2 + ((0 : ℝ) - 65121 / 2) ^ 2) :=
    Real.sqrt_le_sqrt (by norm_num)
  linarith [hlt, hle]

noncomputable def band : BandGlue.BandData :=
  ⟨121, 65000, 85250, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cB, RB, hs1B⟩

end ZeroCount.MidBand

open ZeroCount.MidBand in
theorem solution (U : Finset ℂ)
    (hU : ∀ ρ ∈ U, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ (121 : ℝ) ≤ ρ.im ∧ ρ.im ≤ 65000) :
    ∑ ρ ∈ U, analyticOrderNatAt riemannZeta ρ ≤ 85250 := by
  have hc := H65K.Count121.chk
  rw [Bool.and_eq_true] at hc
  have hT0 : band.T0 = (Q.ofNat 121).val := (Q.cv_nat 121).symm
  have hT1 : band.T1 = (Q.ofNat 65000).val := (Q.cv_nat 65000).symm
  have hcc : band.c = (⟨1 / 2, (Q.frac 65121 2).val⟩ : ℂ) := by rw [Q.cv_frac 65121 2]; rfl
  have hR : band.R = Real.sqrt (Q.frac 4209284657 4).val := by rw [Q.cv_frac 4209284657 4]; rfl
  have hG : band.CapGeom (5773 / 100000) (3 / 1000) :=
    BandGlue.BandData.CapGeom.of_sqrt 121 65000 (65121 / 2) (4209284657 / 4) rfl rfl rfl rfl
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ZeroCount.count_le_of_parts band H65K.Count121.E
    (H11K.validS_of_B _ _ _ _ _ H65K.Count121.E hT0 hT1 hcc hR hc.1) hG
    Arb4.H1000.S_L121_clear H65K.Slab.clear
    (k6side_of_B _ H65K.Count121.G0 H65K.Count121.G1 H65K.Count121.E hT0 hT1 hc.2)
    H65K.Edge.hAH Arb4.H1000.E_T121_hAH U hU
