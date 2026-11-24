-- Prove2me | solution 1 for TSPSDPGap.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-24T08:08:48.90521+00:00
-- url     : https://prove2.me/submissions/d5e7b15c-7987-4d84-841d-62c1b5dbcd07

import Mathlib
import Definitions.Def_TSPSDPGap_integralityGapSDP2
import Theorems.Thm_TSPSDPGap_proposition_4_4
import Theorems.Thm_TSPSDPGap_simplicial_tsp_opt
import Theorems.Thm_TSPSDPGap_sdp2_objective_bound

open scoped ENNReal
open TSPSDPGap

theorem solution (r s : (n : ℕ) → Fin (n + 1)) (z : ℕ) :
    (z : ℝ≥0∞) ≤ integralityGapSDP2 r s := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  let g : ℕ := 4 * z
  have hg : Even g := ⟨2 * z, by omega⟩
  have hg2 : 2 ≤ g := by omega
  obtain ⟨c, hc⟩ := sdp2_objective_bound g hg hg2
  obtain ⟨m, hm⟩ := exists_nat_gt c
  let n : ℕ := (m + 2) * g
  have hgn : g ∣ n := ⟨m + 2, mul_comm (m + 2) g⟩
  have hlt : g < n := by
    dsimp [n]
    nlinarith
  have hn2 : 2 ≤ n := by omega
  let D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := simplicialCostExt g n (s n)
  have hobj_bound : sdp2Objective n D (r n) (s n) (Ymat g n) ≤ 4 := by
    have h1 : sdp2Objective n D (r n) (s n) (Ymat g n) ≤ c / (n : ℝ) + 2 :=
      hc n hgn hlt (r n) (s n)
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hm_le_n : (m : ℝ) ≤ (n : ℝ) := by
      have : m ≤ n := by
        dsimp [n]
        nlinarith
      exact_mod_cast this
    have hdiv : c / (n : ℝ) ≤ 2 := by
      rw [div_le_iff₀ hn_pos]
      linarith
    linarith
  have hfeas : IsSDP1Feasible n (Ymat g n) := proposition_4_4 g n hg hg2 hgn hlt
  have hsdp : sdp2Opt n D (r n) (s n) ≤ 4 := by
    unfold sdp2Opt
    calc
      (⨅ (Y : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ) (_ : IsSDP1Feasible n Y),
          ENNReal.ofReal (sdp2Objective n D (r n) (s n) Y))
        ≤ ENNReal.ofReal (sdp2Objective n D (r n) (s n) (Ymat g n)) :=
          iInf₂_le (Ymat g n) hfeas
      _ ≤ ENNReal.ofReal 4 := ENNReal.ofReal_le_ofReal hobj_bound
      _ = 4 := by simp
  obtain ⟨hmetric, htsp⟩ := simplicial_tsp_opt g n hg hg2 hgn hlt (s n)
  have htsp_enn : ENNReal.ofReal (MetricTSP.tspOpt D) = 4 * (z : ℝ≥0∞) := by
    rw [htsp, ENNReal.ofReal_natCast]
    push_cast [g]
    rfl
  have hratio : (z : ℝ≥0∞) ≤ ENNReal.ofReal (MetricTSP.tspOpt D) / sdp2Opt n D (r n) (s n) := by
    have h4_ne_zero : (4 : ℝ≥0∞) ≠ 0 := by norm_num
    have h4_ne_top : (4 : ℝ≥0∞) ≠ ⊤ := ENNReal.ofNat_ne_top
    calc (z : ℝ≥0∞)
      _ = (z : ℝ≥0∞) * (4 * (4 : ℝ≥0∞)⁻¹) := by
          rw [ENNReal.mul_inv_cancel h4_ne_zero h4_ne_top, mul_one]
      _ = (4 * (z : ℝ≥0∞)) * (4 : ℝ≥0∞)⁻¹ := by ring
      _ ≤ (4 * (z : ℝ≥0∞)) * (sdp2Opt n D (r n) (s n))⁻¹ :=
          mul_le_mul_of_nonneg_left (ENNReal.inv_le_inv.mpr hsdp) zero_le
      _ = ENNReal.ofReal (MetricTSP.tspOpt D) / sdp2Opt n D (r n) (s n) := by
          rw [htsp_enn, div_eq_mul_inv]
  refine hratio.trans ?_
  unfold integralityGapSDP2
  exact le_iSup₂_of_le n hn2 (le_iSup₂_of_le D hmetric le_rfl)
