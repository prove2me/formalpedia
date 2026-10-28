-- Prove2me | solution 1 for SalesTrust.Sharing.appC_info
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:26:18.623337+00:00
-- url     : https://prove2.me/submissions/08de8368-de7b-479d-ae8d-010f240a6592

import Mathlib
import Definitions.Def_SalesTrust_Sharing_Model

open SalesTrust.Sharing in
theorem solution (P : Params) (hS : P.Standing) (qH qL : ℝ) (hqL : qSL P < qL) (hlt : qL < qH) :
    punish P < piR P.VH qH - TeH P qH qL + cont P ⟨qH, TeH P qH qL, qL, TeL P qL⟩ ∧
      piR P.VL qH - TeH P qH qL + punish P <
        piR P.VL qL - TeL P qL + cont P ⟨qH, TeH P qH qL, qL, TeL P qL⟩ := by
  obtain ⟨hp0, hp1, hVLH, hpV, hδ0, hδ1⟩ := hS
  obtain ⟨k, hk⟩ : ∃ k, k = P.δ * P.p / (1 + P.δ * P.p) := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = P.δ / (1 - P.δ) := ⟨_, rfl⟩
  have hdp : 0 < 1 + P.δ * P.p := by nlinarith
  have hd1 : 0 < 1 - P.δ := by linarith
  have hk0 : 0 ≤ k := by rw [hk]; exact div_nonneg (mul_nonneg hδ0 hp0.le) hdp.le
  have hk1 : k < 1 := by rw [hk, div_lt_one hdp]; linarith
  have hkey : r * P.p - r * k * (1 + P.p) = k := by
    rw [hr, hk]; field_simp; ring
  have hq1 : (1 - P.p) ≠ 0 := (by linarith : (0:ℝ) < 1 - P.p).ne'
  have hqS : 0 < qSL P := by
    have e : qSL P = (P.VL - P.p * P.VH) / (2 * (1 - P.p)) := by
      unfold qSL; field_simp; ring
    rw [e]; apply div_pos <;> linarith
  have hD : 0 < P.VH - P.VL := by linarith
  have hTeH : TeH P qH qL = piR P.VH qH - gap P qL + 2 * k * (gap P qL - gap P (qSL P)) := by
    unfold TeH; rw [hk]; ring
  have hTeL : TeL P qL = piR P.VL qL + k * (gap P qL - gap P (qSL P)) := by
    unfold TeL; rw [hk]
  have hcont : ∀ m, cont P m = r * retailerProfit P m := fun m => by unfold cont; rw [hr]
  have hpun : punish P = r * (P.p * gap P (qSL P)) := by unfold punish staticRent; rw [hr]
  have hgap : ∀ q, gap P q = (P.VH - P.VL) * q := fun q => by unfold gap piR; ring
  rw [hpun, hcont]
  dsimp only [retailerProfit]
  rw [hTeH, hTeL, hgap, hgap]
  set A := (P.VH - P.VL) * (qL - qSL P) with hA
  have hApos : 0 < A := mul_pos hD (sub_pos.2 hqL)
  have hkA : (r * P.p - r * k * (1 + P.p)) * A = k * A := by rw [hkey]
  have h1 : 0 < (1 - k) * A := mul_pos (sub_pos.2 hk1) hApos
  have h2 : 0 < (P.VH - P.VL) * qSL P := mul_pos hD hqS
  have h3 : 0 ≤ k * A := mul_nonneg hk0 hApos.le
  have h4 : 0 < (P.VH - P.VL) * (qH - qL) := mul_pos hD (sub_pos.2 hlt)
  unfold piR
  constructor
  · nlinarith
  · nlinarith
