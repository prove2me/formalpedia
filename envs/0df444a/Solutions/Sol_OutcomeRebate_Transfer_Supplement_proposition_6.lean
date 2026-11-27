-- Prove2me | solution 1 for OutcomeRebate.Transfer.Supplement.proposition_6
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:05:10.965573+00:00
-- url     : https://prove2.me/submissions/442dcb84-4897-47a7-b68d-4f051461aa7c

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model
import Definitions.Def_OutcomeRebate_Transfer_Supplement_PartialRebate

open OutcomeRebate
open OutcomeRebate.Transfer
open OutcomeRebate.Transfer.Supplement

theorem solution (P : Params) (hS : P.Standing) (θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1) :
    let m := partialMargin P θ
    let zb := zBar P θ
    (∀ p : ℝ, P.vbar / (P.β * zb) ≤ p → payerObjP P θ 1 p = payerObjP P θ P.β p) ∧
    (∀ p : ℝ, 0 ≤ p → p < P.vbar / (P.β * zb) →
      (m ≤ P.β * P.q * zb / 2 → coversP P θ p) ∧
      (P.β * P.q * zb / 2 < m → m ≤ (1 + P.β) * P.q * zb / 2 →
        (p ≤ P.vbar / zb → coversP P θ p) ∧
        (P.vbar / zb < p → (coversP P θ p ↔ p ≤ P.q * (P.vp + P.vbar / 2) / (m - P.q * zb * P.β / 2)))) ∧
      ((1 + P.β) * P.q * zb / 2 < m →
        (p ≤ P.vbar / zb → (coversP P θ p ↔ p ≤ P.q * P.vp / (m - P.q * zb * (1 + P.β) / 2))) ∧
        (P.vbar / zb < p → (coversP P θ p ↔ p ≤ P.q * (P.vp + P.vbar / 2) / (m - P.q * zb * P.β / 2))))) := by
          intro m zb
          obtain ⟨hn, hvbar, hc, hβ, hβ2, hq, hq1, hα, hα1, hlam, hvp⟩ := hS
          obtain ⟨hθ0, hθ1⟩ := hθ
          set K : ℝ := P.lam * (1 - P.q) / P.q with hK
          have hKpos : 0 < K := by
            rw [hK]; apply div_pos _ hq; apply mul_pos (by linarith) (by linarith)
          set k : ℝ := K ^ (1 / P.α) with hk
          have hk0 : 0 ≤ k := Real.rpow_nonneg hKpos.le _
          have hkα : k ^ P.α = K := by
            rw [hk, ← Real.rpow_mul hKpos.le, one_div, inv_mul_cancel₀ hα.ne', Real.rpow_one]
          have hzb : zb = 1 + θ * k := by
            simp only [zb, zBar, Params.z, zOf]; rw [hk, hK]; ring
          have hzb1 : 1 ≤ zb := by rw [hzb]; nlinarith [mul_nonneg hθ0 hk0]
          have hm : m = P.q + θ * (1 - P.q) := by simp only [m, partialMargin]; ring
          -- welfare characterization
          have hwel : ∀ bb p v, 0 ≤ bb → 0 ≤ p →
              (0 ≤ welfareP P θ bb p v ↔ bb * p * zb ≤ v) := by
            intro bb p v hbb hp
            have hx : 0 ≤ θ * bb * p := by positivity
            have hu2 : u P.α P.lam (-(θ * bb * p)) = -(P.lam * (θ * bb * p) ^ P.α) := by
              unfold u
              split_ifs with h
              · have h0 : θ * bb * p = 0 := by linarith
                rw [h0]; simp [Real.zero_rpow hα.ne']
              · rw [neg_neg]
            have hbz : bb * p * zb = bb * p + k * (θ * bb * p) := by rw [hzb]; ring
            have hbp : 0 ≤ bb * p := mul_nonneg hbb hp
            unfold welfareP
            rw [hu2]
            by_cases hv : bb * p ≤ v
            · have hu1 : u P.α P.lam (v - bb * p) = (v - bb * p) ^ P.α := by
                unfold u; rw [if_pos (by linarith)]
              rw [hu1]
              have e1 : (k * (θ * bb * p)) ^ P.α = K * (θ * bb * p) ^ P.α := by
                rw [Real.mul_rpow hk0 hx, hkα]
              have e2 : (k * (θ * bb * p)) ^ P.α ≤ (v - bb * p) ^ P.α ↔ k * (θ * bb * p) ≤ v - bb * p :=
                Real.rpow_le_rpow_iff (mul_nonneg hk0 hx) (by linarith) hα
              have e3 : 0 ≤ P.q * (v - bb * p) ^ P.α + (1 - P.q) * -(P.lam * (θ * bb * p) ^ P.α) ↔
                  K * (θ * bb * p) ^ P.α ≤ (v - bb * p) ^ P.α := by
                rw [hK, div_mul_eq_mul_div, div_le_iff₀ hq]
                constructor <;> intro h <;> linarith
              rw [e3, ← e1, e2, hbz]
              constructor <;> intro h <;> linarith
            · push Not at hv
              have hu1 : u P.α P.lam (v - bb * p) = -(P.lam * (bb * p - v) ^ P.α) := by
                unfold u; rw [if_neg (by linarith)]; ring_nf
              rw [hu1]
              have hpos : 0 < (bb * p - v) ^ P.α := Real.rpow_pos_of_pos (by linarith) _
              have hpos2 : 0 ≤ (θ * bb * p) ^ P.α := Real.rpow_nonneg hx _
              have hkx : 0 ≤ k * (θ * bb * p) := mul_nonneg hk0 hx
              constructor
              · intro h
                exfalso
                have : 0 < P.q * (P.lam * (bb * p - v) ^ P.α) := by positivity
                have : 0 ≤ (1 - P.q) * (P.lam * (θ * bb * p) ^ P.α) := by
                  apply mul_nonneg (by linarith); positivity
                linarith
              · intro h; exfalso; linarith
          have hbuy : ∀ bb p, 0 ≤ bb → 0 ≤ p → buyersP P θ bb p = Set.Icc (bb * p * zb) P.vbar := by
            intro bb p hbb hp
            have : 0 ≤ bb * p * zb := by positivity
            ext v
            simp only [buyersP, Set.mem_ofPred_eq, Set.mem_Icc, hwel bb p v hbb hp]
            constructor
            · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
            · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, h2⟩, h1⟩
          have hW : ∀ bb p, 0 ≤ bb → 0 ≤ p → bb * p * zb ≤ P.vbar →
              payerObjP P θ bb p = P.n / P.vbar * ((P.vbar - bb * p * zb) *
                (P.q * P.vp - p * m + P.q * (P.vbar + bb * p * zb) / 2)) := by
            intro bb p hbb hp hle
            unfold payerObjP payerPayoffP patientPayoffP demandP
            rw [hbuy bb p hbb hp, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith),
              MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
            have hint : ∫ v in (bb * p * zb)..P.vbar, (P.q * (v - bb * p) - (1 - P.q) * θ * bb * p) =
                P.q * ((P.vbar ^ 2 - (bb * p * zb) ^ 2) / 2) -
                  (P.vbar - bb * p * zb) * (P.q * bb * p + (1 - P.q) * θ * bb * p) := by
              have e : (fun v => P.q * (v - bb * p) - (1 - P.q) * θ * bb * p) =
                  fun v => P.q * v - (P.q * bb * p + (1 - P.q) * θ * bb * p) := by
                funext v; ring
              rw [e, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul, integral_id,
                intervalIntegral.integral_const]
              · simp
              · exact (continuous_const.mul continuous_id).intervalIntegrable _ _
              · exact intervalIntegrable_const
            rw [hint, hm]
            ring
          have hW0 : ∀ bb p, 0 ≤ bb → 0 ≤ p → P.vbar ≤ bb * p * zb → payerObjP P θ bb p = 0 := by
            intro bb p hbb hp hle
            have hvol : MeasureTheory.volume (buyersP P θ bb p) = 0 := by
              rw [hbuy bb p hbb hp, Real.volume_Icc, ENNReal.ofReal_eq_zero]; linarith
            unfold payerObjP payerPayoffP patientPayoffP demandP
            rw [MeasureTheory.setIntegral_measure_zero _ hvol, hvol]
            simp
          have hzb0 : 0 < zb := by linarith
          have hβ1 : P.β < 1 := by linarith
          have hc0 : 0 < P.n / P.vbar := div_pos hn hvbar
          refine ⟨?_, ?_⟩
          · intro p hp
            rw [div_le_iff₀ (mul_pos hβ hzb0)] at hp
            have hp0 : 0 < p := by
              by_contra h; push Not at h
              have : p * (P.β * zb) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (by positivity)
              linarith
            rw [hW0 1 p (by norm_num) hp0.le (by nlinarith), hW0 P.β p hβ.le hp0.le (by nlinarith)]
          · intro p hp0 hplt
            rw [lt_div_iff₀ (mul_pos hβ hzb0)] at hplt
            have hcovA : p ≤ P.vbar / zb → (coversP P θ p ↔
                0 ≤ p * (P.q * P.vp - p * m + P.q * p * zb * (1 + P.β) / 2)) := by
              intro hle
              rw [le_div_iff₀ hzb0] at hle
              unfold coversP
              rw [hW 1 p (by norm_num) hp0 (by linarith), hW P.β p hβ.le hp0 (by nlinarith)]
              have hid : P.n / P.vbar * ((P.vbar - P.β * p * zb) *
                  (P.q * P.vp - p * m + P.q * (P.vbar + P.β * p * zb) / 2)) -
                  P.n / P.vbar * ((P.vbar - 1 * p * zb) *
                  (P.q * P.vp - p * m + P.q * (P.vbar + 1 * p * zb) / 2)) =
                  P.n / P.vbar * (((1 - P.β) * zb) *
                    (p * (P.q * P.vp - p * m + P.q * p * zb * (1 + P.β) / 2))) := by ring
              have hpos : 0 < P.n / P.vbar * ((1 - P.β) * zb) :=
                mul_pos hc0 (mul_pos (by linarith) hzb0)
              constructor
              · intro h
                have h2 : 0 ≤ P.n / P.vbar * ((1 - P.β) * zb) *
                    (p * (P.q * P.vp - p * m + P.q * p * zb * (1 + P.β) / 2)) := by
                  rw [mul_assoc]; linarith
                exact (mul_nonneg_iff_of_pos_left hpos).mp h2
              · intro h
                have h2 := mul_nonneg hpos.le h
                rw [mul_assoc] at h2
                linarith
            have hcovB : P.vbar / zb < p → (coversP P θ p ↔
                p * (m - P.q * zb * P.β / 2) ≤ P.q * (P.vp + P.vbar / 2)) := by
              intro hlt
              rw [div_lt_iff₀ hzb0] at hlt
              unfold coversP
              rw [hW0 1 p (by norm_num) hp0 (by linarith), hW P.β p hβ.le hp0 (by nlinarith)]
              have hpos : 0 < P.n / P.vbar * (P.vbar - P.β * p * zb) := mul_pos hc0 (by linarith)
              rw [← mul_assoc]
              constructor
              · intro h
                have := (mul_nonneg_iff_of_pos_left hpos).mp h
                linarith
              · intro h
                exact mul_nonneg hpos.le (by linarith)
            have heasy : m ≤ (1 + P.β) * P.q * zb / 2 → p ≤ P.vbar / zb → coversP P θ p := by
              intro hm1 hle
              rw [hcovA hle]
              have : 0 ≤ p * ((1 + P.β) * P.q * zb / 2 - m) := mul_nonneg hp0 (by linarith)
              have : 0 ≤ P.q * P.vp := mul_nonneg hq.le hvp
              apply mul_nonneg hp0
              nlinarith
            have hhard : 0 < m - P.q * zb * P.β / 2 → P.vbar / zb < p → (coversP P θ p ↔
                p ≤ P.q * (P.vp + P.vbar / 2) / (m - P.q * zb * P.β / 2)) := by
              intro hD hlt
              rw [hcovB hlt, le_div_iff₀ hD]
            refine ⟨?_, ?_, ?_⟩
            · intro hm1
              by_cases hle : p ≤ P.vbar / zb
              · exact heasy (by nlinarith) hle
              · push Not at hle
                rw [hcovB hle]
                have : p * (m - P.q * zb * P.β / 2) ≤ 0 :=
                  mul_nonpos_of_nonneg_of_nonpos hp0 (by linarith)
                have : 0 ≤ P.q * (P.vp + P.vbar / 2) := mul_nonneg hq.le (by linarith)
                linarith
            · intro hm1 hm2
              exact ⟨heasy hm2, hhard (by linarith)⟩
            · intro hm1
              refine ⟨?_, hhard (by nlinarith)⟩
              intro hle
              have hD : 0 < m - P.q * zb * (1 + P.β) / 2 := by linarith
              rw [hcovA hle, le_div_iff₀ hD]
              have hX : P.q * P.vp - p * m + P.q * p * zb * (1 + P.β) / 2 =
                  P.q * P.vp - p * (m - P.q * zb * (1 + P.β) / 2) := by ring
              rw [hX]
              constructor
              · intro h
                rcases hp0.eq_or_lt with h0 | h0
                · rw [← h0]; simp; exact mul_nonneg hq.le hvp
                · have := (mul_nonneg_iff_of_pos_left h0).mp h
                  linarith
              · intro h
                exact mul_nonneg hp0 (by linarith)
