-- Prove2me | solution 1 for ProxBundle.GPB.Supplement.theorem_5_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:36:25.225715+00:00
-- url     : https://prove2.me/submissions/8eb2e8e2-821d-43ac-9cae-0073f2211ce1

import Mathlib
import Definitions.Def_ProxBundle_GPB_Model
import Definitions.Def_ProxBundle_GPB_Supplement_Rates
import Definitions.Def_ProxBundle_GPB_Supplement_Adaptive

open ProxBundle
open ProxBundle.GPB
open ProxBundle.GPB.Supplement

/-- Theorem 5.3 (corrected integer/small-log convention): arbitrary stepsizes,
then the full (39)/(16) consequence. Every beta >= 1 and T²=0 are allowed. -/
theorem solution (C : ℝ) (hC : 0 < C)
    {n : ℕ} (P : Instance n) (μ Mf Lf Mbar Lbar lam ε β : ℝ)
    (x0 x0s : E n) (A : APBRun n)
    (hμ : 0 ≤ μ) (hMf : 0 ≤ Mf) (hLf : 0 ≤ Lf)
    (hA1 : P.A1 μ) (hA3 : P.A3 Mf Lf)
    (hmin : P.IsMinPair ε Mbar Lbar)
    (hx0s : P.IsNearestOpt x0 x0s) (hx0 : x0 ∈ P.D)
    (hlam : 0 < lam) (hε : 0 < ε) (hβ : 1 ≤ β)
    (hrun : IsAPBRun P lam ε β x0 A) :
    Obtains P A.accepted x0s ε (adaptiveBound μ lam ε Mbar Lbar ‖x0 - x0s‖) ∧
    (StepInterval C ε (Mbar ^ 2 + ε * Lbar) lam (‖x0 - x0s‖ ^ 2) →
      Obtains P A.accepted x0s ε
        (K53 C * (logFactor (tbar Mbar Lbar lam ‖x0 - x0s‖) ε + 1) *
          (rate μ ε (Mbar ^ 2 + ε * Lbar) (‖x0 - x0s‖ ^ 2) + 1))) := by
            obtain ⟨hM, hL, hA, -⟩ := hmin
            obtain ⟨-, -, ⟨hSC, -⟩, hsub⟩ := hA1
            obtain ⟨⟨hsD, hsmin⟩, -⟩ := hx0s
            clear hA3 hMf hLf
            have hθ : 1 ≤ 1 + lam * μ := by linarith only [mul_nonneg hlam.le hμ]
            have hθ0 : 0 < 1 + lam * μ := lt_of_lt_of_le one_pos hθ
            obtain ⟨w, hwdef⟩ : ∃ w, w = lam / (1 + lam * μ) := ⟨_, rfl⟩
            have hwset : lamMu μ lam = w := hwdef.symm
            have hw : 0 < w := by rw [hwdef]; exact div_pos hlam hθ0
            have hwle : w ≤ lam := by
              rw [hwdef]; exact div_le_self hlam.le hθ
            have hwinv : 1 / w = μ + 1 / lam := by
              rw [hwdef, one_div_div, add_div, mul_div_cancel_left₀ _ hlam.ne', add_comm]
            obtain ⟨S, hSset⟩ : ∃ S, S = Mbar ^ 2 + ε * Lbar := ⟨_, rfl⟩
            have hS : 0 ≤ S := by rw [hSset]; positivity
            obtain ⟨B, hBset⟩ : ∃ B, B = 8 * w * S / ε := ⟨_, rfl⟩
            have hB : 0 ≤ B := by rw [hBset]; positivity
            have hB1 : 0 < 2 * (1 + B) := by linarith only [hB]
            have hpos : 0 < 1 / (2 * (1 + B)) := one_div_pos.2 hB1
            have hle1 : 1 / (2 * (1 + B)) ≤ 1 := by
              rw [div_le_one hB1]; linarith only [hB]
            -- pure real lemmas
            have hlim : ∀ l r q : ℝ, 0 ≤ q → (∀ t : ℝ, 0 < t → t < 1 → l ≤ r + t * q) → l ≤ r := by
              intro l r q hq h
              apply le_of_forall_pos_le_add
              intro δ hδ
              have hQ : 0 < q + δ + 1 := by linarith only [hq, hδ]
              have hd1 : δ / (q + δ + 1) < 1 := by rw [div_lt_one hQ]; linarith only [hq]
              have h4 : δ / (q + δ + 1) * q ≤ δ := by
                rw [div_mul_eq_mul_div, div_le_iff₀ hQ]
                exact mul_le_mul_of_nonneg_left (by linarith only [hδ]) hδ.le
              linarith only [h _ (div_pos hδ hQ) hd1, h4]
            have hRτ : ∀ τ s : ℝ, τ ≤ 1 → (1 - τ) * B ≤ τ →
                (1 - τ) * (2 * Mbar * s + Lbar * s ^ 2) - τ * (s ^ 2 / (2 * w)) ≤ (1 - τ) * ε / 4 := by
              intro τ s h1 hBU
              have e1 : (1 - τ) * B * (s ^ 2 / (2 * w)) ≤ τ * (s ^ 2 / (2 * w)) :=
                mul_le_mul_of_nonneg_right hBU (by positivity)
              have e2 : B * (s ^ 2 / (2 * w)) = 4 * S * s ^ 2 / ε := by
                rw [hBset]; field_simp; ring
              have e3 : 2 * Mbar * s + Lbar * s ^ 2 - 4 * S * s ^ 2 / ε ≤ ε / 4 := by
                rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hε, hSset]
                linarith only [sq_nonneg (2 * Mbar * s - ε / 2), mul_nonneg (mul_nonneg hε.le hL) (sq_nonneg s)]
              have e4 := mul_le_mul_of_nonneg_left e3 (sub_nonneg.2 h1)
              rw [mul_assoc, e2] at e1
              linarith only [e1, e4]
            have hR1 : ∀ τ y y' g g' f h l nx nx' q D : ℝ, 0 ≤ τ → τ ≤ 1 → g' + nx' + q ≤ g + nx →
                f - l ≤ D → y ≤ y' → y ≤ f + h → 0 ≤ nx → (1 - τ) * D - τ * q ≤ (1 - τ) * ε / 4 →
                y - (τ * g + (1 - τ) * (l + h) + nx) ≤ τ * (y' - (g' + nx')) + (1 - τ) * ε / 4 := by
              intro τ y y' g g' f h l nx nx' q D h0 h1 k1 k2 k3 k8 hnx k4
              have h1' := sub_nonneg.2 h1
              have l5 := mul_le_mul_of_nonneg_left k1 h0
              have l6 := mul_le_mul_of_nonneg_left k2 h1'
              have l7 := mul_le_mul_of_nonneg_left k3 h0
              have l8 := mul_le_mul_of_nonneg_left k8 h1'
              have l9 := mul_nonneg h1' hnx
              linarith only [l5, l6, l7, l8, l9, k4]
            have hRs : ∀ s e d D0 : ℝ, 0 ≤ d → d ≤ D0 →
                s ^ 2 + e ^ 2 ≤ d ^ 2 + 2 * lam * ((2 * Mbar + Lbar * d) * e) →
                s ≤ 2 * (max 1 (2 * lam * Lbar) * D0 + lam * Mbar) := by
              intro s e d D0 hd0 hda k4
              have hk : 0 ≤ lam * (2 * Mbar + Lbar * d) := by positivity
              have k5 : s ≤ d + lam * (2 * Mbar + Lbar * d) := by
                apply le_of_sq_le_sq _ (add_nonneg hd0 hk)
                linarith only [sq_nonneg (e - lam * (2 * Mbar + Lbar * d)), mul_nonneg hd0 hk, k4]
              have hX1 : 1 ≤ max 1 (2 * lam * Lbar) := le_max_left _ _
              have hX2 : 2 * lam * Lbar ≤ max 1 (2 * lam * Lbar) := le_max_right _ _
              have h1 : (1 + lam * Lbar) * d ≤ 2 * max 1 (2 * lam * Lbar) * D0 :=
                mul_le_mul (by linarith only [hX1, hX2]) hda hd0 (by linarith only [hX1])
              linarith only [k5, h1]
            have hRt : ∀ s Y : ℝ, 0 ≤ s → s ≤ 2 * Y →
                2 * Mbar * s + Lbar * s ^ 2 ≤ Mbar ^ 2 + 4 * (Lbar + 2) * Y ^ 2 := by
              intro s Y hs0 k6
              have k7 := pow_le_pow_left₀ hs0 k6 2
              have k8 := mul_le_mul_of_nonneg_left k7 (by linarith only [hL] : 0 ≤ Lbar + 2)
              linarith only [k8, sq_nonneg (Mbar - s), sq_nonneg s]
            have hRk : ∀ s e d r : ℝ, s ^ 2 / (2 * lam) + e ^ 2 / (2 * w) ≤ d ^ 2 / (2 * lam) + r →
                s ^ 2 + e ^ 2 ≤ d ^ 2 + 2 * lam * r := by
              intro s e d r h
              have h1 : e ^ 2 / (2 * lam) ≤ e ^ 2 / (2 * w) :=
                div_le_div_of_nonneg_left (sq_nonneg e) (by linarith only [hw]) (by linarith only [hwle])
              have h2 : s ^ 2 / (2 * lam) + e ^ 2 / (2 * lam) ≤ d ^ 2 / (2 * lam) + r := by
                linarith only [h, h1]
              rw [← add_div, div_add' _ _ _ (by positivity), div_le_div_iff_of_pos_right (by positivity)] at h2
              linarith only [h2]
            have hRser : ∀ F y y' G e d : ℝ, F - (G + y') ≤ ε / 2 →
                G + y' + e / (2 * w) ≤ y + d / (2 * lam) → ε < F - y →
                (1 + lam * μ) * e + lam * ε ≤ d := by
              intro F y y' G e d h1 h2 h3
              have h4 : e / (2 * w) + ε / 2 ≤ d / (2 * lam) := by linarith only [h1, h2, h3]
              have e1 : e / (2 * w) = (1 + lam * μ) * e / (2 * lam) := by
                rw [hwdef]; field_simp
              have e2 : ε / 2 = lam * ε / (2 * lam) := by field_simp
              rw [e1, e2, ← add_div, div_le_div_iff_of_pos_right (by positivity)] at h4
              exact h4
            have hRlog : ∀ (N : ℕ) (T LF x : ℝ), 0 ≤ T → 0 ≤ LF → 2 * (1 + B) * LF ≤ N →
                (0 < T → Real.log (4 * T / ε) ≤ LF) → ε / 2 < x →
                x - ε / 4 ≤ (1 - 1 / (2 * (1 + B))) ^ N * (T - ε / 4) → False := by
              intro N T LF x hT0 hLF0 hN hlog h2 h3
              have hr0 : 0 ≤ 1 - 1 / (2 * (1 + B)) := sub_nonneg.2 hle1
              have hrN : 0 ≤ (1 - 1 / (2 * (1 + B))) ^ N := pow_nonneg hr0 N
              have h4 : ε / 4 < (1 - 1 / (2 * (1 + B))) ^ N * T := by
                linarith only [h2, h3, mul_nonneg hrN hε.le]
              have hTpos : 0 < T := by
                rcases hT0.lt_or_eq with h | h
                · exact h
                · rw [← h, mul_zero] at h4; linarith only [h4, hε]
              have h5 : (1 - 1 / (2 * (1 + B))) ^ N ≤ Real.exp (-LF) := by
                have h6 : 1 - 1 / (2 * (1 + B)) ≤ Real.exp (-(1 / (2 * (1 + B)))) := by
                  linarith only [Real.add_one_le_exp (-(1 / (2 * (1 + B))))]
                refine (pow_le_pow_left₀ hr0 h6 N).trans ?_
                rw [← Real.exp_nat_mul, Real.exp_le_exp]
                have : LF ≤ N * (1 / (2 * (1 + B))) := by
                  rw [mul_one_div, le_div_iff₀ hB1]
                  linarith only [hN]
                linarith only [this]
              have h8 : 4 * T / ε ≤ Real.exp LF := by
                rw [← Real.log_le_iff_le_exp (by positivity)]; exact hlog hTpos
              rw [div_le_iff₀ hε] at h8
              have h9 : (1 - 1 / (2 * (1 + B))) ^ N * T ≤ Real.exp (-LF) * (ε / 4 * Real.exp LF) :=
                mul_le_mul h5 (by linarith only [h8]) hTpos.le (Real.exp_pos _).le
              have h10 : Real.exp (-LF) * (ε / 4 * Real.exp LF) = ε / 4 := by
                rw [mul_left_comm, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
              linarith only [h4, h9, h10]
            have hRK : ∀ (K : ℕ) (r D : ℝ), 0 ≤ D → 0 ≤ r → K * (lam * ε) + D ≤ r →
                (1 + lam * μ) ^ K * (μ * D + ε) ≤ μ * r + ε → (K : ℝ) ≤ serBound μ lam ε r := by
              intro K r D hD hr h1 h2
              have c1 : (K : ℝ) ≤ r / (lam * ε) := by
                rw [le_div_iff₀ (mul_pos hlam hε)]
                linarith only [h1, hD]
              unfold serBound
              split_ifs with h
              · exact c1
              · have hμ' : 0 < μ := lt_of_le_of_ne hμ (Ne.symm h)
                refine le_min c1 ?_
                have c2 : (1 + lam * μ) ^ K ≤ μ * r / ε + 1 := by
                  rw [div_add_one hε.ne', le_div_iff₀ hε]
                  refine le_trans ?_ h2
                  exact mul_le_mul_of_nonneg_left (by linarith only [mul_nonneg hμ hD]) (pow_nonneg hθ0.le K)
                have c3 := Real.log_le_log (pow_pos hθ0 K) c2
                rw [Real.log_pow] at c3
                have c4 := Real.one_sub_inv_le_log_of_pos hθ0
                have c5 : 1 - (1 + lam * μ)⁻¹ = μ * w := by
                  rw [hwdef]; field_simp; ring
                rw [c5] at c4
                rw [hwset, one_div, inv_mul_eq_div, le_div_iff₀ (mul_pos hμ' hw)]
                exact le_trans (mul_le_mul_of_nonneg_left c4 (Nat.cast_nonneg K)) c3
            have hRtr : ∀ t : ℝ, 1 / (2 * (1 + B)) ≤ 1 - t → t < (1 - t) * B →
                1 / (2 * (1 + B)) ≤ 1 - (1 + t) / 2 := by
              intro t _ hb
              rw [div_le_iff₀ hB1]
              linarith only [hb]
            have hserB0 : ∀ r : ℝ, 0 ≤ r → 0 ≤ serBound μ lam ε r := by
              intro r hr
              unfold serBound
              split_ifs with h
              · positivity
              · refine le_min (by positivity) ?_
                rw [hwset]
                refine mul_nonneg (by positivity) (Real.log_nonneg ?_)
                have : 0 ≤ μ * r / ε := by positivity
                linarith only [this]
            -- final rate comparison
            have hrate : ∀ (N : ℕ) (LF r : ℝ), 0 ≤ LF → 0 ≤ r → (N : ℝ) < 2 * (1 + B) * LF + 1 →
                StepInterval C ε S lam r →
                ((N : ℝ) + 1) * (serBound μ lam ε r + 1) ≤
                  K53 C * (LF + 1) * (rate μ ε S r + 1) := by
              intro N LF r hLF0 hr0 hNlt hSI
              obtain ⟨hSpos, hI1, hI2⟩ := hSI
              have hser0 := hserB0 r hr0
              clear hRτ hR1 hRs hRt hRk hRser hRlog hRK hRtr hserB0 hlim hsub hSC hsD hsmin hA hrun
              obtain ⟨c, hc⟩ : ∃ c, c = max C 1 := ⟨_, rfl⟩
              have hc1 : 1 ≤ c := by rw [hc]; exact le_max_right _ _
              have hcC : C ≤ c := by rw [hc]; exact le_max_left _ _
              have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
              have hJ1 : ε ≤ lam * (c * S) := by
                rw [div_le_iff₀ (mul_pos hC hSpos)] at hI1
                have := mul_le_mul_of_nonneg_right hcC (mul_pos hlam hSpos).le
                linarith only [hI1, this]
              have hJ2 : lam * ε ≤ c * r := by
                rw [le_div_iff₀ hε] at hI2
                have := mul_le_mul_of_nonneg_right hcC hr0
                linarith only [hI2, this]
              obtain ⟨a, ha⟩ : ∃ a, a = w * S / ε := ⟨_, rfl⟩
              have ha0 : 0 ≤ a := by rw [ha]; positivity
              have hBa : B = 8 * a := by rw [hBset, ha]; ring
              have hN1 : (N : ℝ) + 1 ≤ 2 * (1 + 8 * a) * (LF + 1) := by
                rw [hBa] at hNlt
                linarith only [hNlt, ha0]
              obtain ⟨ser, hser⟩ : ∃ ser, ser = serBound μ lam ε r := ⟨_, rfl⟩
              rw [← hser] at hser0 ⊢
              have hfin : ∀ X : ℝ, 0 ≤ X → ser ≤ c * X → a ≤ c * X → a * ser ≤ X →
                  2 * (1 + 8 * a) * (ser + 1) ≤ K53 C * (X + 1) := by
                intro X hX h1 h2 h3
                unfold K53
                rw [← hc]
                linarith only [mul_nonneg hX hc0.le, h1, h2, h3, hc1, hX]
              have hRfin : 2 * (1 + 8 * a) * (ser + 1) ≤ K53 C * (rate μ ε S r + 1) := by
                have hser1 : ser ≤ r / (lam * ε) := by
                  rw [hser]; unfold serBound
                  split_ifs
                  · exact le_rfl
                  · exact min_le_left _ _
                have ha1 : a ≤ lam * S / ε := by
                  rw [ha]; gcongr
                have hR : 2 * (1 + 8 * a) * (ser + 1) ≤ K53 C * (S * r / ε ^ 2 + 1) := by
                  apply hfin
                  · positivity
                  · refine hser1.trans ?_
                    rw [div_le_iff₀ (mul_pos hlam hε)]
                    have : c * (S * r / ε ^ 2) * (lam * ε) = r * (lam * (c * S)) / ε := by field_simp
                    rw [this, le_div_iff₀ hε]
                    exact mul_le_mul_of_nonneg_left hJ1 hr0
                  · refine ha1.trans ?_
                    rw [div_le_iff₀ hε]
                    have : c * (S * r / ε ^ 2) * ε = S * (c * r) / ε := by field_simp
                    rw [this, le_div_iff₀ hε]
                    have := mul_le_mul_of_nonneg_left hJ2 hS
                    linarith only [this]
                  · refine (mul_le_mul ha1 hser1 hser0 (by positivity)).trans (le_of_eq ?_)
                    field_simp
                unfold rate
                split_ifs with h
                · exact hR
                · have hμ' : 0 < μ := lt_of_le_of_ne hμ (Ne.symm h)
                  rcases min_choice (S * r / ε ^ 2) ((S / (μ * ε) + 1) * Real.log (1 + μ * r / ε)) with hm | hm
                  · rw [hm]; exact hR
                  · rw [hm]
                    obtain ⟨l, hl⟩ : ∃ l, l = Real.log (1 + μ * r / ε) := ⟨_, rfl⟩
                    have hz0 : 0 ≤ μ * r / ε := by positivity
                    have hl0 : 0 ≤ l := by rw [hl]; exact Real.log_nonneg (by linarith only [hz0])
                    have hser2 : ser ≤ 1 / (μ * w) * l := by
                      rw [hser]; unfold serBound
                      rw [if_neg h, hl, add_comm (1:ℝ) (μ * r / ε), hwset]
                      exact min_le_right _ _
                    have hgl := Real.one_sub_inv_le_log_of_pos (by linarith only [hz0] : 0 < 1 + μ * r / ε)
                    rw [← hl] at hgl ⊢
                    have hSμ : 0 ≤ S / (μ * ε) := by positivity
                    have hcl : 0 ≤ c * l := mul_nonneg hc0.le hl0
                    apply hfin
                    · positivity
                    · refine hser2.trans ?_
                      rw [← mul_assoc]
                      refine mul_le_mul_of_nonneg_right ?_ hl0
                      have e1 : 1 / (μ * w) = 1 / (μ * lam) + 1 := by
                        rw [hwdef]; field_simp
                      have e2 : 1 / (μ * lam) ≤ c * (S / (μ * ε)) := by
                        rw [div_le_iff₀ (mul_pos hμ' hlam)]
                        have : c * (S / (μ * ε)) * (μ * lam) = lam * (c * S) / ε := by field_simp
                        rw [this, le_div_iff₀ hε]; linarith only [hJ1]
                      rw [e1]; linarith only [e2, hc1]
                    · have e1 : a = S / (μ * ε) * (lam * μ / (1 + lam * μ)) := by
                        rw [ha, hwdef]; field_simp
                      have e2 : lam * μ / (1 + lam * μ) ≤ c * l := by
                        have hden : 0 < ε + μ * r := by positivity
                        have e3 : 1 - (1 + μ * r / ε)⁻¹ = μ * r / (ε + μ * r) := by
                          field_simp; ring
                        have e4 : lam * μ / (1 + lam * μ) ≤ c * (μ * r / (ε + μ * r)) := by
                          rw [← mul_div_assoc, div_le_div_iff₀ hθ0 hden]
                          have q1 := mul_le_mul_of_nonneg_left hJ2 hμ
                          have q2 : 0 ≤ (c - 1) * (lam * μ * (μ * r)) :=
                            mul_nonneg (sub_nonneg.2 hc1) (by positivity)
                          linarith only [q1, q2]
                        rw [e3] at hgl
                        exact e4.trans (mul_le_mul_of_nonneg_left hgl hc0.le)
                      rw [e1]
                      have e5 := mul_le_mul_of_nonneg_left e2 hSμ
                      linarith only [e5, hcl]
                    · have e1 := mul_le_mul_of_nonneg_left hser2 ha0
                      have e2 : a * (1 / (μ * w) * l) = S / (μ * ε) * l := by
                        rw [ha]; field_simp
                      linarith only [e1, e2, hl0]
              calc ((N : ℝ) + 1) * (ser + 1) ≤ 2 * (1 + 8 * a) * (LF + 1) * (ser + 1) :=
                    mul_le_mul_of_nonneg_right hN1 (by linarith only [hser0])
                _ = (LF + 1) * (2 * (1 + 8 * a) * (ser + 1)) := by ring
                _ ≤ (LF + 1) * (K53 C * (rate μ ε S r + 1)) :=
                    mul_le_mul_of_nonneg_left hRfin (by linarith only [hLF0])
                _ = K53 C * (LF + 1) * (rate μ ε S r + 1) := by ring
            obtain ⟨hx00, hy00, hτ0, hstep⟩ := hrun
            -- convex combination identity
            have hcomb0 : ∀ (a b : ℝ) (p q : E n), a + b = 1 →
                ‖a • p + b • q‖ ^ 2 = a * ‖p‖ ^ 2 + b * ‖q‖ ^ 2 - a * b * ‖p - q‖ ^ 2 := by
              intro a b p q hab
              rw [norm_add_sq_real, norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left,
                real_inner_smul_right, mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
              obtain rfl : b = 1 - a := by linarith only [hab]
              ring
            have haff : ∀ (a b : ℝ) (u v c : E n), a + b = 1 →
                a • u + b • v - c = a • (u - c) + b • (v - c) := by
              intro a b u v c hab
              rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hab, one_smul]
            have hcomb : ∀ (a b : ℝ) (u v c : E n), a + b = 1 →
                ‖a • u + b • v - c‖ ^ 2 = a * ‖u - c‖ ^ 2 + b * ‖v - c‖ ^ 2 - a * b * ‖u - v‖ ^ 2 := by
              intro a b u v c hab
              rw [haff a b u v c hab, hcomb0 a b _ _ hab, sub_sub_sub_cancel_right]
            -- strongly convex prox inequality
            have hκ : ∀ r : ℝ, r / (2 * w) = (μ / 2 * r + r / (2 * lam)) := by
              intro r
              have : r / (2 * w) = r / 2 * (1 / w) := by rw [mul_one_div, div_div]
              rw [this, hwinv, mul_add, mul_one_div, div_div]; ring
            have hRprox : ∀ t gu gx gz nu nx e : ℝ, 0 < t →
                gz ≤ t * gu + (1 - t) * gx - t * (1 - t) * (μ / 2 * e) →
                gx + nx / (2 * lam) ≤ gz + (t * nu + (1 - t) * nx - t * (1 - t) * e) / (2 * lam) →
                gx + nx / (2 * lam) + e / (2 * w) ≤ gu + nu / (2 * lam) + t * (e / (2 * w)) := by
              intro t gu gx gz nu nx e ht h1 h2
              rw [hκ]
              have h3 : (t * nu + (1 - t) * nx - t * (1 - t) * e) / (2 * lam)
                    = t * (nu / (2 * lam)) + (1 - t) * (nx / (2 * lam))
                      - t * (1 - t) * (e / (2 * lam)) := by ring
              rw [h3] at h2
              have h4 : t * (gx + nx / (2 * lam) + (μ / 2 * e + e / (2 * lam))) ≤
                  t * (gu + nu / (2 * lam) + t * (μ / 2 * e + e / (2 * lam))) := by
                linarith only [h1, h2]
              exact le_of_mul_le_mul_left h4 ht
            have hprox : ∀ (G : E n → ℝ) (c x : E n), StrongConvexOn P.D μ G → P.IsProxMin G c lam x →
                ∀ u ∈ P.D, G x + ‖x - c‖ ^ 2 / (2 * lam) + ‖u - x‖ ^ 2 / (2 * w) ≤
                  G u + ‖u - c‖ ^ 2 / (2 * lam) := by
              intro G c x hG hx u hu
              obtain ⟨hxD, hxm⟩ := hx
              refine hlim _ _ (‖u - x‖ ^ 2 / (2 * w)) (div_nonneg (sq_nonneg _) (by linarith only [hw])) ?_
              intro t ht ht1
              have hab : t + (1 - t) = 1 := add_sub_cancel _ _
              have h1 := hG.2 hu hxD ht.le (sub_nonneg.2 ht1.le) hab
              have h2 := hxm _ (hG.1 hu hxD ht.le (sub_nonneg.2 ht1.le) hab)
              rw [hcomb t (1 - t) u x c hab] at h2
              exact hRprox t _ _ _ _ _ _ ht h1 h2
            -- linearization error
            have hlin : ∀ u ∈ P.D, ∀ x ∈ P.D,
                P.f u - P.ellf u x ≤ 2 * Mbar * ‖u - x‖ + Lbar * ‖u - x‖ ^ 2 := by
              intro u hu x hx
              have h1 := hsub u hu x hx
              have h2 := real_inner_le_norm (P.f' u - P.f' x) (u - x)
              have h4 := mul_le_mul_of_nonneg_right (hA u hu x hx) (norm_nonneg (u - x))
              unfold Instance.ellf at h1 ⊢
              rw [← neg_sub u x, inner_neg_right] at h1
              rw [inner_sub_left] at h2
              linarith only [h1, h2, h4]
            have hell : ∀ (a b : ℝ) (u v x : E n), a + b = 1 →
                P.ellf (a • u + b • v) x = a * P.ellf u x + b * P.ellf v x := by
              intro a b u v x hab
              unfold Instance.ellf
              rw [haff a b u v x hab, inner_add_right, real_inner_smul_right, real_inner_smul_right]
              obtain rfl : b = 1 - a := by linarith only [hab]
              ring
            have hcutSC : ∀ (x : E n) (G : E n → ℝ), (∀ u ∈ P.D, G u = P.ellf u x + P.h u) →
                StrongConvexOn P.D μ G := by
              intro x G hG
              refine ⟨hSC.1, ?_⟩
              intro u hu v hv a b ha hb hab
              have h1 := hSC.2 hu hv ha hb hab
              simp only [smul_eq_mul] at h1 ⊢
              rw [hG _ (hSC.1 hu hv ha hb hab), hG _ hu, hG _ hv, hell a b u v x hab]
              linarith only [h1]
            have hcombSC : ∀ (τ : ℝ) (G1 G2 G : E n → ℝ), 0 ≤ τ → τ ≤ 1 →
                StrongConvexOn P.D μ G1 → StrongConvexOn P.D μ G2 →
                (∀ u ∈ P.D, G u = τ * G1 u + (1 - τ) * G2 u) → StrongConvexOn P.D μ G := by
              intro τ G1 G2 G hτ hτ1 h1 h2 hG
              refine ⟨hSC.1, ?_⟩
              intro u hu v hv a b ha hb hab
              have h3 := mul_le_mul_of_nonneg_left (h1.2 hu hv ha hb hab) hτ
              have h4 := mul_le_mul_of_nonneg_left (h2.2 hu hv ha hb hab) (sub_nonneg.2 hτ1)
              simp only [smul_eq_mul] at h3 h4 ⊢
              rw [hG _ (hSC.1 hu hv ha hb hab), hG _ hu, hG _ hv]
              linarith only [h3, h4]
            have hcutle : ∀ x ∈ P.D, ∀ u ∈ P.D, P.ellf u x + P.h u ≤ P.φ u := by
              intro x hx u hu
              exact add_le_add_left (hsub x hx u hu) (P.h u)
            -- t unfolded at successors
            have htS : ∀ p : ℕ, A.accepted.t P lam (p + 1) =
                P.φ (A.accepted.y (p + 1)) - (A.accepted.Γ (p + 1) (A.accepted.x (p + 1)) +
                  ‖A.accepted.x (p + 1) - A.accepted.xc (p + 1)‖ ^ 2 / (2 * lam)) :=
              fun p => if_neg (Nat.succ_ne_zero p)
            have ht0 : A.accepted.t P lam 0 = 0 := if_pos rfl
            have hp0 : ∀ p : ℕ, ε / 2 < A.accepted.t P lam p → 1 ≤ p := by
              intro p h
              rcases Nat.eq_zero_or_pos p with rfl | hp
              · rw [ht0] at h; linarith only [h, hε]
              · exact hp
            -- contraction for good tau
            have hgood : ∀ (p : ℕ) (U : Trial n), A.accepted.x p ∈ P.D →
                StrongConvexOn P.D μ (A.accepted.Γ p) →
                P.IsProxMin (A.accepted.Γ p) (A.accepted.xc p) lam (A.accepted.x p) →
                (∃ i ≤ p, A.accepted.y p = A.accepted.x i) →
                IsTrial P lam ε A.accepted (p + 1) U →
                ε / 2 < A.accepted.t P lam p → 0 ≤ U.τ → U.τ ≤ 1 → (1 - U.τ) * B ≤ U.τ →
                U.t P lam ≤ U.τ * A.accepted.t P lam p + (1 - U.τ) * ε / 4 := by
              intro p U hxp hGS hGp hy hU ht h0 h1 hBU
              obtain ⟨iy, hiy, hyx⟩ := hy
              obtain ⟨-, hU2, hUp, -, hUy2, hUy3⟩ := hU
              obtain ⟨hUxc, hUΓ⟩ := hU2 ht
              rw [Nat.add_sub_cancel] at hUxc hUΓ
              obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp0 p ht; omega⟩
              have hUD := hUp.1
              have k3 : P.φ U.y ≤ P.φ (A.accepted.y (q + 1)) := by
                rw [hyx]; exact hUy2 iy (Nat.lt_succ_of_le hiy)
              have k1 := hprox _ _ _ hGS hGp U.x hUD
              have k2 := hlin U.x hUD _ hxp
              rw [htS]
              unfold Trial.t Trial.m
              rw [hUΓ _ hUD, hUxc]
              exact hR1 _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 k1 k2 k3 hUy3
                (div_nonneg (sq_nonneg _) (by linarith only [hlam])) (hRτ _ _ h1 hBU)
            -- invariant
            have hInv : ∀ j : ℕ, A.accepted.x j ∈ P.D ∧ 0 ≤ A.τ j ∧
                1 / (2 * (1 + B)) ≤ 1 - A.τ j ∧
                (1 ≤ j → StrongConvexOn P.D μ (A.accepted.Γ j) ∧
                  (∀ u ∈ P.D, A.accepted.Γ j u ≤ P.φ u) ∧
                  P.IsProxMin (A.accepted.Γ j) (A.accepted.xc j) lam (A.accepted.x j)) ∧
                (∃ i ≤ j, A.accepted.y j = A.accepted.x i) := by
              intro j
              induction j with
              | zero =>
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · rw [hx00]; exact hx0
                · rw [hτ0]
                · rw [hτ0, sub_zero]; exact hle1
                · intro h; omega
                · exact ⟨0, le_rfl, by rw [hy00, hx00]⟩
              | succ p ih =>
                obtain ⟨hxD, hτn, hτu, hG, hyx⟩ := ih
                obtain ⟨hc, hτi, htr, hrej, -, hτj, hxj, hyj, hxcj, hΓj⟩ := hstep (p + 1) (Nat.succ_pos p)
                rw [Nat.add_sub_cancel] at hτi
                have htau : ∀ q : ℕ, q < A.count (p + 1) → 0 ≤ (A.trial (p + 1) q).τ ∧
                    1 / (2 * (1 + B)) ≤ 1 - (A.trial (p + 1) q).τ := by
                  intro q
                  induction q with
                  | zero =>
                    intro _
                    rw [hτi]
                    exact ⟨div_nonneg hτn (zero_le_one.trans hβ),
                      hτu.trans (sub_le_sub_left (div_le_self hτn hβ) 1)⟩
                  | succ q ihq =>
                    intro hq
                    obtain ⟨h0, h1⟩ := ihq (Nat.lt_of_succ_lt hq)
                    obtain ⟨⟨hr1, hr2⟩, hr3⟩ := hrej q hq
                    rw [Nat.add_sub_cancel] at hr1 hr2
                    have hb : (A.trial (p + 1) q).τ < (1 - (A.trial (p + 1) q).τ) * B := by
                      refine lt_of_not_ge fun hb => ?_
                      obtain ⟨g1, -, g3⟩ := hG (hp0 p hr1)
                      exact absurd hr2 (not_lt.2 (hgood p _ hxD g1 g3 hyx (htr q (Nat.lt_of_succ_lt hq)) hr1 h0
                        (by linarith only [h1, hpos]) hb))
                    rw [hr3]
                    exact ⟨by linarith only [h0], hRtr _ h1 hb⟩
                have hlast : A.count (p + 1) - 1 < A.count (p + 1) := by omega
                obtain ⟨hU0, hU1⟩ := htau _ hlast
                have hUt := htr _ hlast
                clear htau hrej htr
                obtain ⟨U, hUset⟩ : ∃ U, U = A.trial (p + 1) (A.count (p + 1) - 1) := ⟨_, rfl⟩
                rw [← hUset] at hU0 hU1 hUt hτj hxj hyj hxcj hΓj
                obtain ⟨hT1, hT2, hTp, hTy, -, -⟩ := hUt
                rw [Nat.add_sub_cancel] at hT1 hT2
                have hUle : U.τ ≤ 1 := by linarith only [hU1, hpos]
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · rw [hxj]; exact hTp.1
                · rw [hτj]; exact hU0
                · rw [hτj]; exact hU1
                · intro _
                  have hprox' : P.IsProxMin (A.accepted.Γ (p + 1)) (A.accepted.xc (p + 1)) lam
                      (A.accepted.x (p + 1)) := by
                    refine ⟨by rw [hxj]; exact hTp.1, ?_⟩
                    intro u hu
                    rw [hxj, hxcj, hΓj u hu, hΓj _ hTp.1]
                    exact hTp.2 u hu
                  rcases le_or_gt (A.accepted.t P lam p) (ε / 2) with h | h
                  · have hform : ∀ u ∈ P.D, A.accepted.Γ (p + 1) u =
                        P.ellf u (A.accepted.x p) + P.h u := fun u hu =>
                      (hΓj u hu).trans ((hT1 h).2 u hu)
                    refine ⟨hcutSC _ _ hform, ?_, hprox'⟩
                    intro u hu
                    rw [hform u hu]; exact hcutle _ hxD u hu
                  · have hform : ∀ u ∈ P.D, A.accepted.Γ (p + 1) u = U.τ * A.accepted.Γ p u +
                        (1 - U.τ) * (P.ellf u (A.accepted.x p) + P.h u) := fun u hu =>
                      (hΓj u hu).trans ((hT2 h).2 u hu)
                    obtain ⟨g1, g2, -⟩ := hG (hp0 p h)
                    refine ⟨hcombSC U.τ (A.accepted.Γ p) (fun u => P.ellf u (A.accepted.x p) + P.h u) _
                      hU0 hUle g1 (hcutSC (A.accepted.x p) _ (fun u _ => rfl)) hform, ?_, hprox'⟩
                    intro u hu
                    rw [hform u hu]
                    have l1 := mul_le_mul_of_nonneg_left (g2 u hu) hU0
                    have l2 := mul_le_mul_of_nonneg_left (hcutle _ hxD u hu) (sub_nonneg.2 hUle)
                    linarith only [l1, l2]
                · rcases hTy with ⟨i, hi, hy⟩ | hy
                  · exact ⟨i, hi.le, by rw [hyj, hy]⟩
                  · exact ⟨p + 1, le_rfl, by rw [hyj, hy, hxj]⟩
            have hyle : ∀ p : ℕ, P.φ (A.accepted.y (p + 1)) ≤ P.φ (A.accepted.x (p + 1)) := by
              intro p
              obtain ⟨hc, -, htr, -, -, -, hxj, hyj, -, -⟩ := hstep (p + 1) (Nat.succ_pos p)
              rw [hyj, hxj]
              exact (htr (A.count (p + 1) - 1) (by omega)).2.2.2.2.2
            have hcyc1 : ∀ p : ℕ, A.accepted.t P lam p ≤ ε / 2 →
                A.accepted.xc (p + 1) = A.accepted.x p ∧
                    ∀ u ∈ P.D, A.accepted.Γ (p + 1) u = P.ellf u (A.accepted.x p) + P.h u := by
              intro p h
              obtain ⟨hc, -, htr, -, -, -, -, -, hxcj, hΓj⟩ := hstep (p + 1) (Nat.succ_pos p)
              obtain ⟨g1, g2⟩ := (htr (A.count (p + 1) - 1) (by omega)).1 h
              rw [Nat.add_sub_cancel] at g1 g2
              exact ⟨hxcj.trans g1, fun u hu => (hΓj u hu).trans (g2 u hu)⟩
            have hcyc2 : ∀ p : ℕ, ε / 2 < A.accepted.t P lam p →
                A.accepted.xc (p + 1) = A.accepted.xc p ∧
                A.accepted.t P lam (p + 1) ≤
                  A.τ (p + 1) * A.accepted.t P lam p + (1 - A.τ (p + 1)) * ε / 4 := by
              intro p h
              obtain ⟨hc, -, htr, -, hnrej, hτj, hxj, hyj, hxcj, hΓj⟩ := hstep (p + 1) (Nat.succ_pos p)
              have hUt := htr (A.count (p + 1) - 1) (by omega)
              obtain ⟨g1, -⟩ := hUt.2.1 h
              rw [Nat.add_sub_cancel] at g1
              refine ⟨hxcj.trans g1, ?_⟩
              have hn := not_lt.1 (fun hh => hnrej ⟨h, hh⟩)
              rw [htS, hτj, hyj, hxj, hxcj, hΓj _ hUt.2.2.1.1]
              exact hn
            have hxD : ∀ j, A.accepted.x j ∈ P.D := fun j => (hInv j).1
            -- key directional inequality
            have hdir : ∀ u ∈ P.D, ∀ v ∈ P.D,
                P.ellf x0s v + P.h x0s - (P.ellf u v + P.h u) ≤
                  (2 * Mbar + Lbar * ‖v - x0s‖) * ‖x0s - u‖ := by
              intro u hu v hv
              refine hlim _ _ (Lbar * ‖x0s - u‖ * ‖x0s - u‖) (by positivity) ?_
              intro t ht ht1
              have h1t : 0 ≤ 1 - t := sub_nonneg.2 ht1.le
              have hab : t + (1 - t) = 1 := add_sub_cancel _ _
              have hz := hSC.1 hu hsD ht.le h1t hab
              have q3 := hSC.2 hu hsD ht.le h1t hab
              obtain ⟨z, hzdef⟩ : ∃ z, z = t • u + (1 - t) • x0s := ⟨_, rfl⟩
              rw [← hzdef] at hz q3
              have q1 : P.f x0s + P.h x0s ≤ P.f z + P.h z := hsmin z hz
              have q2 : P.f z + inner ℝ (P.f' z) (x0s - z) ≤ P.f x0s := hsub z hz x0s hsD
              have q3' : P.h z ≤ t * P.h u + (1 - t) * P.h x0s - t * (1 - t) * (μ / 2 * ‖u - x0s‖ ^ 2) := q3
              have q4 : 0 ≤ t * (1 - t) * (μ / 2 * ‖u - x0s‖ ^ 2) := by positivity
              have ez : x0s - z = t • (x0s - u) := by rw [hzdef]; module
              have ev : v - z = (v - x0s) + t • (x0s - u) := by rw [hzdef]; module
              rw [ez, real_inner_smul_right] at q2
              have q5 : P.h x0s - P.h u + inner ℝ (P.f' z) (x0s - u) ≤ 0 := by
                have : t * (P.h x0s - P.h u + inner ℝ (P.f' z) (x0s - u)) ≤ t * 0 := by
                  linarith only [q1, q2, q3', q4]
                exact le_of_mul_le_mul_left this ht
              have q6 := real_inner_le_norm (P.f' v - P.f' z) (x0s - u)
              have q8 : ‖v - z‖ ≤ ‖v - x0s‖ + t * ‖x0s - u‖ := by
                rw [ev]
                refine (norm_add_le _ _).trans ?_
                rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
              have q9 : ‖P.f' v - P.f' z‖ ≤ 2 * Mbar + Lbar * (‖v - x0s‖ + t * ‖x0s - u‖) :=
                (hA v hv z hz).trans (add_le_add_right (mul_le_mul_of_nonneg_left q8 hL) _)
              have q10 := mul_le_mul_of_nonneg_right q9 (norm_nonneg (x0s - u))
              have e5 : (inner ℝ (P.f' v) (x0s - v) : ℝ) - inner ℝ (P.f' v) (u - v)
                  = inner ℝ (P.f' v) (x0s - u) := by
                rw [← inner_sub_right, sub_sub_sub_cancel_right]
              rw [inner_sub_left] at q6
              unfold Instance.ellf
              linarith only [q5, q6, q10, e5]
            -- first gap of a cycle
            have hfirst : ∀ a : ℕ, A.accepted.t P lam a ≤ ε / 2 → ‖A.accepted.x a - x0s‖ ≤ ‖x0 - x0s‖ →
                A.accepted.t P lam (a + 1) ≤ tbar Mbar Lbar lam ‖x0 - x0s‖ := by
              intro a hta hda
              obtain ⟨-, -, -, hG, -⟩ := hInv (a + 1)
              obtain ⟨hGS, -, hGp⟩ := hG (Nat.succ_pos a)
              obtain ⟨hxc, hΓ⟩ := hcyc1 a hta
              have hu := hxD (a + 1)
              have hv := hxD a
              have k1 := hprox _ _ _ hGS hGp x0s hsD
              have k2 := hlin _ hu _ hv
              have k3 := hdir _ hu _ hv
              have k0 : P.φ (A.accepted.y (a + 1)) ≤ P.f (A.accepted.x (a + 1)) + P.h (A.accepted.x (a + 1)) :=
                hyle a
              rw [htS, hxc, hΓ _ hu]
              rw [hxc, hΓ _ hu, hΓ _ hsD, norm_sub_rev x0s (A.accepted.x a)] at k1
              have hs0 := norm_nonneg (A.accepted.x (a + 1) - A.accepted.x a)
              have hd0 := norm_nonneg (A.accepted.x a - x0s)
              generalize ‖A.accepted.x (a + 1) - A.accepted.x a‖ = s at *
              generalize ‖x0s - A.accepted.x (a + 1)‖ = e at *
              generalize ‖A.accepted.x a - x0s‖ = d at *
              have k5 := hRt s _ hs0 (hRs s e d ‖x0 - x0s‖ hd0 hda (hRk s e d _ (by linarith only [k1, k3])))
              have k9 : 0 ≤ s ^ 2 / (2 * lam) := by positivity
              unfold tbar
              linarith only [k5, k9, k0, k2]
            clear hdir hlin hgood hcombSC hcutSC hcutle hell hcomb hcomb0 haff hlim hR1 hRτ hRprox hRk hRt hRs hA hstep hyle
            -- cycle length
            have htb0 : 0 ≤ tbar Mbar Lbar lam ‖x0 - x0s‖ := by
              unfold tbar; positivity
            obtain ⟨T, hT⟩ : ∃ T, T = tbar Mbar Lbar lam ‖x0 - x0s‖ := ⟨_, rfl⟩
            rw [← hT] at htb0 hfirst ⊢
            obtain ⟨LF, hLF⟩ : ∃ LF, LF = logFactor T ε := ⟨_, rfl⟩
            have hLF0 : 0 ≤ LF := by
              rw [hLF]; unfold logFactor
              split_ifs
              · exact le_rfl
              · exact le_max_right _ _
            have hLFT : 0 < T → Real.log (4 * T / ε) ≤ LF := by
              intro h
              rw [hLF]; unfold logFactor
              rw [if_neg h.ne']
              exact le_max_left _ _
            have hBLF : 0 ≤ 2 * (1 + B) * LF := mul_nonneg hB1.le hLF0
            obtain ⟨N, hN⟩ : ∃ N, N = ⌈2 * (1 + B) * LF⌉₊ := ⟨_, rfl⟩
            have hNge : 2 * (1 + B) * LF ≤ N := by rw [hN]; exact Nat.le_ceil _
            have hNlt : (N : ℝ) < 2 * (1 + B) * LF + 1 := by rw [hN]; exact Nat.ceil_lt_add_one hBLF
            have hcycle : ∀ a : ℕ, A.accepted.t P lam a ≤ ε / 2 →
                ‖A.accepted.x a - x0s‖ ≤ ‖x0 - x0s‖ →
                ∃ b : ℕ, a < b ∧ b ≤ a + (N + 1) ∧ A.accepted.t P lam b ≤ ε / 2 ∧
                  A.accepted.xc b = A.accepted.x a := by
              intro a hta hda
              by_contra hcon
              have hcon' : ∀ b : ℕ, a < b → b ≤ a + (N + 1) → A.accepted.xc b = A.accepted.x a →
                  ε / 2 < A.accepted.t P lam b := fun b h1 h2 h3 =>
                lt_of_not_ge fun h4 => hcon ⟨b, h1, h2, h4, h3⟩
              have hf := hfirst a hta hda
              have hall : ∀ k : ℕ, k ≤ N → A.accepted.xc (a + 1 + k) = A.accepted.x a ∧
                  ε / 2 < A.accepted.t P lam (a + 1 + k) ∧
                  A.accepted.t P lam (a + 1 + k) - ε / 4 ≤
                    (1 - 1 / (2 * (1 + B))) ^ k * (T - ε / 4) := by
                intro k
                induction k with
                | zero =>
                  intro _
                  have hxc := (hcyc1 a hta).1
                  refine ⟨hxc, hcon' (a + 1) (by omega) (by omega) hxc, ?_⟩
                  rw [pow_zero, one_mul]
                  exact sub_le_sub_right hf _
                | succ k ih =>
                  intro hk
                  obtain ⟨h1, h2, h3⟩ := ih (by omega)
                  obtain ⟨-, hτ0', hτ1', -, -⟩ := hInv (a + 1 + k + 1)
                  obtain ⟨hc1, hc2⟩ := hcyc2 (a + 1 + k) h2
                  have hxc : A.accepted.xc (a + 1 + k + 1) = A.accepted.x a := hc1.trans h1
                  refine ⟨hxc, hcon' (a + 1 + k + 1) (by omega) (by omega) hxc, ?_⟩
                  rw [pow_succ', ← add_assoc, mul_assoc]
                  have h4 := mul_le_mul_of_nonneg_left h3 (sub_nonneg.2 hle1)
                  have h5 : A.τ (a + 1 + k + 1) * (A.accepted.t P lam (a + 1 + k) - ε / 4) ≤
                      (1 - 1 / (2 * (1 + B))) * (A.accepted.t P lam (a + 1 + k) - ε / 4) :=
                    mul_le_mul_of_nonneg_right (by linarith only [hτ1']) (by linarith only [h2, hε])
                  linarith only [h4, h5, hc2]
              obtain ⟨-, h2, h3⟩ := hall N le_rfl
              exact hRlog N T LF _ htb0 hLF0 hNge hLFT h2 h3
            -- serious step
            have hserious : ∀ a b : ℕ, a < b → A.accepted.t P lam b ≤ ε / 2 →
                A.accepted.xc b = A.accepted.x a → ε < P.φ (A.accepted.y b) - P.φ x0s →
                (1 + lam * μ) * ‖A.accepted.x b - x0s‖ ^ 2 + lam * ε ≤ ‖A.accepted.x a - x0s‖ ^ 2 := by
              intro a b hab htb hxc hgap
              obtain ⟨p, rfl⟩ : ∃ p, b = p + 1 := ⟨b - 1, by omega⟩
              obtain ⟨-, -, -, hG, -⟩ := hInv (p + 1)
              obtain ⟨hGS, hGle, hGp⟩ := hG (Nat.succ_pos p)
              have k1 := hprox _ _ _ hGS hGp x0s hsD
              have k2 := hGle x0s hsD
              rw [htS] at htb
              rw [hxc] at k1 htb
              rw [norm_sub_rev x0s, norm_sub_rev x0s] at k1
              exact hRser _ _ _ _ _ _ htb (k1.trans (add_le_add_left k2 _)) hgap
            have hr0 : 0 ≤ ‖x0 - x0s‖ ^ 2 := sq_nonneg _
            obtain ⟨ser, hser⟩ : ∃ ser, ser = serBound μ lam ε (‖x0 - x0s‖ ^ 2) := ⟨_, rfl⟩
            have hser0 : 0 ≤ ser := by rw [hser]; exact hserB0 _ hr0
            have hmain : ∃ j : ℕ, (j : ℝ) ≤ ((N : ℝ) + 1) * (ser + 1) ∧
                P.φ (A.accepted.y j) - P.φ x0s ≤ ε := by
              by_contra hcon
              have hcon' : ∀ j : ℕ, (j : ℝ) ≤ ((N : ℝ) + 1) * (ser + 1) →
                  ε < P.φ (A.accepted.y j) - P.φ x0s := fun j h1 =>
                lt_of_not_ge fun h2 => hcon ⟨j, h1, h2⟩
              obtain ⟨K, hK⟩ : ∃ K, K = ⌊ser⌋₊ + 1 := ⟨_, rfl⟩
              have hK1 : ser < K := by rw [hK]; push_cast; exact Nat.lt_floor_add_one ser
              have hK2 : (K : ℝ) ≤ ser + 1 := by
                rw [hK]; push_cast; linarith only [Nat.floor_le hser0]
              have hN0 : 0 ≤ (N : ℝ) + 1 := by positivity
              have hlε : 0 < lam * ε := mul_pos hlam hε
              have hind : ∀ k : ℕ, k ≤ K → ∃ i : ℕ, i ≤ (N + 1) * k ∧ A.accepted.t P lam i ≤ ε / 2 ∧
                  k * (lam * ε) + ‖A.accepted.x i - x0s‖ ^ 2 ≤ ‖x0 - x0s‖ ^ 2 ∧
                  (1 + lam * μ) ^ k * (μ * ‖A.accepted.x i - x0s‖ ^ 2 + ε) ≤ μ * ‖x0 - x0s‖ ^ 2 + ε := by
                intro k
                induction k with
                | zero =>
                  intro _
                  refine ⟨0, le_rfl, ?_, ?_, ?_⟩
                  · rw [ht0]; linarith only [hε]
                  · rw [hx00, Nat.cast_zero, zero_mul, zero_add]
                  · rw [hx00, pow_zero, one_mul]
                | succ k ih =>
                  intro hk
                  obtain ⟨a, ha, hta, h1, h2⟩ := ih (Nat.le_of_succ_le hk)
                  have hda : ‖A.accepted.x a - x0s‖ ≤ ‖x0 - x0s‖ := by
                    apply le_of_sq_le_sq _ (norm_nonneg _)
                    have : 0 ≤ (k : ℝ) * (lam * ε) := mul_nonneg (Nat.cast_nonneg k) hlε.le
                    linarith only [this, h1]
                  obtain ⟨b, hab, hb, htb, hxc⟩ := hcycle a hta hda
                  have hbk : b ≤ (N + 1) * (k + 1) := by
                    rw [Nat.mul_succ]; omega
                  have hbR : (b : ℝ) ≤ ((N : ℝ) + 1) * (ser + 1) := by
                    have e1 : b ≤ (N + 1) * K := hbk.trans (Nat.mul_le_mul_left _ hk)
                    have e2 : (b : ℝ) ≤ ((N : ℝ) + 1) * K := by exact_mod_cast e1
                    exact e2.trans (mul_le_mul_of_nonneg_left hK2 hN0)
                  have hs := hserious a b hab htb hxc (hcon' b hbR)
                  have hbn := sq_nonneg ‖A.accepted.x b - x0s‖
                  refine ⟨b, hbk, htb, ?_, ?_⟩
                  · rw [Nat.cast_succ]
                    have : 0 ≤ lam * μ * ‖A.accepted.x b - x0s‖ ^ 2 :=
                      mul_nonneg (mul_nonneg hlam.le hμ) hbn
                    linarith only [this, hs, h1]
                  · rw [pow_succ, mul_assoc]
                    refine le_trans (mul_le_mul_of_nonneg_left ?_ (pow_nonneg hθ0.le k)) h2
                    have := mul_le_mul_of_nonneg_left hs hμ
                    linarith only [this]
              obtain ⟨i, -, -, h1, h2⟩ := hind K le_rfl
              have hKser := hRK K _ _ (sq_nonneg _) hr0 h1 h2
              rw [← hser] at hKser
              exact absurd hK1 (not_lt.2 hKser)
            have hceil : ((⌈2 * (1 + B) * LF⌉ : ℤ) : ℝ) = (N : ℝ) := by
              rw [hN]
              exact (natCast_ceil_eq_intCast_ceil hBLF).symm
            have hbd : adaptiveBound μ lam ε Mbar Lbar ‖x0 - x0s‖ = ((N : ℝ) + 1) * (ser + 1) := by
              unfold adaptiveBound
              rw [← hceil, hser, hLF, hT, hBset, hwset, hSset]
            obtain ⟨j, hj, hjo⟩ := hmain
            refine ⟨⟨j, by rw [hbd]; exact hj, hjo⟩, ?_⟩
            intro hSI
            rw [← hSset] at hSI ⊢
            rw [hser] at hj
            rw [← hLF]
            exact ⟨j, hj.trans (hrate N LF _ hLF0 hr0 hNlt hSI), hjo⟩
