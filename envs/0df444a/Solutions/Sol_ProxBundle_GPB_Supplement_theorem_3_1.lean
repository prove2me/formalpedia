-- Prove2me | solution 1 for ProxBundle.GPB.Supplement.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:34:50.335056+00:00
-- url     : https://prove2.me/submissions/899f831e-cecf-438d-8367-b8d44ef86f0a

import Mathlib
import Definitions.Def_ProxBundle_GPB_Model
import Definitions.Def_ProxBundle_GPB_Supplement_Rates

open ProxBundle
open ProxBundle.GPB
open ProxBundle.GPB.Supplement

/-- Theorem 3.1: the full interval and both regimes, with one explicit logarithmic
factor and a constant depending only on the fixed universal input C. -/
theorem solution (C : ℝ) (hC : 0 < C)
    {n : ℕ} (P : Instance n) (μ Mf Lf Mbar Lbar lam ε : ℝ)
    (x0 x0s : E n) (R : Run n)
    (hμ : 0 ≤ μ) (hMf : 0 ≤ Mf) (hLf : 0 ≤ Lf)
    (hA1 : P.A1 μ) (hA3 : P.A3 Mf Lf)
    (hmin : P.IsMinPair ε Mbar Lbar)
    (hx0s : P.IsNearestOpt x0 x0s) (hx0 : x0 ∈ P.D)
    (hlam : 0 < lam) (hε : 0 < ε)
    (hinterval : StepInterval C ε (Mf ^ 2 + ε * Lf) lam (‖x0 - x0s‖ ^ 2))
    (hrun : IsRun P μ lam ε (tau38 μ lam ε Mf Lf) x0 R) :
    Obtains P R x0s ε
      (K31 C * (logFactor (tbar Mbar Lbar lam ‖x0 - x0s‖) ε + 1) *
        (rate μ ε (Mf ^ 2 + ε * Lf) (‖x0 - x0s‖ ^ 2) + 1)) := by
          have hM : ∀ (S d0 tb θ A Lg : ℝ) (k : ℕ), 0 < S → ε / (C * S) ≤ lam → lam ≤ C * d0 ^ 2 / ε →
              θ - 1 = lam * μ → 1 ≤ θ → A = 1 + 8 * lamMu μ lam * S / ε → 1 ≤ A → 0 < d0 → 0 < tb →
              Lg = A * max (Real.log (16 * tb / ε)) 0 → 0 ≤ rate μ ε S (d0 ^ 2) → 0 ≤ logFactor tb ε →
              (k:ℝ) * lam * ε ≤ d0 ^ 2 → (0 < μ → θ ^ k * (ε / μ) ≤ d0 ^ 2 + ε / μ) →
              ((k : ℝ) + 1) * (Lg + 2) ≤ K31 C * (logFactor tb ε + 1) * (rate μ ε S (d0 ^ 2) + 1) := by
            clear hrun hinterval hx0 hx0s hmin hA3 hA1 hLf hMf R x0 x0s Mbar Lbar Mf Lf P
            intro S d0 tb θ A Lg k hS hlamlo hlamhi hθ' hθ1 hAd hA1' hd0pos htbpos hLg hrate0 hlog0 hkd hkμ
            have hθ : θ = 1 + lam * μ := by linarith only [hθ']
            obtain ⟨c, hc⟩ : ∃ c, c = max C 1 := ⟨_, rfl⟩
            have hc1 : 1 ≤ c := hc ▸ le_max_right _ _
            have hCc : C ≤ c := hc ▸ le_max_left _ _
            have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
            have hLb : Lg ≤ A * (logFactor tb ε + 1.4) := by
              rw [hLg]
              apply mul_le_mul_of_nonneg_left _ (le_trans zero_le_one hA1')
              have h4 : Real.log 4 ≤ 1.4 := by
                have e : (4:ℝ) = 2 ^ 2 := by norm_num
                rw [e, Real.log_pow]; have := Real.log_two_lt_d9; push_cast; linarith only [this]
              have e : Real.log (16 * tb / ε) = Real.log (4 * tb / ε) + Real.log 4 := by
                rw [← Real.log_mul (div_pos (mul_pos four_pos htbpos) hε).ne' (by norm_num)]; congr 1; ring
              apply max_le
              · rw [e]; unfold logFactor; rw [if_neg htbpos.ne']
                have := le_max_left (Real.log (4 * tb / ε)) 0; linarith only [this, h4]
              · linarith only [hlog0]
            have hCS : 0 < C * S := mul_pos hC hS
            have hlo' : ε ≤ C * S * lam := by
              rw [div_le_iff₀ hCS] at hlamlo; linarith only [hlamlo]
            have hhi' : lam * ε ≤ C * d0 ^ 2 := by
              rwa [le_div_iff₀ hε] at hlamhi
            have hlm : lamMu μ lam ≤ lam := by
              unfold lamMu; rw [← hθ]; exact div_le_self hlam.le hθ1
            have hlm0 : 0 < lamMu μ lam := by unfold lamMu; rw [← hθ]; exact div_pos hlam (lt_of_lt_of_le one_pos hθ1)
            -- three bounds for each regime
            have hB1 : (k:ℝ) ≤ c * (S * d0 ^ 2 / ε ^ 2) ∧ k * A ≤ (c + 8) * (S * d0 ^ 2 / ε ^ 2) ∧
                A ≤ 1 + 8 * (c * (S * d0 ^ 2 / ε ^ 2)) := by
              have hρ0 : 0 ≤ S * d0 ^ 2 / ε ^ 2 := div_nonneg (mul_nonneg hS.le (sq_nonneg _)) (sq_nonneg _)
              have a1 : (k:ℝ) ≤ c * (S * d0 ^ 2 / ε ^ 2) := by
                have : (k:ℝ) ≤ C * (S * d0 ^ 2 / ε ^ 2) := by
                  have h1 : (k:ℝ) * ε ^ 2 ≤ C * S * d0 ^ 2 := by
                    have h1 := mul_le_mul_of_nonneg_left hkd hCS.le
                    have h2 := mul_le_mul_of_nonneg_left hlo' (mul_nonneg hk0 hε.le)
                    linear_combination h1 + h2
                  have : (k:ℝ) ≤ (C * S * d0 ^ 2) / ε ^ 2 := (le_div_iff₀ (pow_pos hε 2)).2 h1
                  calc (k:ℝ) ≤ _ := this
                    _ = _ := by ring
                exact this.trans (mul_le_mul_of_nonneg_right hCc hρ0)
              have hSe : 0 ≤ S / ε := div_nonneg hS.le hε.le
              have hSe2 : 0 ≤ S / ε ^ 2 := div_nonneg hS.le (sq_nonneg _)
              have a0 : lamMu μ lam * S / ε ≤ (lam * ε) * (S / ε ^ 2) := by
                have h1 := mul_le_mul_of_nonneg_right hlm hSe
                have e : (lam * ε) * (S / ε ^ 2) = lam * (S / ε) := by field_simp
                rw [e, mul_div_assoc]; exact h1
              have a2 : k * (lamMu μ lam * S / ε) ≤ S * d0 ^ 2 / ε ^ 2 := by
                have h1 := mul_le_mul_of_nonneg_left a0 hk0
                have h2 := mul_le_mul_of_nonneg_right hkd hSe2
                linear_combination h1 + h2
              have a3 : lamMu μ lam * S / ε ≤ c * (S * d0 ^ 2 / ε ^ 2) := by
                have h1 := mul_le_mul_of_nonneg_right hhi' hSe2
                have h2 := mul_le_mul_of_nonneg_right hCc hρ0
                linear_combination a0 + h1 + h2
              have eA : A = 1 + 8 * (lamMu μ lam * S / ε) := by rw [hAd]; ring
              refine ⟨a1, ?_, ?_⟩
              · rw [eA]; linear_combination a1 + 8 * a2
              · rw [eA]; linear_combination 8 * a3
            have hB2 : 0 < μ → (k:ℝ) ≤ c * ((S / (μ * ε) + 1) * Real.log (1 + μ * d0 ^ 2 / ε)) ∧
                k * A ≤ (c + 8) * ((S / (μ * ε) + 1) * Real.log (1 + μ * d0 ^ 2 / ε)) ∧
                A ≤ 1 + 8 * (c * ((S / (μ * ε) + 1) * Real.log (1 + μ * d0 ^ 2 / ε))) := by
              intro hμ0
              obtain ⟨y, hy⟩ : ∃ y, y = μ * d0 ^ 2 / ε := ⟨_, rfl⟩
              have hy0 : 0 < y := by rw [hy]; positivity
              rw [← hy]
              obtain ⟨Λ, hΛ⟩ : ∃ Λ, Λ = Real.log (1 + y) := ⟨_, rfl⟩
              rw [← hΛ]
              obtain ⟨σ, hσ⟩ : ∃ σ, σ = S / (μ * ε) := ⟨_, rfl⟩
              have hσ0 : 0 < σ := by rw [hσ]; exact div_pos hS (mul_pos hμ0 hε)
              rw [← hσ]
              have hθp : 0 < θ := lt_of_lt_of_le one_pos hθ1
              have hyΛ : y / (1 + y) ≤ Λ := by
                have := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + y by linarith only [hy0])
                rw [← hΛ] at this
                have e : y / (1 + y) = 1 - (1 + y)⁻¹ := by field_simp; ring
                rw [e]; exact this
              have hΛ0 : 0 ≤ Λ := le_trans (div_nonneg hy0.le (by linarith only [hy0])) hyΛ
              have hpow : θ ^ k ≤ 1 + y := by
                have h1 := hkμ hμ0
                have h2 := mul_le_mul_of_nonneg_right h1 (div_nonneg hμ0.le hε.le)
                have e1 : θ ^ k * (ε / μ) * (μ / ε) = θ ^ k := by field_simp
                have e2 : (d0 ^ 2 + ε / μ) * (μ / ε) = 1 + y := by rw [hy]; field_simp; ring
                rw [e1, e2] at h2; exact h2
              have hklog : k * Real.log θ ≤ Λ := by
                rw [← Real.log_pow, hΛ]
                exact Real.log_le_log (by positivity) hpow
              have hlogθ : μ * lamMu μ lam ≤ Real.log θ := by
                have := Real.one_sub_inv_le_log_of_pos hθp
                have e : μ * lamMu μ lam = 1 - θ⁻¹ := by
                  unfold lamMu; rw [← hθ]; field_simp; linarith only [hθ]
                rw [e]; exact this
              have hkm : k * (μ * lamMu μ lam) ≤ Λ := (mul_le_mul_of_nonneg_left hlogθ hk0).trans hklog
              have hinv : 1 ≤ (μ * lamMu μ lam) * (C * σ + 1) := by
                have e : (μ * lamMu μ lam) * (C * σ + 1) = (C * S * lam / ε + lam * μ) / θ := by
                  unfold lamMu; rw [← hθ, hσ]; field_simp
                rw [e, le_div_iff₀ hθp, hθ]
                have : 1 ≤ C * S * lam / ε := by rw [le_div_iff₀ hε]; linarith only [hlo']
                linarith only [this]
              have a1 : (k:ℝ) ≤ (C * σ + 1) * Λ := by
                have h1 := mul_le_mul_of_nonneg_left hinv hk0
                have h2 := mul_le_mul_of_nonneg_right hkm (add_nonneg (mul_nonneg hC.le hσ0.le) zero_le_one)
                linear_combination h1 + h2
              have hσΛ : 0 ≤ σ * Λ := mul_nonneg hσ0.le hΛ0
              have hcΛ : 1 * Λ ≤ c * Λ := mul_le_mul_of_nonneg_right hc1 hΛ0
              have hCσ : C * (σ * Λ) ≤ c * (σ * Λ) := mul_le_mul_of_nonneg_right hCc hσΛ
              have a1' : (k:ℝ) ≤ c * ((σ + 1) * Λ) := by linear_combination a1 + hcΛ + hCσ
              have eA : A = 1 + 8 * ((μ * lamMu μ lam) * σ) := by
                rw [hAd, hσ]; field_simp
              have a2 : k * ((μ * lamMu μ lam) * σ) ≤ σ * Λ := by
                linear_combination mul_le_mul_of_nonneg_right hkm hσ0.le
              have a3 : μ * lamMu μ lam ≤ c * Λ := by
                have h1 : μ * lamMu μ lam ≤ c * (y / (1 + y)) := by
                  unfold lamMu; rw [← hθ, mul_div_assoc', mul_div_assoc', div_le_div_iff₀ hθp (by linarith only [hy0]), hθ]
                  have hx : lam * μ ≤ c * y := by
                    have : lam * ε * μ ≤ C * d0 ^ 2 * μ := mul_le_mul_of_nonneg_right hhi' hμ
                    have h2 : lam * μ ≤ C * y := by
                      have e : C * y = (C * d0 ^ 2 * μ) / ε := by rw [hy]; ring
                      rw [e, le_div_iff₀ hε]; linear_combination this
                    exact h2.trans (mul_le_mul_of_nonneg_right hCc hy0.le)
                  have hx0 : 0 ≤ lam * μ * y := mul_nonneg (mul_nonneg hlam.le hμ) hy0.le
                  have := mul_le_mul_of_nonneg_right hc1 hx0
                  linear_combination this + hx
                exact h1.trans (mul_le_mul_of_nonneg_left hyΛ (le_trans zero_le_one hc1))
              have a3' := mul_le_mul_of_nonneg_right a3 hσ0.le
              refine ⟨a1', ?_, ?_⟩
              · rw [eA]; linear_combination a1' + 8 * a2 + 8 * hΛ0
              · rw [eA]; linear_combination 8 * a3' + 8 * mul_nonneg (le_trans zero_le_one hc1) hΛ0
            have hfinal : ∀ ρ : ℝ, 0 ≤ ρ → (k:ℝ) ≤ c * ρ → k * A ≤ (c + 8) * ρ → A ≤ 1 + 8 * (c * ρ) →
                ((k : ℝ) + 1) * (Lg + 2) ≤ K31 C * (logFactor tb ε + 1) * (ρ + 1) := by
              intro ρ hρ h1 h2 h3
              unfold K31
              rw [← hc]
              obtain ⟨l, hl⟩ : ∃ l, l = logFactor tb ε := ⟨_, rfl⟩
              rw [← hl] at hLb hlog0 ⊢
              have s1 : ((k:ℝ) + 1) * A ≤ 1 + (9 * c + 8) * ρ := by linear_combination h2 + h3
              have t1 := mul_le_mul_of_nonneg_left hLb (show (0:ℝ) ≤ k + 1 by linarith only [hk0])
              have t2 := mul_le_mul_of_nonneg_right s1 (show (0:ℝ) ≤ l + 1.4 by linarith only [hlog0])
              have hc0 : 0 ≤ c := le_trans zero_le_one hc1
              have q2 : 0 ≤ c * ρ * l := mul_nonneg (mul_nonneg hc0 hρ) hlog0
              have q3 : 0 ≤ ρ * l := mul_nonneg hρ hlog0
              have q4 : 0 ≤ c * l := mul_nonneg hc0 hlog0
              have q5 : 0 ≤ (c - 1) * ρ := mul_nonneg (sub_nonneg.2 hc1) hρ
              linear_combination t1 + t2 + 2 * h1 + 11 * q2 + 2 * q3 + 20 * q4 + 5.4 * q5 + 20 * hc1 + 9 * hlog0 + 4.2 * hρ
            rcases hμ.eq_or_lt with h0 | h0
            · unfold rate; rw [if_pos h0.symm]
              exact hfinal _ (by positivity) hB1.1 hB1.2.1 hB1.2.2
            · unfold rate at hrate0 ⊢; rw [if_neg h0.ne'] at hrate0 ⊢
              rcases min_choice (S * d0 ^ 2 / ε ^ 2) ((S / (μ * ε) + 1) * Real.log (1 + μ * d0 ^ 2 / ε)) with h | h
              · rw [h]; exact hfinal _ (by positivity) hB1.1 hB1.2.1 hB1.2.2
              · rw [h] at hrate0 ⊢; exact hfinal _ hrate0 (hB2 h0).1 (hB2 h0).2.1 (hB2 h0).2.2
          have hkeyN : ∀ M L d S' ε' : ℝ, 0 < ε' → 0 ≤ L → 0 ≤ d → S' = M ^ 2 + ε' * L →
              2 * M * d + L * d ^ 2 - 4 * S' / ε' * d ^ 2 ≤ ε' / 4 := by
            intro M L d S' ε' hε' hL hd hS'
            have e : 4 * S' / ε' * d ^ 2 = 4 * M ^ 2 * d ^ 2 / ε' + 4 * L * d ^ 2 := by
              rw [hS']; field_simp
            have e2 : 2 * M * d - ε' / 4 ≤ 4 * M ^ 2 * d ^ 2 / ε' := by
              rw [le_div_iff₀ hε']; linear_combination sq_nonneg (2 * M * d - ε' / 2)
            rw [e]; linear_combination e2 + 3 * mul_nonneg hL (sq_nonneg d)
          have hDb : ∀ a b d d0 lam M L : ℝ, 0 ≤ a → a ≤ d0 → 0 ≤ lam → 0 ≤ M → 0 ≤ L → 0 ≤ b →
              d ^ 2 + b ^ 2 ≤ a ^ 2 + 2 * lam * (2 * M + L * a) * a + 2 * lam * (4 * M + L * a) * b →
              d ^ 2 ≤ 16 * (max 1 (2 * lam * L) * d0 + lam * M) ^ 2 := by
            intro a b d d0 lam M L ha had hl hM hL hb h
            have h1 : 1 ≤ max 1 (2 * lam * L) := le_max_left _ _
            have h2 : 2 * lam * L ≤ max 1 (2 * lam * L) := le_max_right _ _
            obtain ⟨Mx, hMx⟩ : ∃ Mx, Mx = max 1 (2 * lam * L) := ⟨_, rfl⟩
            rw [← hMx] at h1 h2 ⊢
            have hd0 : 0 ≤ d0 := le_trans ha had
            have hA0 : 0 ≤ Mx * d0 := mul_nonneg (by linarith) hd0
            have hA1 : a ≤ Mx * d0 := le_trans had (le_mul_of_one_le_left hd0 h1)
            have hA2 : 2 * lam * L * a ≤ Mx * d0 :=
              calc 2 * lam * L * a ≤ Mx * a := mul_le_mul_of_nonneg_right h2 ha
                _ ≤ Mx * d0 := mul_le_mul_of_nonneg_left had (by linarith)
            have hp : 0 ≤ lam * M := mul_nonneg hl hM
            have hq : 0 ≤ 2 * lam * L * a := by positivity
            have hc0 := sq_nonneg (b - (8 * (lam * M) + 2 * lam * L * a) / 2)
            have h_a2 := mul_le_mul hA1 hA1 ha hA0
            have h_qa := mul_le_mul hA2 hA1 ha hA0
            have h_pa := mul_le_mul_of_nonneg_left hA1 hp
            have h_q2 := mul_le_mul hA2 hA2 hq hA0
            have h_pq := mul_le_mul_of_nonneg_left hA2 hp
            have hpp := sq_nonneg (lam * M)
            have hpA := mul_nonneg hp hA0
            have hAA := mul_nonneg hA0 hA0
            linarith
          have hTa : ∀ M L d X : ℝ, 0 ≤ M → 0 ≤ L → 0 ≤ d → d ^ 2 ≤ 16 * X ^ 2 →
              (2 * M + L * d) * d ≤ 4 * (M ^ 2 + 4 * (L + 2) * X ^ 2) := by
            intro M L d X hM hL hd h
            linear_combination sq_nonneg (M - d) + 3 * sq_nonneg M + h + mul_le_mul_of_nonneg_left h hL + 16 * sq_nonneg X
          have hlim : ∀ X Y Z : ℝ, 0 ≤ Z → (∀ s : ℝ, 0 < s → s < 1 → Y - s * Z ≤ X) → Y ≤ X := by
            intro X Y Z hZ h
            by_contra hc
            push Not at hc
            have h1 := h (min (1/2) ((Y - X) / (2 * (Z + 1)))) (lt_min (by norm_num) (div_pos (sub_pos.2 hc) (by linarith only [hZ])))
              (lt_of_le_of_lt (min_le_left _ _) (by norm_num))
            have h2 : min (1/2) ((Y - X) / (2 * (Z + 1))) * Z ≤ (Y - X) / (2 * (Z + 1)) * Z :=
              mul_le_mul_of_nonneg_right (min_le_right _ _) hZ
            have h3 : (Y - X) / (2 * (Z + 1)) * Z < Y - X := by
              rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
              linear_combination mul_pos (sub_pos.2 hc) (show 0 < Z + 2 by linarith only [hZ])
            linarith only [h1, h2, h3]
          have hsq : ∀ A B : E n, ∀ s : ℝ, ‖(1 - s) • A + s • B‖ ^ 2 =
              (1 - s) * ‖A‖ ^ 2 + s * ‖B‖ ^ 2 - (1 - s) * s * ‖A - B‖ ^ 2 := by
            intro A B s
            rw [norm_add_sq_real, norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left,
              real_inner_smul_right, mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
            ring
          have h2l : 0 < 2 * lam := mul_pos two_pos hlam
          have hKnn : 0 ≤ 1 / (2 * lam) + μ / 2 := add_nonneg (one_div_nonneg.2 h2l.le) (div_nonneg hμ zero_le_two)
          have hQ : ∀ (g : E n → ℝ) (c x : E n), StrongConvexOn P.D μ g → P.IsProxMin g c lam x →
              ∀ u ∈ P.D, g x + ‖x - c‖ ^ 2 / (2 * lam) + (1 / (2 * lam) + μ / 2) * ‖u - x‖ ^ 2 ≤
                g u + ‖u - c‖ ^ 2 / (2 * lam) := by
            intro g c x hg hx u hu
            apply hlim _ _ ((1 / (2 * lam) + μ / 2) * ‖u - x‖ ^ 2) (mul_nonneg hKnn (sq_nonneg _))
            intro s hs0 hs1
            have hw : (1 - s) • x + s • u ∈ P.D := hg.1 hx.1 hu (sub_nonneg.2 hs1.le) hs0.le (sub_add_cancel 1 s)
            have h1 := hx.2 _ hw
            have h2 := hg.2 hx.1 hu (sub_nonneg.2 hs1.le) hs0.le (sub_add_cancel 1 s)
            have h3 : (1 - s) • x + s • u - c = (1 - s) • (x - c) + s • (u - c) := by
              simp only [smul_sub, sub_smul, one_smul]; abel
            rw [h3, hsq] at h1
            have h4 : x - c - (u - c) = x - u := by abel
            rw [h4] at h1
            have h5 : ‖x - u‖ = ‖u - x‖ := norm_sub_rev _ _
            rw [h5] at h1 h2
            simp only [smul_eq_mul] at h2
            have key : s * (g x + ‖x - c‖ ^ 2 / (2 * lam)) ≤
                s * (g u + ‖u - c‖ ^ 2 / (2 * lam) - (1 - s) * ((1 / (2 * lam) + μ / 2) * ‖u - x‖ ^ 2)) := by
              have e1 : ((1 - s) * ‖x - c‖ ^ 2 + s * ‖u - c‖ ^ 2 - (1 - s) * s * ‖u - x‖ ^ 2) / (2 * lam)
                = (1 - s) * (‖x - c‖ ^ 2 / (2 * lam)) + s * (‖u - c‖ ^ 2 / (2 * lam)) - (1 - s) * s * (1 / (2 * lam) * ‖u - x‖ ^ 2) := by
                field_simp
              rw [e1] at h1
              linear_combination h1 + h2
            linear_combination le_of_mul_le_mul_left key hs0
          obtain ⟨hS, hlamlo, hlamhi⟩ := hinterval
          set S := Mf ^ 2 + ε * Lf with hSdef
          set τ := tau38 μ lam ε Mf Lf with hτdef
          set d0 := ‖x0 - x0s‖ with hd0
          set tb := tbar Mbar Lbar lam d0 with htb
          set θ := 1 + lam * μ with hθ
          have hθ1 : 1 ≤ θ := by have := mul_nonneg hlam.le hμ; linarith only [this, hθ]
          have hτeq : τ = 8 * lam * S / (8 * lam * S + θ * ε) := by
            rw [hτdef, tau38, ← hSdef, ← hθ]; field_simp
          have hθp : 0 < θ := lt_of_lt_of_le one_pos hθ1
          have hθε : 0 < θ * ε := mul_pos hθp hε
          have h8 : 0 < 8 * lam * S := mul_pos (mul_pos (by norm_num) hlam) hS
          have hden : 0 < 8 * lam * S + θ * ε := add_pos h8 hθε
          have hτ0 : 0 < τ := by rw [hτeq]; exact div_pos h8 hden
          have hτ1 : τ < 1 := by rw [hτeq, div_lt_one hden]; linarith only [hθε]
          have h1τ : 1 - τ = θ * ε / (8 * lam * S + θ * ε) := by rw [hτeq]; field_simp; ring
          -- τ K = (1-τ) 4 S / ε with K = θ/(2 lam)
          have hτK : τ * (θ / (2 * lam)) = (1 - τ) * (4 * S / ε) := by
            rw [h1τ, hτeq]; field_simp; ring
          have hKθ : 1 / (2 * lam) + μ / 2 = θ / (2 * lam) := by rw [hθ]; field_simp
          set A := 1 + 8 * lamMu μ lam * S / ε with hAd
          have hAτ : (1 - τ) * A = 1 := by
            rw [h1τ, hAd, lamMu]; field_simp; ring
          have hd0pos : 0 < d0 := by
            rcases (norm_nonneg (x0 - x0s)).lt_or_eq with h | h
            · exact h
            · exfalso; rw [← hd0] at h; rw [← h] at hlamhi
              have e : C * (0:ℝ) ^ 2 / ε = 0 := by simp
              rw [e] at hlamhi; exact absurd hlam (not_lt.2 hlamhi)
          obtain ⟨hMb, hLb, hA3b, -⟩ := hmin
          have htbpos : 0 < tb := by
            rw [htb, tbar]
            have : 0 < max 1 (2 * lam * Lbar) * d0 + lam * Mbar :=
              add_pos_of_pos_of_nonneg (mul_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) hd0pos) (mul_nonneg hlam.le hMb)
            exact add_pos_of_nonneg_of_pos (sq_nonneg _)
              (mul_pos (mul_pos four_pos (by linarith only [hLb])) (pow_pos this 2))
          have hA1' : 1 ≤ A := by
            have h1 : 0 ≤ lamMu μ lam := div_nonneg hlam.le (hθ ▸ hθp.le)
            have h2 : 0 ≤ 8 * lamMu μ lam * S / ε :=
              div_nonneg (mul_nonneg (mul_nonneg (by norm_num) h1) hS.le) hε.le
            linarith only [h2, hAd]
          clear_value A θ tb d0 τ S
          obtain ⟨hr0, hy0, hrs⟩ := hrun
          have hstep : ∀ j : ℕ, (R.t P lam j ≤ ε / 2 → R.xc (j+1) = R.x j ∧ StrongConvexOn P.D μ (R.Γ (j+1)) ∧
                ∀ v ∈ P.D, P.ellf v (R.x j) + P.h v ≤ R.Γ (j+1) v ∧ R.Γ (j+1) v ≤ P.φ v) ∧
              (ε / 2 < R.t P lam j → R.xc (j+1) = R.xc j ∧
                P.BU μ lam τ (R.xc j) (R.x j) (R.Γ j) (R.Γ (j+1))) ∧
              P.IsProxMin (R.Γ (j+1)) (R.xc (j+1)) lam (R.x (j+1)) ∧
              (∃ i ≤ j + 1, R.y (j+1) = R.x i) ∧ (∀ i ≤ j + 1, P.φ (R.y (j+1)) ≤ P.φ (R.x i)) := by
            intro j
            obtain ⟨h1, h2, h3, h4, h5⟩ := hrs (j+1) (by omega)
            simp only [Nat.add_sub_cancel] at h1 h2
            exact ⟨fun h => ⟨(h1 h).1, (h1 h).2.1.1, (h1 h).2.2⟩, h2, h3, h4, h5⟩
          have hΓ : ∀ j : ℕ, StrongConvexOn P.D μ (R.Γ (j+1)) ∧ ∀ v ∈ P.D, R.Γ (j+1) v ≤ P.φ v := by
            intro j
            rcases le_or_gt (R.t P lam j) (ε / 2) with h | h
            · obtain ⟨-, h2, h3⟩ := (hstep j).1 h
              exact ⟨h2, fun v hv => (h3 v hv).2⟩
            · obtain ⟨-, hb⟩ := (hstep j).2.1 h
              exact ⟨hb.1.1, hb.2.1⟩
          have hxD : ∀ j, R.x j ∈ P.D := by
            intro j; cases j with
            | zero => rw [hr0]; exact hx0
            | succ j => exact ((hstep j).2.2.1).1
          have hyx : ∀ j, P.φ (R.y j) ≤ P.φ (R.x j) := by
            intro j; cases j with
            | zero => rw [hr0, hy0]
            | succ j => exact (hstep j).2.2.2.2 _ le_rfl
          have hyy : ∀ j, P.φ (R.y (j+1)) ≤ P.φ (R.y j) := by
            intro j; cases j with
            | zero => have := (hstep 0).2.2.2.2 0 (by omega); rw [hr0] at this; rw [hy0]; exact this
            | succ j =>
              obtain ⟨i, hi, hyi⟩ := (hstep j).2.2.2.1
              rw [hyi]; exact (hstep (j+1)).2.2.2.2 i (by omega)
          have ht0 : R.t P lam 0 = 0 := by simp [Run.t]
          have ht : ∀ j, R.t P lam (j+1) = P.φ (R.y (j+1)) - R.m lam (j+1) := by
            intro j; simp [Run.t]
          have hA : ∀ j, ∀ v ∈ P.D, R.m lam (j+1) + θ / (2 * lam) * ‖v - R.x (j+1)‖ ^ 2 ≤
              P.φ v + ‖v - R.xc (j+1)‖ ^ 2 / (2 * lam) := by
            intro j v hv
            have := hQ _ _ _ (hΓ j).1 (hstep j).2.2.1 v hv
            have h2 := (hΓ j).2 v hv
            rw [hKθ] at this
            simp only [Run.m]; linarith only [this, h2]
          have hgrad : ∀ M L : ℝ, P.A3 M L → ∀ x ∈ P.D, ∀ y ∈ P.D,
              P.f x - P.ellf x y ≤ (2 * M + L * ‖x - y‖) * ‖x - y‖ := by
            intro M L hML x hx y hy
            have h1 := hA1.2.2.2 x hx y hy
            simp only [Instance.ellf] at h1 ⊢
            have h2 : (inner ℝ (P.f' x - P.f' y) (x - y)) ≤ ‖P.f' x - P.f' y‖ * ‖x - y‖ := real_inner_le_norm _ _
            have h3 := hML x hx y hy
            have h4 : (inner ℝ (P.f' x - P.f' y) (x - y)) = (inner ℝ (P.f' x) (x - y)) - (inner ℝ (P.f' y) (x - y)) := inner_sub_left _ _ _
            have h5 : (inner ℝ (P.f' x) (y - x)) = - (inner ℝ (P.f' x) (x - y)) := by
              rw [← inner_neg_right, neg_sub]
            have h6 := mul_le_mul_of_nonneg_right h3 (norm_nonneg (x - y))
            linarith only [h1, h2, h4, h5, h6]
          have hN : ∀ j, ε / 2 < R.t P lam j → R.t P lam (j+1) - ε / 4 ≤ τ * (R.t P lam j - ε / 4) := by
            intro j hj
            have hj1 : 1 ≤ j := by
              rcases Nat.eq_zero_or_pos j with h | h
              · rw [h, ht0] at hj; linarith only [hj, hε]
              · exact h
            obtain ⟨hxc, hBU⟩ := (hstep j).2.1 hj
            obtain ⟨-, -, Gb, hGsc, hGeq, hGpm, hGlow⟩ := hBU
            have hQ1 := hQ Gb (R.xc j) (R.x j) hGsc hGpm (R.x (j+1)) (hxD _)
            rw [hKθ] at hQ1
            have hl := hGlow (R.x (j+1)) (hxD _)
            have hg := hgrad Mf Lf hA3 (R.x (j+1)) (hxD _) (R.x j) (hxD _)
            obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
            have htj := ht j'
            have htj1 := ht (j'+1)
            have hy1 := hyy (j'+1)
            have hy2 := hyx (j'+1+1)
            simp only [Run.m] at htj htj1
            rw [hxc] at htj1
            simp only [Instance.φ] at hy2
            set d := ‖R.x (j'+1+1) - R.x (j'+1)‖
            set c := R.xc (j'+1)
            have hd : 0 ≤ d := norm_nonneg _
            have key := hkeyN Mf Lf d S ε hε hLf hd hSdef
            have k2 : τ * (θ / (2 * lam) * d ^ 2) = (1 - τ) * (4 * S / ε * d ^ 2) := by
              rw [← mul_assoc, hτK]; ring
            have hcpos : 0 ≤ ‖R.x (j'+1+1) - c‖ ^ 2 / (2 * lam) := div_nonneg (sq_nonneg _) h2l.le
            have hτ1' : 0 ≤ 1 - τ := sub_nonneg.2 hτ1.le
            have k3 := mul_le_mul_of_nonneg_left key hτ1'
            have k4 := mul_le_mul_of_nonneg_left hQ1 hτ0.le
            have k5 := mul_le_mul_of_nonneg_left hy1 hτ0.le
            have k6 := mul_le_mul_of_nonneg_left hy2 hτ1'
            have k7 := mul_le_mul_of_nonneg_left hg hτ1'
            have k8 := mul_nonneg hτ1' hcpos
            simp only [Instance.φ, Instance.ellf] at hl hg k6 k7 htj htj1 hy1 k5 ⊢
            rw [htj1, htj]
            linear_combination hl + k4 + k5 + k6 + k7 + k3 + k8 - τ * hGeq - k2
          have hhsub : ∀ v ∈ P.D, inner ℝ (P.f' x0s) (x0s - v) - 2 * Mbar * ‖v - x0s‖ ≤ P.h v - P.h x0s := by
            intro v hv
            have hu := hx0s.1.1
            apply hlim _ _ (Lbar * ‖v - x0s‖ ^ 2) (mul_nonneg hLb (sq_nonneg _))
            intro s hs0 hs1
            have hw : (1 - s) • x0s + s • v ∈ P.D := hA1.2.2.1.1.1 hu hv (sub_nonneg.2 hs1.le) hs0.le (sub_add_cancel 1 s)
            have hconv := hA1.2.2.1.1.2 hu hv (sub_nonneg.2 hs1.le) hs0.le (sub_add_cancel 1 s)
            simp only [smul_eq_mul] at hconv
            have hopt := hx0s.1.2 _ hw
            have hsg := hA1.2.2.2 _ hw x0s hu
            simp only [Instance.ellf, Instance.φ] at hsg hopt
            set w := (1 - s) • x0s + s • v
            have e1 : x0s - w = s • (x0s - v) := by
              simp only [w, smul_sub, sub_smul, one_smul]; abel
            have e2 : w - x0s = s • (v - x0s) := by
              simp only [w, smul_sub, sub_smul, one_smul]; abel
            rw [e1, inner_smul_right] at hsg
            have hA3w := hA3b w hw x0s hu
            rw [e2, norm_smul, Real.norm_eq_abs, abs_of_pos hs0] at hA3w
            have hin : inner ℝ (P.f' x0s - P.f' w) (x0s - v) ≤ ‖P.f' x0s - P.f' w‖ * ‖x0s - v‖ := real_inner_le_norm _ _
            rw [inner_sub_left, norm_sub_rev x0s v, norm_sub_rev (P.f' x0s)] at hin
            have hm := mul_le_mul_of_nonneg_right hA3w (norm_nonneg (v - x0s))
            have hmu : 0 ≤ (1 - s) * s * (μ / 2 * ‖x0s - v‖ ^ 2) := by
              exact mul_nonneg (mul_nonneg (sub_nonneg.2 hs1.le) hs0.le) (mul_nonneg (div_nonneg hμ zero_le_two) (sq_nonneg _))
            -- s (h v - h u) ≥ s ⟪f' w, u - v⟫
            have key : s * (inner ℝ (P.f' w) (x0s - v)) ≤ s * (P.h v - P.h x0s) := by
              linear_combination hsg + hopt + hconv + hmu
            have key2 := le_of_mul_le_mul_left key hs0
            linear_combination key2 + hin + hm
          have hT : ∀ g, R.t P lam g ≤ ε / 2 → ‖R.x g - x0s‖ ≤ d0 → R.t P lam (g+1) ≤ 4 * tb := by
            intro g hg ha
            have hu := hx0s.1.1
            obtain ⟨hxc, hsc, hmod⟩ := (hstep g).1 hg
            have hpm := (hstep g).2.2.1
            rw [hxc] at hpm
            have hQ2 := hQ _ _ _ hsc hpm x0s hu
            rw [hKθ] at hQ2
            have hup := (hmod x0s hu).2
            have hlow := (hmod (R.x (g+1)) (hxD _)).1
            have hh := hhsub (R.x (g+1)) (hxD _)
            have hg1 := hgrad Mbar Lbar hA3b x0s hu (R.x g) (hxD g)
            have hg2 := hgrad Mbar Lbar hA3b (R.x (g+1)) (hxD _) (R.x g) (hxD g)
            have hA3' := hA3b x0s hu (R.x g) (hxD g)
            have hin : inner ℝ (P.f' x0s - P.f' (R.x g)) (R.x (g+1) - x0s) ≤
                ‖P.f' x0s - P.f' (R.x g)‖ * ‖R.x (g+1) - x0s‖ := real_inner_le_norm _ _
            rw [inner_sub_left] at hin
            have i1 : inner ℝ (P.f' (R.x g)) (R.x (g+1) - R.x g) = inner ℝ (P.f' (R.x g)) (R.x (g+1) - x0s) +
                inner ℝ (P.f' (R.x g)) (x0s - R.x g) := by
              rw [← inner_add_right]; congr 1; abel
            have i2 : inner ℝ (P.f' x0s) (x0s - R.x (g+1)) = - inner ℝ (P.f' x0s) (R.x (g+1) - x0s) := by
              rw [← inner_neg_right, neg_sub]
            have hm := mul_le_mul_of_nonneg_right hA3' (norm_nonneg (R.x (g+1) - x0s))
            have htg := ht g
            simp only [Run.m, Instance.φ] at htg
            rw [hxc] at htg
            have hyx' := hyx (g+1)
            simp only [Instance.φ] at hyx'
            rw [norm_sub_rev x0s (R.x g)] at hg1 hQ2 hm
            rw [norm_sub_rev x0s (R.x (g+1))] at hQ2
            simp only [Instance.ellf, Instance.φ] at hg1 hg2 hlow hup
            have hb : 0 ≤ ‖R.x (g+1) - x0s‖ := norm_nonneg _
            have hd : 0 ≤ ‖R.x (g+1) - R.x g‖ := norm_nonneg _
            have ha0 : 0 ≤ ‖R.x g - x0s‖ := norm_nonneg _
            have hθb : ‖R.x (g+1) - x0s‖ ^ 2 / (2 * lam) ≤ θ / (2 * lam) * ‖R.x (g+1) - x0s‖ ^ 2 := by
              rw [div_mul_eq_mul_div]
              exact div_le_div_of_nonneg_right (le_mul_of_one_le_left (sq_nonneg _) hθ1) h2l.le
            have E0 : ‖R.x (g+1) - R.x g‖ ^ 2 / (2 * lam) + ‖R.x (g+1) - x0s‖ ^ 2 / (2 * lam) ≤ ‖R.x g - x0s‖ ^ 2 / (2 * lam) + (2 * Mbar + Lbar * ‖R.x g - x0s‖) * ‖R.x g - x0s‖ +
                (4 * Mbar + Lbar * ‖R.x g - x0s‖) * ‖R.x (g+1) - x0s‖ := by
              linear_combination hQ2 + hup + hlow + hh + hg1 + hin + hm - i1 - i2 + hθb
            have E1 : ‖R.x (g+1) - R.x g‖ ^ 2 + ‖R.x (g+1) - x0s‖ ^ 2 ≤ ‖R.x g - x0s‖ ^ 2 + 2 * lam * (2 * Mbar + Lbar * ‖R.x g - x0s‖) * ‖R.x g - x0s‖ +
                2 * lam * (4 * Mbar + Lbar * ‖R.x g - x0s‖) * ‖R.x (g+1) - x0s‖ := by
              have := mul_le_mul_of_nonneg_left E0 h2l.le
              have k1 : 2 * lam * (‖R.x (g+1) - R.x g‖ ^ 2 / (2 * lam)) = ‖R.x (g+1) - R.x g‖ ^ 2 := mul_div_cancel₀ _ h2l.ne'
              have k2 : 2 * lam * (‖R.x (g+1) - x0s‖ ^ 2 / (2 * lam)) = ‖R.x (g+1) - x0s‖ ^ 2 := mul_div_cancel₀ _ h2l.ne'
              have k3 : 2 * lam * (‖R.x g - x0s‖ ^ 2 / (2 * lam)) = ‖R.x g - x0s‖ ^ 2 := mul_div_cancel₀ _ h2l.ne'
              linear_combination this - k1 - k2 + k3
            have hdd := hDb ‖R.x g - x0s‖ ‖R.x (g+1) - x0s‖ ‖R.x (g+1) - R.x g‖ d0 lam Mbar Lbar ha0 ha hlam.le hMb hLb hb E1
            have hfin := hTa Mbar Lbar ‖R.x (g+1) - R.x g‖ _ hMb hLb hd hdd
            have hdpos : 0 ≤ ‖R.x (g+1) - R.x g‖ ^ 2 / (2 * lam) := div_nonneg (sq_nonneg _) h2l.le
            rw [htb, tbar, htg]
            linarith only [hfin, hg2, hlow, hyx', hdpos]
          obtain ⟨Lg, hLg⟩ : ∃ Lg : ℝ, Lg = A * max (Real.log (16 * tb / ε)) 0 := ⟨_, rfl⟩
          have hA0 : 0 < A := lt_of_lt_of_le one_pos hA1'
          have hLg0 : 0 ≤ Lg := by rw [hLg]; exact mul_nonneg hA0.le (le_max_right _ _)
          have hgap : ∀ m : ℕ, ε / 4 < τ ^ m * (4 * tb - ε / 4) → (m : ℝ) < Lg := by
            intro m hm
            have hτe : τ ≤ Real.exp (-(1 / A)) := by
              have h1 := Real.add_one_le_exp (-(1 / A))
              have h2 : 1 - τ = 1 / A := eq_one_div_of_mul_eq_one_left hAτ
              linarith only [h1, h2]
            have hτm : τ ^ m ≤ Real.exp (-(m / A)) := by
              calc τ ^ m ≤ Real.exp (-(1 / A)) ^ m := pow_le_pow_left₀ hτ0.le hτe m
                _ = Real.exp (-(m / A)) := by rw [← Real.exp_nat_mul]; congr 1; ring
            have htb16 : 0 < 16 * tb := mul_pos (by norm_num) htbpos
            have h3 : ε < Real.exp (-(m / A)) * (16 * tb) := by
              have h1 := mul_le_mul_of_nonneg_right hτm htb16.le
              have h4 := mul_nonneg (pow_nonneg hτ0.le m) hε.le
              linarith only [h1, h4, hm]
            have h5 : ε / (16 * tb) < Real.exp (-(m / A)) := (div_lt_iff₀ htb16).2 h3
            have h6 := Real.log_lt_log (div_pos hε htb16) h5
            rw [Real.log_exp, ← inv_div, Real.log_inv] at h6
            have h7 : (m : ℝ) / A < max (Real.log (16 * tb / ε)) 0 :=
              lt_of_lt_of_le (neg_lt_neg_iff.1 h6) (le_max_left _ _)
            rw [div_lt_iff₀ hA0] at h7
            rw [hLg, mul_comm]; exact h7
          have hInv : ∀ j : ℕ, (∀ i ≤ j, ε < P.φ (R.y i) - P.φ x0s) → ∃ s ≤ j, ∃ k : ℕ,
              R.t P lam s ≤ ε / 2 ∧ ‖R.x s - x0s‖ ^ 2 ≤ d0 ^ 2 - k * lam * ε ∧
              (0 < μ → θ ^ k * (‖R.x s - x0s‖ ^ 2 + ε / μ) ≤ d0 ^ 2 + ε / μ) ∧
              (s : ℝ) ≤ k * (Lg + 2) ∧
              (s < j → R.xc j = R.x s ∧ ε / 2 < R.t P lam j ∧
                R.t P lam j - ε / 4 ≤ τ ^ (j - s - 1) * (4 * tb - ε / 4)) := by
            intro j
            induction j with
            | zero =>
              intro _
              refine ⟨0, le_rfl, 0, by rw [ht0]; exact (half_pos hε).le, ?_, ?_, by simp, fun h => absurd h (lt_irrefl 0)⟩
              · rw [hr0, ← hd0]; simp
              · intro _; rw [hr0, ← hd0]; simp
            | succ j ih =>
              intro hf
              obtain ⟨s, hsj, k, hts, hDs, hθs, hsk, hnull⟩ := ih (fun i hi => hf i (by omega))
              have hDs0 : ‖R.x s - x0s‖ ≤ d0 := by
                have : ‖R.x s - x0s‖ ^ 2 ≤ d0 ^ 2 := by
                  have h0 : (0:ℝ) ≤ k * lam * ε := mul_nonneg (mul_nonneg (Nat.cast_nonneg k) hlam.le) hε.le
                  linarith only [h0, hDs]
                exact (pow_le_pow_iff_left₀ (norm_nonneg _) hd0pos.le (by norm_num)).1 this
              have hxcj : R.xc (j+1) = R.x s := by
                rcases Nat.lt_or_ge s j with h | h
                · obtain ⟨h1, h2, -⟩ := hnull h
                  rw [← h1]; exact ((hstep j).2.1 h2).1
                · have : s = j := by omega
                  subst this; exact ((hstep s).1 hts).1
              have hlen : ((j + 1 : ℕ) : ℝ) - s ≤ Lg + 2 := by
                rcases Nat.lt_or_ge s j with h | h
                · obtain ⟨-, h2, h3⟩ := hnull h
                  have := hgap (j - s - 1) (by linarith only [h2, h3])
                  have e : ((j - s - 1 : ℕ) : ℝ) = (j:ℝ) - s - 1 := by
                    rw [Nat.cast_sub (Nat.sub_pos_of_lt h), Nat.cast_sub hsj, Nat.cast_one]
                  rw [e] at this; push_cast; linarith only [this]
                · have : s = j := by omega
                  subst this; push_cast; linarith only [hLg0]
              rcases le_or_gt (R.t P lam (j+1)) (ε / 2) with hser | hnul
              · -- new serious index
                refine ⟨j+1, le_rfl, k+1, hser, ?_⟩
                have hAj := hA j x0s hx0s.1.1
                have htj := ht j
                have hfj := hf (j+1) le_rfl
                rw [hxcj, norm_sub_rev x0s (R.x (j+1)), norm_sub_rev x0s (R.x s)] at hAj
                have hopt : P.φ x0s ≤ P.φ x0s := le_rfl
                have key : θ * ‖R.x (j+1) - x0s‖ ^ 2 ≤ ‖R.x s - x0s‖ ^ 2 - lam * ε := by
                  have h1 : θ / (2 * lam) * ‖R.x (j+1) - x0s‖ ^ 2 ≤ ‖R.x s - x0s‖ ^ 2 / (2 * lam) - ε / 2 := by
                    linarith only [hAj, htj, hfj, hser]
                  have h2 := mul_le_mul_of_nonneg_left h1 h2l.le
                  have e1 : 2 * lam * (θ / (2 * lam) * ‖R.x (j+1) - x0s‖ ^ 2) = θ * ‖R.x (j+1) - x0s‖ ^ 2 := by
                    rw [← mul_assoc, mul_div_cancel₀ _ h2l.ne']
                  have e2 : 2 * lam * (‖R.x s - x0s‖ ^ 2 / (2 * lam)) = ‖R.x s - x0s‖ ^ 2 := mul_div_cancel₀ _ h2l.ne'
                  linarith only [h2, e1, e2]
                have hle : ‖R.x (j+1) - x0s‖ ^ 2 ≤ θ * ‖R.x (j+1) - x0s‖ ^ 2 :=
                  le_mul_of_one_le_left (sq_nonneg _) hθ1
                refine ⟨by push_cast; linarith only [key, hle, hDs], ?_, ?_, fun h => absurd h (lt_irrefl _)⟩
                · intro hμ0
                  have := hθs hμ0
                  have e : θ * (ε / μ) = ε / μ + lam * ε := by rw [hθ]; field_simp
                  have h0 : 0 ≤ θ ^ k := pow_nonneg hθp.le k
                  calc θ ^ (k+1) * (‖R.x (j+1) - x0s‖ ^ 2 + ε / μ)
                      = θ ^ k * (θ * ‖R.x (j+1) - x0s‖ ^ 2 + θ * (ε / μ)) := by ring
                    _ ≤ θ ^ k * (‖R.x s - x0s‖ ^ 2 + ε / μ) := by
                        exact mul_le_mul_of_nonneg_left (by linarith only [key, e]) h0
                    _ ≤ _ := this
                · push_cast at hlen ⊢; linarith only [hlen, hsk]
              · refine ⟨s, by omega, k, hts, hDs, hθs, hsk, fun _ => ⟨hxcj, hnul, ?_⟩⟩
                rcases Nat.lt_or_ge s j with h | h
                · obtain ⟨-, h2, h3⟩ := hnull h
                  have := hN j h2
                  have e : j + 1 - s - 1 = (j - s - 1) + 1 := by omega
                  rw [e, pow_succ]
                  have hp := mul_le_mul_of_nonneg_left h3 hτ0.le
                  linarith only [hp, this]
                · have : s = j := by omega
                  subst this
                  have := hT s hts hDs0
                  have e : s + 1 - s - 1 = 0 := by omega
                  rw [e, pow_zero, one_mul]; exact sub_le_sub_right this _
          have hrate0 : 0 ≤ rate μ ε S (d0 ^ 2) := by
            unfold rate
            have h1 : 0 ≤ S * d0 ^ 2 / ε ^ 2 := div_nonneg (mul_nonneg hS.le (sq_nonneg _)) (sq_nonneg _)
            by_cases h : μ = 0
            · rw [if_pos h]; exact h1
            · rw [if_neg h]
              refine le_min h1 (mul_nonneg (add_nonneg (div_nonneg hS.le (mul_nonneg hμ hε.le)) zero_le_one) (Real.log_nonneg ?_))
              exact le_add_of_nonneg_right (div_nonneg (mul_nonneg hμ (sq_nonneg _)) hε.le)
          have hlog0 : 0 ≤ logFactor tb ε := by
            unfold logFactor; split_ifs
            · exact le_rfl
            · exact le_max_right _ _
          have hK0 : 0 < K31 C := by
            unfold K31
            exact mul_pos (by norm_num) (by linarith only [le_max_right C 1])
          have hb0 : 0 ≤ K31 C * (logFactor tb ε + 1) * (rate μ ε S (d0 ^ 2) + 1) :=
            mul_nonneg (mul_nonneg hK0.le (add_nonneg hlog0 zero_le_one)) (add_nonneg hrate0 zero_le_one)
          by_contra hno
          unfold Obtains at hno
          push Not at hno
          obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = ⌊K31 C * (logFactor tb ε + 1) * (rate μ ε S (d0 ^ 2) + 1)⌋₊ := ⟨_, rfl⟩
          have hN1 : K31 C * (logFactor tb ε + 1) * (rate μ ε S (d0 ^ 2) + 1) < (N : ℝ) + 1 := by
            rw [hNdef]; exact Nat.lt_floor_add_one _
          have hfail : ∀ i ≤ N, ε < P.φ (R.y i) - P.φ x0s := fun i hi =>
            hno i (le_trans (Nat.cast_le.2 (hNdef ▸ hi)) (Nat.floor_le hb0))
          obtain ⟨s, hsN, k, hts, hDs, hθs, hsk, hnull⟩ := hInv N hfail
          have hlenN : (N : ℝ) + 1 ≤ s + (Lg + 2) := by
            rcases Nat.lt_or_ge s N with h | h
            · obtain ⟨-, h2, h3⟩ := hnull h
              have := hgap (N - s - 1) (by linarith only [h2, h3])
              have e : ((N - s - 1 : ℕ) : ℝ) = (N:ℝ) - s - 1 := by
                rw [Nat.cast_sub (Nat.sub_pos_of_lt h), Nat.cast_sub hsN, Nat.cast_one]
              rw [e] at this; linarith only [this]
            · have : s = N := by omega
              subst this; linarith only [hLg0]
          have hkd : (k : ℝ) * lam * ε ≤ d0 ^ 2 := by linarith only [hDs, sq_nonneg ‖R.x s - x0s‖]
          have hkμ : 0 < μ → θ ^ k * (ε / μ) ≤ d0 ^ 2 + ε / μ := by
            intro hμ0
            have := hθs hμ0
            have h0 : 0 ≤ θ ^ k * ‖R.x s - x0s‖ ^ 2 := mul_nonneg (pow_nonneg hθp.le k) (sq_nonneg _)
            rw [mul_add] at this; linarith only [this, h0]
          have hmain := hM S d0 tb θ A Lg k hS hlamlo hlamhi (by linarith only [hθ]) hθ1 hAd hA1' hd0pos htbpos hLg hrate0 hlog0 hkd hkμ
          linarith only [hN1, hmain, hlenN, hsk]
