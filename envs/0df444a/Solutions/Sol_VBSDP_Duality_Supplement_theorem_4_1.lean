-- Prove2me | solution 1 for VBSDP.Duality.Supplement.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:37:10.44806+00:00
-- url     : https://prove2.me/submissions/cc8cdfe3-eca8-42fd-909d-490285da53e5

import Mathlib
import Definitions.Def_VBSDP_Duality_Supplement_IsAnalyticCenter
import Definitions.Def_VBSDP_Duality_Supplement_IsNewtonRun

open VBSDP
open VBSDP.Duality
open VBSDP.Duality.Supplement

theorem solution {m n : ℕ}
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hF₀ : F₀.IsHermitian) (hF : ∀ i, (F i).IsHermitian)
    (hbdd : Bornology.IsBounded {x : Fin m → ℝ | (VBSDP.Duality.lmi F₀ F x).PosDef})
    (xk : ℕ → Fin m → ℝ) (hrun : IsNewtonRun F₀ F xk)
    (xs : Fin m → ℝ) (hxs : IsAnalyticCenter F₀ F xs)
    (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε ≤ 0.5) (k : ℕ)
    (hk : 11 * (barrier F₀ F (xk 0) - barrier F₀ F xs) + Real.logb 2 (Real.logb 2 (1 / ε)) ≤ k) :
    barrier F₀ F (xk k) - barrier F₀ F xs ≤ ε := by
      open Matrix in
      classical
      have hlin0 : ∀ c q : ℝ, (∀ t : ℝ, 0 ≤ t * c + t ^ 2 * q) → c = 0 := by
        clear * -
        intro c q h
        have hs : 0 < |q| + 1 := by linarith [abs_nonneg q]
        have h1 := h (-c / (|q| + 1))
        have e : -c / (|q| + 1) * c + (-c / (|q| + 1)) ^ 2 * q =
            c ^ 2 / (|q| + 1) * (q / (|q| + 1) - 1) := by field_simp; ring
        rw [e] at h1
        have h2 : q / (|q| + 1) - 1 < 0 := by
          rw [sub_neg, div_lt_one hs]; linarith [le_abs_self q]
        have h3 : c ^ 2 / (|q| + 1) ≤ 0 := by
          by_contra hc; push Not at hc; nlinarith
        have h4 : c ^ 2 ≤ 0 := by
          have := div_mul_cancel₀ (c ^ 2) hs.ne'
          nlinarith
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm h4 (sq_nonneg _))
      have hK : AntitoneOn (fun a : ℝ => (a - Real.log (1 + a)) / a ^ 2) (Set.Ioi 0) := by
        clear * -
        have hlogb : ∀ x : ℝ, 0 ≤ x → Real.log (1 + x) ≤ (x ^ 2 + 2 * x) / (2 * (1 + x)) := by
          intro x hx
          have h1 : 0 < 1 + x := by linarith
          have h2 : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith)
          have h3 := Real.self_le_sinh_iff.2 h2
          rw [Real.sinh_log h1] at h3
          have e : ((1 + x) - (1 + x)⁻¹) / 2 = (x ^ 2 + 2 * x) / (2 * (1 + x)) := by
            field_simp; ring
          linarith
        have hd : ∀ x ∈ Set.Ioi (0:ℝ), HasDerivAt (fun a : ℝ => (a - Real.log (1 + a)) / a ^ 2)
            (((1 - 1 / (1 + x)) * x ^ 2 - (x - Real.log (1 + x)) * (2 * x)) / (x ^ 2) ^ 2) x := by
          intro x hx
          have hx0 : (0:ℝ) < x := hx
          have h1 : (1 + x) ≠ 0 := by linarith
          have hl : HasDerivAt (fun a : ℝ => Real.log (1 + a)) (1 / (1 + x)) x := by
            have := ((hasDerivAt_id x).const_add 1).log h1
            simpa using this
          have h_num : HasDerivAt (fun a : ℝ => a - Real.log (1 + a)) (1 - 1 / (1 + x)) x :=
            (hasDerivAt_id' x).sub hl
          have h_den : HasDerivAt (fun a : ℝ => a ^ 2) (2 * x) x := by
            simpa using hasDerivAt_pow 2 x
          exact h_num.div h_den (by positivity)
        apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
        · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
        · intro x hx; rw [interior_Ioi] at hx; exact (hd x hx).differentiableAt.differentiableWithinAt
        · intro x hx
          rw [interior_Ioi] at hx
          rw [(hd x hx).deriv]
          have hx0 : (0:ℝ) < x := hx
          apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
          have hb := hlogb x hx0.le
          have h1 : 0 < 1 + x := by linarith
          have e : (1 - 1 / (1 + x)) * x ^ 2 - (x - Real.log (1 + x)) * (2 * x) =
              2 * x * (Real.log (1 + x) - (x ^ 2 + 2 * x) / (2 * (1 + x))) := by
            field_simp; ring
          rw [e]
          exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
      have hK2 : AntitoneOn (fun a : ℝ => (a - Real.log (1 + a)) / a ^ 2) (Set.Ioo (-1) 0) := by
        clear * -
        have hlogb : ∀ x : ℝ, -1 < x → x ≤ 0 → (x ^ 2 + 2 * x) / (2 * (1 + x)) ≤ Real.log (1 + x) := by
          intro x hx1 hx
          have h1 : 0 < 1 + x := by linarith
          have h2 : Real.log (1 + x) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
          have h3 := Real.sinh_le_self_iff.2 h2
          rw [Real.sinh_log h1] at h3
          have e : ((1 + x) - (1 + x)⁻¹) / 2 = (x ^ 2 + 2 * x) / (2 * (1 + x)) := by
            field_simp; ring
          linarith
        have hd : ∀ x ∈ Set.Ioo (-1:ℝ) 0, HasDerivAt (fun a : ℝ => (a - Real.log (1 + a)) / a ^ 2)
            (((1 - 1 / (1 + x)) * x ^ 2 - (x - Real.log (1 + x)) * (2 * x)) / (x ^ 2) ^ 2) x := by
          intro x hx
          have h1 : (1 + x) ≠ 0 := by linarith [hx.1]
          have hx0 : x ≠ 0 := by linarith [hx.2]
          have hl : HasDerivAt (fun a : ℝ => Real.log (1 + a)) (1 / (1 + x)) x := by
            have := ((hasDerivAt_id x).const_add 1).log h1
            simpa using this
          have h_num : HasDerivAt (fun a : ℝ => a - Real.log (1 + a)) (1 - 1 / (1 + x)) x :=
            (hasDerivAt_id' x).sub hl
          have h_den : HasDerivAt (fun a : ℝ => a ^ 2) (2 * x) x := by
            simpa using hasDerivAt_pow 2 x
          exact h_num.div h_den (by positivity)
        apply antitoneOn_of_deriv_nonpos (convex_Ioo (-1) 0)
        · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
        · intro x hx; rw [interior_Ioo] at hx; exact (hd x hx).differentiableAt.differentiableWithinAt
        · intro x hx
          rw [interior_Ioo] at hx
          rw [(hd x hx).deriv]
          have hx0 : x ≠ 0 := by linarith [hx.2]
          apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
          have hb := hlogb x hx.1 hx.2.le
          have h1 : 0 < 1 + x := by linarith [hx.1]
          have e : (1 - 1 / (1 + x)) * x ^ 2 - (x - Real.log (1 + x)) * (2 * x) =
              (-2 * x) * ((x ^ 2 + 2 * x) / (2 * (1 + x)) - Real.log (1 + x)) := by
            field_simp; ring
          rw [e]
          exact mul_nonpos_of_nonneg_of_nonpos (by linarith [hx.2]) (by linarith)
      have hsym : ∀ s : ℝ, 0 ≤ s → s < 1 → s - Real.log (1 + s) ≤ -s - Real.log (1 + -s) := by
        clear * -
        have hd : ∀ x ∈ Set.Ioo (-1:ℝ) 1, HasDerivAt
            (fun s : ℝ => Real.log (1 + s) - Real.log (1 + -s) - 2 * s)
            (1 / (1 + x) - (-1) / (1 + -x) - 2) x := by
          intro x hx
          have h1 : 1 + x ≠ 0 := by linarith [hx.1]
          have h2 : 1 + -x ≠ 0 := by linarith [hx.2]
          have a1 : HasDerivAt (fun a : ℝ => Real.log (1 + a)) (1 / (1 + x)) x := by
            simpa using ((hasDerivAt_id x).const_add 1).log h1
          have a2 : HasDerivAt (fun a : ℝ => Real.log (1 + -a)) ((-1) / (1 + -x)) x := by
            simpa using ((hasDerivAt_id x).neg.const_add 1).log h2
          have a3 : HasDerivAt (fun a : ℝ => 2 * a) 2 x := by
            simpa using (hasDerivAt_id x).const_mul 2
          exact (a1.sub a2).sub a3
        have hmono : MonotoneOn (fun s : ℝ => Real.log (1 + s) - Real.log (1 + -s) - 2 * s)
            (Set.Ico 0 1) := by
          apply monotoneOn_of_deriv_nonneg (convex_Ico 0 1)
          · intro x hx
            exact (hd x ⟨by linarith [hx.1], hx.2⟩).continuousAt.continuousWithinAt
          · intro x hx; rw [interior_Ico] at hx
            exact (hd x ⟨by linarith [hx.1], hx.2⟩).differentiableAt.differentiableWithinAt
          · intro x hx; rw [interior_Ico] at hx
            rw [(hd x ⟨by linarith [hx.1], hx.2⟩).deriv]
            have h1 : 0 < 1 + x := by linarith [hx.1]
            have h2 : 0 < 1 + -x := by linarith [hx.2]
            have e : 1 / (1 + x) - (-1) / (1 + -x) - 2 = 2 * x ^ 2 / ((1 + x) * (1 + -x)) := by
              field_simp; ring
            rw [e]; positivity
        intro s hs0 hs1
        have := hmono ⟨le_refl 0, by norm_num⟩ ⟨hs0, hs1⟩ hs0
        simp at this
        linarith
      have hSc : ∀ l g g' : ℝ, 0 ≤ l → 0 ≤ g' → g' ≤ g - (l - Real.log (1 + l)) →
          (l < 1 → g ≤ -l - Real.log (1 - l)) →
          (l ^ 2 < 1 → g' ≤ -l ^ 2 - Real.log (1 - l ^ 2)) →
          g' ≤ 7 / 2 * g ^ 2 ∧ (1 / 5 < g → g' ≤ g - 1 / 11) := by
        clear * -
        intro l g g' hl0 hg' hdec hlow hW
        refine ⟨?_, fun hg5 => ?_⟩
        · have hD : 0 < 1 + l := by linarith only [hl0]
          set P := l ^ 2 / (2 * (1 + l)) with hPdef
          have hP2 : P * (2 * (1 + l)) = l ^ 2 := div_mul_cancel₀ _ (ne_of_gt (by linarith only [hl0]))
          have hP0 : 0 ≤ P := div_nonneg (sq_nonneg l) (by linarith only [hl0])
          -- ω(l) ≥ P
          have hgP : P + g' ≤ g := by
            have h3 := Real.self_le_sinh_iff.2 (Real.log_nonneg (by linarith only [hl0] : (1:ℝ) ≤ 1 + l))
            rw [Real.sinh_log hD] at h3
            have hv : (1 + l) * (1 + l)⁻¹ = 1 := mul_inv_cancel₀ hD.ne'
            have e : (1 + l)⁻¹ = 1 - l + 2 * P := by
              linear_combination (1 - l + 2 * P) * hv - (1 + l)⁻¹ * hP2
            rw [e] at h3
            linarith only [h3, hdec]
          rcases le_or_gt (1 / 2) l with hl | hl
          · have h12 : 1 / 12 ≤ P := by
              rw [hPdef, le_div_iff₀ (by linarith only [hl0])]
              linarith only [mul_nonneg (sub_nonneg.2 hl) (by linarith only [hl0] : (0:ℝ) ≤ l + 1 / 3)]
            linarith only [sq_nonneg (g - 1 / 7), h12, hgP]
          · have hl2 : l ^ 2 ≤ (1 / 2) ^ 2 := pow_le_pow_left₀ hl0 hl.le 2
            have hE : 0 < 1 - l ^ 2 := by linarith only [hl2]
            have hWb : g' * (2 * (1 - l ^ 2)) ≤ l ^ 4 := by
              have hy : 0 < (1 - l ^ 2)⁻¹ := inv_pos.2 hE
              have hy1 : (1 - l ^ 2) * (1 - l ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hE.ne'
              have h3 := Real.self_le_sinh_iff.2 (Real.log_nonneg (x := (1 - l ^ 2)⁻¹)
                (one_le_inv₀ hE |>.2 (by linarith only [sq_nonneg l])))
              rw [Real.sinh_log hy, Real.log_inv, inv_inv] at h3
              have h4 := hW (by linarith only [hl2])
              have h5 : (2 * g') * (1 - l ^ 2) ≤ ((1 - l ^ 2)⁻¹ - 1 - l ^ 2) * (1 - l ^ 2) :=
                mul_le_mul_of_nonneg_right (by linarith only [h3, h4]) (by linarith only [hE])
              have e : ((1 - l ^ 2)⁻¹ - 1 - l ^ 2) * (1 - l ^ 2) = l ^ 4 := by
                linear_combination hy1
              linarith only [h5, e]
            have hsq : (P + g') ^ 2 ≤ g ^ 2 := pow_le_pow_left₀ (by linarith only [hP0, hg']) hgP 2
            have h7 : 0 ≤ 1 - 7 * P := by
              have hll : l * l ≤ l * (1 / 2) := mul_le_mul_of_nonneg_left hl.le hl0
              refine le_of_mul_le_mul_right (?_ : 0 * (2 * (1 + l)) ≤ (1 - 7 * P) * (2 * (1 + l))) (by linarith only [hl0] : (0:ℝ) < 2 * (1 + l))
              linarith only [hll, hP2, hl0, hl]
            have key : g' * (1 - 7 * P) ≤ 7 / 2 * P ^ 2 := by
              have h1 : g' * (1 - 7 * P) * (2 * (1 - l ^ 2)) ≤ l ^ 4 * (1 - 7 * P) := by
                have := mul_le_mul_of_nonneg_right hWb h7
                linarith only [this]
              have h2 : l ^ 4 * (1 - 7 * P) ≤ 7 / 2 * P ^ 2 * (2 * (1 - l ^ 2)) := by
                have e : 7 / 2 * P ^ 2 * (2 * (1 - l ^ 2)) - l ^ 4 * (1 - 7 * P) =
                    P ^ 2 * (1 + l) * (3 - 11 * l + 14 * l ^ 2) := by
                  linear_combination ((1 - 7 * P) * (l ^ 2 + 2 * P * (1 + l)) + 14 * P ^ 2 * (1 + l)) * hP2
                have : 0 ≤ P ^ 2 * (1 + l) * (3 - 11 * l + 14 * l ^ 2) :=
                  mul_nonneg (mul_nonneg (sq_nonneg P) hD.le) (by linarith only [sq_nonneg (l - 11 / 28)])
                linarith only [e, this]
              exact le_of_mul_le_mul_right (h1.trans h2) (by linarith only [hE])
            linarith only [hsq, key, sq_nonneg g', mul_nonneg hP0 hg']
        · rcases lt_or_ge l (1 / 2) with hl | hl
          · exfalso
            have h1 := hlow (by linarith only [hl])
            have hy : 0 < 2 * (1 - l) := by linarith only [hl]
            have h2 := Real.one_sub_inv_le_log_of_pos hy
            rw [Real.log_mul (by norm_num) (by linarith only [hl])] at h2
            have h3 : (2 * (1 - l))⁻¹ ≤ l + 1 / 2 := by
              rw [inv_le_iff_one_le_mul₀ hy]
              linarith only [mul_nonneg hl0 (by linarith only [hl] : (0:ℝ) ≤ 1 - 2 * l)]
            have h4 := Real.log_two_lt_d9
            linarith only [h1, h2, h3, h4, hg5]
          · have h1 : Real.log ((1 + l) / (3 / 2)) ≤ (1 + l) / (3 / 2) - 1 :=
              Real.log_le_sub_one_of_pos (by linarith only [hl0])
            rw [Real.log_div (by linarith only [hl0]) (by norm_num)] at h1
            have e : Real.log (3 / 2) = Real.log (11 / 9) + Real.log (27 / 22) := by
              rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
            have ha := Real.self_le_sinh_iff.2 (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 11 / 9))
            rw [Real.sinh_log (by norm_num)] at ha
            have hb := Real.self_le_sinh_iff.2 (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 27 / 22))
            rw [Real.sinh_log (by norm_num)] at hb
            norm_num at ha hb
            linarith only [h1, e, ha, hb, hdec, hl]
      have hdecrL : ∀ (μ : Fin n → ℝ) (lam : ℝ), 0 < lam → ∑ i, μ i = ∑ i, μ i ^ 2 →
          lam ^ 2 = ∑ i, μ i ^ 2 → (∀ i, |μ i| ≤ lam) →
          lam - Real.log (1 + lam) ≤ ∑ i, Real.log (1 + 1 / (1 + lam) * μ i) := by
        clear * - hK2 hsym
        intro μ lam hl hN1 hlam2 habs
        have hl1 : 0 < 1 + lam := by linarith
        set p := 1 / (1 + lam) with hp
        have hp0 : 0 < p := by rw [hp]; positivity
        set s := p * lam with hs
        have hs1 : s < 1 := by
          rw [hs, hp, div_mul_eq_mul_div, one_mul, div_lt_one hl1]; linarith
        have hs0 : 0 < s := mul_pos hp0 (by linarith)
        set W := ((-s) - Real.log (1 + -s)) / (-s) ^ 2 with hW
        have hterm : ∀ u : ℝ, |u| ≤ s → u - u ^ 2 * W ≤ Real.log (1 + u) := by
          intro u hu
          have hu1 := neg_abs_le u
          have hu2 := le_abs_self u
          rcases lt_trichotomy u 0 with hneg | hzero | hpos
          · have hmem1 : -s ∈ Set.Ioo (-1:ℝ) 0 := ⟨by linarith, by linarith⟩
            have hmem2 : u ∈ Set.Ioo (-1:ℝ) 0 := ⟨by linarith, hneg⟩
            have hK := hK2 hmem1 hmem2 (by linarith)
            simp only at hK
            have hne : u ≠ 0 := hneg.ne
            have hu0 : 0 < u ^ 2 := lt_of_le_of_ne (sq_nonneg u) (Ne.symm (pow_ne_zero 2 hne))
            have : u - Real.log (1 + u) ≤ u ^ 2 * W := by
              have e : u - Real.log (1 + u) = u ^ 2 * ((u - Real.log (1 + u)) / u ^ 2) := by
                field_simp
              rw [e]; exact mul_le_mul_of_nonneg_left hK hu0.le
            linarith
          · rw [hzero]; simp
          · have hmem1 : -s ∈ Set.Ioo (-1:ℝ) 0 := ⟨by linarith, by linarith⟩
            have hmem2 : -u ∈ Set.Ioo (-1:ℝ) 0 := ⟨by linarith, by linarith⟩
            have hK := hK2 hmem1 hmem2 (by linarith)
            simp only at hK
            have hne : u ≠ 0 := hpos.ne'
            have hu0 : 0 < u ^ 2 := lt_of_le_of_ne (sq_nonneg u) (Ne.symm (pow_ne_zero 2 hne))
            have h1 := hsym u hpos.le (by linarith)
            have : -u - Real.log (1 + -u) ≤ u ^ 2 * W := by
              have e : -u - Real.log (1 + -u) = u ^ 2 * ((-u - Real.log (1 + -u)) / (-u) ^ 2) := by
                field_simp
              rw [e]; exact mul_le_mul_of_nonneg_left hK hu0.le
            linarith
        have hsum : ∑ i, (p * μ i - (p * μ i) ^ 2 * W) ≤ ∑ i, Real.log (1 + p * μ i) :=
          Finset.sum_le_sum fun i _ => hterm _ (by
            rw [abs_mul, abs_of_pos hp0, hs]; exact mul_le_mul_of_nonneg_left (habs i) hp0.le)
        have e1 : ∑ i, (p * μ i - (p * μ i) ^ 2 * W) = p * lam ^ 2 - s ^ 2 * W := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hN1, ← hlam2]
          simp only [mul_pow]
          rw [← Finset.sum_mul, ← Finset.mul_sum, ← hlam2, hs]; ring
        have e2 : s ^ 2 * W = -s - Real.log (1 + -s) := by
          rw [hW]; field_simp
        have e3 : 1 + -s = 1 / (1 + lam) := by rw [hs, hp]; field_simp; ring
        have e4 : p * lam ^ 2 + s = lam := by rw [hs, hp]; field_simp; ring
        have hlogs : Real.log (1 + -s) = -Real.log (1 + lam) := by
          rw [e3, one_div, Real.log_inv]
        show lam - Real.log (1 + lam) ≤ ∑ i, Real.log (1 + p * μ i)
        linarith
      have hSD : ∀ (G A : Matrix (Fin n) (Fin n) ℝ), G.PosDef → A.IsHermitian →
          ∃ T : Matrix (Fin n) (Fin n) ℝ, Tᴴ * G * T = 1 ∧
            ∃ μ : Fin n → ℝ, Tᴴ * A * T = Matrix.diagonal μ := by
        clear * -
        intro G A hG hA
        have hspec := hG.1.spectral_theorem
        simp only [Unitary.conjStarAlgAut_apply] at hspec
        set U : Matrix (Fin n) (Fin n) ℝ := (hG.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hU
        have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
        have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
        set d := hG.1.eigenvalues with hd
        have hdpos : ∀ i, 0 < d i := hG.eigenvalues_pos
        have hG' : G = U * diagonal d * star U := by
          refine hspec.trans ?_; congr 2
        set S := U * diagonal (fun i => 1 / Real.sqrt (d i)) with hS
        have hSH : Sᴴ = diagonal (fun i => 1 / Real.sqrt (d i)) * star U := by
          rw [hS, conjTranspose_mul, diagonal_conjTranspose]; simp [Matrix.star_eq_conjTranspose]
        have hSGS : Sᴴ * G * S = 1 := by
          rw [hSH, hG', hS]
          have : diagonal (fun i => 1 / Real.sqrt (d i)) * star U * (U * diagonal d * star U) *
              (U * diagonal (fun i => 1 / Real.sqrt (d i))) =
              diagonal (fun i => 1 / Real.sqrt (d i)) * (star U * U) * diagonal d * (star U * U) *
              diagonal (fun i => 1 / Real.sqrt (d i)) := by simp only [Matrix.mul_assoc]
          rw [this, hUU, Matrix.mul_one, Matrix.mul_one, diagonal_mul_diagonal, diagonal_mul_diagonal,
            ← diagonal_one]
          congr 1; funext i
          have h1 := hdpos i
          have h2 : Real.sqrt (d i) ^ 2 = d i := Real.sq_sqrt h1.le
          have h3 : 0 < Real.sqrt (d i) := Real.sqrt_pos.2 h1
          field_simp; nlinarith
        set B := Sᴴ * A * S with hB
        have hBH : B.IsHermitian := isHermitian_conjTranspose_mul_mul S hA
        have hspecB := hBH.spectral_theorem
        simp only [Unitary.conjStarAlgAut_apply] at hspecB
        set V : Matrix (Fin n) (Fin n) ℝ := (hBH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hV
        have hVV : star V * V = 1 := Unitary.coe_star_mul_self _
        have hB' : B = V * diagonal hBH.eigenvalues * star V := by
          refine hspecB.trans ?_; congr 2
        clear_value B
        obtain ⟨V, μ, hVV, hB'⟩ : ∃ (V : Matrix (Fin n) (Fin n) ℝ) (μ : Fin n → ℝ),
            star V * V = 1 ∧ B = V * diagonal μ * star V := ⟨_, _, hVV, hB'⟩
        refine ⟨S * V, ?_, μ, ?_⟩
        · rw [conjTranspose_mul]
          have : Vᴴ * Sᴴ * G * (S * V) = Vᴴ * (Sᴴ * G * S) * V := by simp only [Matrix.mul_assoc]
          rw [this, hSGS, Matrix.mul_one, ← Matrix.star_eq_conjTranspose, hVV]
        · rw [conjTranspose_mul]
          have : Vᴴ * Sᴴ * A * (S * V) = Vᴴ * B * V := by simp only [hB, Matrix.mul_assoc]
          rw [this, hB', ← Matrix.star_eq_conjTranspose]
          have : star V * (V * diagonal μ * star V) * V =
            (star V * V) * diagonal μ * (star V * V) := by simp only [Matrix.mul_assoc]
          rw [this, hVV, Matrix.one_mul, Matrix.mul_one]
      -- (LL) the barrier, feasibility and traces along a line, in eigenvalue form
      have hLL : ∀ (G A T : Matrix (Fin n) (Fin n) ℝ) (μ : Fin n → ℝ), G.PosDef →
          Tᴴ * G * T = 1 → Tᴴ * A * T = Matrix.diagonal μ →
        (∀ p : ℝ, (G + p • A).PosDef ↔ ∀ i, 0 < 1 + p * μ i) ∧
        (∀ p : ℝ, (∀ i, 0 < 1 + p * μ i) →
           Real.log (G + p • A)⁻¹.det = Real.log G⁻¹.det - ∑ i, Real.log (1 + p * μ i)) ∧
        (G⁻¹ * A).trace = ∑ i, μ i ∧
        (A * G⁻¹ * A * G⁻¹).trace = ∑ i, μ i ^ 2 := by
        clear * -
        intro G A T μ hG hT hTA
        set W := Tᴴ * G with hW
        have hWT : W * T = 1 := hT
        have hTW : T * W = 1 := mul_eq_one_comm.1 hWT
        have hGinv : G⁻¹ = T * Tᴴ := by
          apply Matrix.inv_eq_left_inv
          rw [Matrix.mul_assoc]; exact hTW
        have hconj : ∀ p : ℝ, Tᴴ * (G + p • A) * T = diagonal (fun i => 1 + p * μ i) := by
          intro p
          rw [Matrix.mul_add, Matrix.add_mul, hT, Matrix.mul_smul, Matrix.smul_mul, hTA]
          ext i j; by_cases h : i = j <;> simp [diagonal, h]
        have hinj : Function.Injective T.mulVec := by
          intro x y hxy
          have := congrArg (W.mulVec) hxy
          simpa [mulVec_mulVec, hWT] using this
        have hpd : ∀ p : ℝ, (G + p • A).PosDef ↔ ∀ i, 0 < 1 + p * μ i := by
          intro p
          rw [← posDef_diagonal_iff, ← hconj p]
          constructor
          · intro h; exact h.conjTranspose_mul_mul_same hinj
          · intro h
            have hinjW : Function.Injective W.mulVec := by
              intro x y hxy
              have := congrArg (T.mulVec) hxy
              simpa [mulVec_mulVec, hTW] using this
            have := h.conjTranspose_mul_mul_same hinjW
            have e : Wᴴ * (Tᴴ * (G + p • A) * T) * W = G + p • A := by
              have : Wᴴ * (Tᴴ * (G + p • A) * T) * W = (T * W)ᴴ * (G + p • A) * (T * W) := by
                simp only [conjTranspose_mul, Matrix.mul_assoc]
              rw [this, hTW]; simp
            rwa [e] at this
        have hdet : ∀ p : ℝ, (G + p • A).det * (T.det * T.det) = ∏ i, (1 + p * μ i) := by
          intro p
          have := congrArg Matrix.det (hconj p)
          rw [det_mul, det_mul, det_conjTranspose, det_diagonal] at this
          simp only [star_trivial] at this
          rw [← this]; ring
        have hc : 0 < T.det * T.det := by
          have h0 := hdet 0
          simp only [zero_smul, add_zero, zero_mul, add_zero, Finset.prod_const_one] at h0
          have := hG.det_pos
          nlinarith
        refine ⟨hpd, ?_, ?_, ?_⟩
        · intro p hp
          have hM := (hpd p).2 hp
          have h0 := hdet 0
          simp only [zero_smul, add_zero, zero_mul, Finset.prod_const_one] at h0
          simp only [det_nonsing_inv, Ring.inverse_eq_inv', Real.log_inv]
          rw [← Real.log_prod (fun i _ => (hp i).ne')]
          rw [← hdet p]
          have h1 := hM.det_pos
          have h2 := hG.det_pos
          rw [Real.log_mul h1.ne' hc.ne']
          have : Real.log G.det = - Real.log (T.det * T.det) := by
            rw [eq_neg_iff_add_eq_zero, ← Real.log_mul h2.ne' hc.ne', h0, Real.log_one]
          rw [this]; ring
        · rw [hGinv, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, ← Matrix.mul_assoc, hTA,
            trace_diagonal]
        · have e1 : A * (T * Tᴴ) * A * (T * Tᴴ) = (A * T * Tᴴ * A * T) * Tᴴ := by
            simp only [Matrix.mul_assoc]
          have e2 : Tᴴ * (A * T * Tᴴ * A * T) = (Tᴴ * A * T) * (Tᴴ * A * T) := by
            simp only [Matrix.mul_assoc]
          rw [hGinv, e1, trace_mul_comm, e2, hTA, diagonal_mul_diagonal, trace_diagonal]
          simp [sq]
      -- (N4b) decrement at the full Newton point, in the eigenbasis of the step
      have hN4b : ∀ (Fx A Av T : Matrix (Fin n) (Fin n) ℝ) (μ : Fin n → ℝ),
          Tᴴ * Fx * T = 1 → Tᴴ * A * T = Matrix.diagonal μ → Av.IsHermitian →
          (∀ i, 0 < 1 + μ i) → (Fx⁻¹ * Av).trace = (Av * Fx⁻¹ * A * Fx⁻¹).trace →
          ((Fx + (1:ℝ) • A)⁻¹ * Av).trace ≤ (∑ i, μ i ^ 2) *
            Real.sqrt ((Av * (Fx + (1:ℝ) • A)⁻¹ * Av * (Fx + (1:ℝ) • A)⁻¹).trace) := by
        clear * -
        intro Fx A Av T μ hT hTμ hAv hμ1 hfo
        set W := Tᴴ * Fx with hW
        have hWT : W * T = 1 := hT
        have hTW : T * W = 1 := mul_eq_one_comm.1 hWT
        have hGinv : Fx⁻¹ = T * Tᴴ := by
          apply Matrix.inv_eq_left_inv
          rw [Matrix.mul_assoc]; exact hTW
        set m : Fin n → ℝ := fun i => 1 / (1 + μ i) with hm
        have hm1 : ∀ i, m i * (1 + μ i) = 1 := fun i => by
          simp only [hm]; field_simp [(hμ1 i).ne']
        have hmpos : ∀ i, 0 < m i := fun i => by simp only [hm]; exact one_div_pos.2 (hμ1 i)
        have hFinv : (Fx + (1:ℝ) • A)⁻¹ = T * diagonal m * Tᴴ := by
          apply Matrix.inv_eq_left_inv
          have h1 : T * diagonal m * Tᴴ * (Fx + (1:ℝ) • A) * T = T := by
            have : Tᴴ * (Fx + (1:ℝ) • A) * T = diagonal (fun i => 1 + μ i) := by
              rw [Matrix.mul_add, Matrix.add_mul, hT, one_smul, hTμ]
              ext i j; by_cases h : i = j <;> simp [diagonal, h]
            calc T * diagonal m * Tᴴ * (Fx + (1:ℝ) • A) * T
                = T * diagonal m * (Tᴴ * (Fx + (1:ℝ) • A) * T) := by simp only [Matrix.mul_assoc]
              _ = T := by
                rw [this, Matrix.mul_assoc, diagonal_mul_diagonal]
                have : (fun i => m i * (1 + μ i)) = fun _ => (1:ℝ) := funext hm1
                rw [this, diagonal_one, Matrix.mul_one]
          calc T * diagonal m * Tᴴ * (Fx + (1:ℝ) • A) = T * diagonal m * Tᴴ * (Fx + (1:ℝ) • A) * (T * W) := by
                rw [hTW, Matrix.mul_one]
            _ = (T * diagonal m * Tᴴ * (Fx + (1:ℝ) • A) * T) * W := by simp only [Matrix.mul_assoc]
            _ = 1 := by rw [h1, hTW]
        set C := Tᴴ * Av * T with hC
        have hCs : ∀ i j, C j i = C i j := by
          intro i j
          have : Cᴴ = C := by
            rw [hC, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hAv.eq,
              Matrix.mul_assoc]
          have := congrFun (congrFun this j) i
          simpa using this.symm
        have e1 : ((Fx + (1:ℝ) • A)⁻¹ * Av).trace = ∑ i, m i * C i i := by
          rw [hFinv, show T * diagonal m * Tᴴ * Av = T * (diagonal m * Tᴴ * Av) by
            simp only [Matrix.mul_assoc], trace_mul_comm,
            show diagonal m * Tᴴ * Av * T = diagonal m * C by simp only [hC, Matrix.mul_assoc]]
          simp [Matrix.trace, diagonal_mul]
        have e2 : (Av * (Fx + (1:ℝ) • A)⁻¹ * Av * (Fx + (1:ℝ) • A)⁻¹).trace =
            ∑ i, ∑ j, C i j * m j * C j i * m i := by
          have : Av * (T * diagonal m * Tᴴ) * Av * (T * diagonal m * Tᴴ) =
              (Av * T * diagonal m * Tᴴ * Av * T * diagonal m) * Tᴴ := by simp only [Matrix.mul_assoc]
          rw [hFinv, this, trace_mul_comm]
          have : Tᴴ * (Av * T * diagonal m * Tᴴ * Av * T * diagonal m) =
              (C * diagonal m) * (C * diagonal m) := by simp only [hC, Matrix.mul_assoc]
          rw [this]
          simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, diagonal_apply, mul_ite, mul_zero,
            Finset.sum_ite_eq', Finset.mem_univ, if_true]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
        have e3 : ∑ i, C i i = ∑ i, μ i * C i i := by
          have h1 : (Fx⁻¹ * Av).trace = ∑ i, C i i := by
            rw [hGinv, Matrix.mul_assoc, trace_mul_comm]; rfl
          have h2 : (Av * Fx⁻¹ * A * Fx⁻¹).trace = ∑ i, μ i * C i i := by
            have : Av * (T * Tᴴ) * A * (T * Tᴴ) = (Av * T * (Tᴴ * A * T)) * Tᴴ := by
              simp only [Matrix.mul_assoc]
            rw [hGinv, this, trace_mul_comm, hTμ]
            have : Tᴴ * (Av * T * diagonal μ) = C * diagonal μ := by simp only [hC, Matrix.mul_assoc]
            rw [this]
            simp [Matrix.trace, mul_diagonal, mul_comm]
          rw [← h1, hfo, h2]
        -- scalar part
        have e4 : ∑ i, m i * C i i = ∑ i, μ i ^ 2 * (m i * C i i) := by
          have : ∀ i, m i * C i i = μ i ^ 2 * (m i * C i i) + (C i i - μ i * C i i) := by
            intro i
            have := hm1 i
            linear_combination (C i i * (1 - μ i)) * this
          rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib, Finset.sum_sub_distrib, e3]
          ring
        have hdiag : ∑ i, (m i * C i i) ^ 2 ≤ ∑ i, ∑ j, C i j * m j * C j i * m i := by
          apply Finset.sum_le_sum; intro i _
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
          have : 0 ≤ ∑ j ∈ Finset.univ.erase i, C i j * m j * C j i * m i := by
            apply Finset.sum_nonneg; intro j _
            rw [hCs i j]
            have e : C i j * m j * C i j * m i = (C i j * C i j) * (m i * m j) := by ring
            rw [e]; exact mul_nonneg (mul_self_nonneg _) (mul_pos (hmpos i) (hmpos j)).le
          have e2 : (m i * C i i) ^ 2 = C i i * m i * C i i * m i := by ring
          linarith
        have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => μ i ^ 2) (fun i => m i * C i i)
        have h4 : ∑ i, (μ i ^ 2) ^ 2 ≤ (∑ i, μ i ^ 2) ^ 2 := by
          rw [sq (∑ i, μ i ^ 2), Finset.sum_mul_sum]
          apply Finset.sum_le_sum; intro i _
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
          have : 0 ≤ ∑ j ∈ Finset.univ.erase i, μ i ^ 2 * μ j ^ 2 :=
            Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
          have e2 : (μ i ^ 2) ^ 2 = μ i ^ 2 * μ i ^ 2 := by ring
          linarith
        rw [e1, e2, e4]
        set Q := ∑ i, ∑ j, C i j * m j * C j i * m i
        have hQ0 : 0 ≤ Q := le_trans (Finset.sum_nonneg fun i _ => sq_nonneg _) hdiag
        have hS0 : 0 ≤ ∑ i, μ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
        have hsq : (∑ i, μ i ^ 2 * (m i * C i i)) ^ 2 ≤ ((∑ i, μ i ^ 2) * Real.sqrt Q) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hQ0]
          calc _ ≤ (∑ i, (μ i ^ 2) ^ 2) * ∑ i, (m i * C i i) ^ 2 := hCS
            _ ≤ (∑ i, μ i ^ 2) ^ 2 * Q := by
                apply mul_le_mul h4 hdiag (Finset.sum_nonneg fun i _ => sq_nonneg _) (sq_nonneg _)
        exact abs_le_of_sq_le_sq' hsq (mul_nonneg hS0 (Real.sqrt_nonneg _)) |>.2
      -- linear structure of the LMI
      have hlmi : ∀ (x d : Fin m → ℝ) (p : ℝ),
          VBSDP.Duality.lmi F₀ F (x + p • d) = VBSDP.Duality.lmi F₀ F x + p • ∑ i, d i • F i := by
        intro x d p
        simp only [VBSDP.Duality.lmi, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul,
          Finset.sum_add_distrib, Finset.smul_sum, add_assoc]
      have hherm : ∀ v : Fin m → ℝ, (∑ i, v i • F i).IsHermitian := by
        intro v
        unfold Matrix.IsHermitian
        rw [Matrix.conjTranspose_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.conjTranspose_smul, (hF i).eq, star_trivial]
      -- (S1) scalar: superadditivity of h(t) = t - log(1+t) in the Euclidean norm
      have hS1 : ∀ ν : Fin n → ℝ, (∀ i, 0 < 1 + ν i) →
          Real.sqrt (∑ i, ν i ^ 2) - Real.log (1 + Real.sqrt (∑ i, ν i ^ 2)) ≤
            ∑ i, (ν i - Real.log (1 + ν i)) := by
        clear * - hK hsym
        intro ν hν
        set r := Real.sqrt (∑ i, ν i ^ 2) with hr
        have hr0 : 0 ≤ r := Real.sqrt_nonneg _
        have hr2 : r ^ 2 = ∑ i, ν i ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
        rcases hr0.lt_or_eq with hrpos | hr00
        · -- each term: h(ν i) ≥ ν i ^ 2 * K r
          have hterm : ∀ i, ν i ^ 2 * ((r - Real.log (1 + r)) / r ^ 2) ≤ ν i - Real.log (1 + ν i) := by
            intro i
            have hle : |ν i| ≤ r := by
              rw [hr]; apply Real.abs_le_sqrt
              exact Finset.single_le_sum (f := fun i => ν i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i)
            rcases (abs_nonneg (ν i)).lt_or_eq with ha | ha
            · have hK1 := hK ha hrpos hle
              simp only at hK1
              have e : ν i ^ 2 = |ν i| ^ 2 := (sq_abs _).symm
              have h3 : |ν i| - Real.log (1 + |ν i|) ≤ ν i - Real.log (1 + ν i) := by
                rcases le_or_gt 0 (ν i) with hp | hn
                · rw [abs_of_nonneg hp]
                · rw [abs_of_neg hn]
                  have := hsym (-ν i) (by linarith) (by linarith [hν i])
                  simpa using this
              have h4 : |ν i| ^ 2 * ((r - Real.log (1 + r)) / r ^ 2) ≤ |ν i| - Real.log (1 + |ν i|) := by
                have hp : 0 < |ν i| ^ 2 := by positivity
                calc |ν i| ^ 2 * ((r - Real.log (1 + r)) / r ^ 2)
                    ≤ |ν i| ^ 2 * ((|ν i| - Real.log (1 + |ν i|)) / |ν i| ^ 2) :=
                      mul_le_mul_of_nonneg_left hK1 hp.le
                  _ = |ν i| - Real.log (1 + |ν i|) := by field_simp
              rw [e]; linarith
            · have h0 : ν i = 0 := abs_eq_zero.1 ha.symm
              rw [h0]; simp
          calc r - Real.log (1 + r) = (∑ i, ν i ^ 2) * ((r - Real.log (1 + r)) / r ^ 2) := by
                rw [← hr2]; field_simp
            _ = ∑ i, ν i ^ 2 * ((r - Real.log (1 + r)) / r ^ 2) := by rw [Finset.sum_mul]
            _ ≤ _ := Finset.sum_le_sum fun i _ => hterm i
        · rw [← hr00]; simp
          exact Finset.sum_le_sum fun i _ => by
            have := Real.log_le_sub_one_of_pos (hν i)
            linarith
      -- (LB) generic lower bound: gap ≤ ω*(Λ) when the gradient is Λ-bounded in the local norm
      have hLB : ∀ z : Fin m → ℝ, (VBSDP.Duality.lmi F₀ F z).PosDef → ∀ Λ : ℝ, 0 ≤ Λ → Λ < 1 →
          (∀ v : Fin m → ℝ, ((VBSDP.Duality.lmi F₀ F z)⁻¹ * ∑ i, v i • F i).trace ≤
            Λ * Real.sqrt (((∑ i, v i • F i) * (VBSDP.Duality.lmi F₀ F z)⁻¹ * (∑ i, v i • F i) *
              (VBSDP.Duality.lmi F₀ F z)⁻¹).trace)) →
          barrier F₀ F z - barrier F₀ F xs ≤ -Λ - Real.log (1 - Λ) := by
        intro z hz Λ hΛ0 hΛ1 hgrad
        obtain ⟨T, hT, ν, hTν⟩ := hSD _ _ hz (hherm (xs - z))
        obtain ⟨hpd, hlog, htr1, htr2⟩ := hLL _ _ T ν hz hT hTν
        have hxs1 : VBSDP.Duality.lmi F₀ F xs =
            VBSDP.Duality.lmi F₀ F z + (1:ℝ) • ∑ i, (xs - z) i • F i := by
          rw [← hlmi]; congr 1; funext i; simp
        have hν : ∀ i, 0 < 1 + 1 * ν i := (hpd 1).1 (hxs1 ▸ hxs.1)
        have hν' : ∀ i, 0 < 1 + ν i := fun i => by simpa using hν i
        have hb : barrier F₀ F xs = barrier F₀ F z - ∑ i, Real.log (1 + ν i) := by
          unfold barrier; rw [hxs1, hlog 1 hν]; simp
        have hg := hgrad (xs - z)
        rw [htr1, htr2] at hg
        have h1 := hS1 ν hν'
        set r := Real.sqrt (∑ i, ν i ^ 2) with hr
        have hr0 : 0 ≤ r := Real.sqrt_nonneg _
        have hsum : ∑ i, (ν i - Real.log (1 + ν i)) = ∑ i, ν i - ∑ i, Real.log (1 + ν i) :=
          Finset.sum_sub_distrib ..
        -- log(1+r) + log(1-Λ) ≤ (1+r)(1-Λ) - 1
        have h2 : Real.log ((1 + r) * (1 - Λ)) ≤ (1 + r) * (1 - Λ) - 1 :=
          Real.log_le_sub_one_of_pos (mul_pos (by linarith) (by linarith))
        rw [Real.log_mul (by linarith) (by linarith),
          show (1 + r) * (1 - Λ) - 1 = r - Λ - Λ * r by ring] at h2
        rw [hb]
        linarith
      have hfeas : ∀ j, (VBSDP.Duality.lmi F₀ F (xk j)).PosDef := by
        intro j
        induction j with
        | zero => exact hrun.1
        | succ j ih =>
          obtain ⟨δx, p, -, hp, -, hx⟩ := hrun.2 j
          rw [hx]; exact hp
      have hsmulA : ∀ (t : ℝ) (v : Fin m → ℝ), ∑ i, (t • v) i • F i = t • ∑ i, v i • F i := by
        intro t v; simp [Finset.smul_sum, mul_smul]
      -- discriminant: if t²Q - 2ta + L ≥ 0 for all t, Q ≥ 0, L ≥ 0, then a ≤ √L √Q
      have hdisc : ∀ a Q L : ℝ, 0 ≤ Q → 0 ≤ L → (∀ t : ℝ, -L / 2 ≤ -t * a + t ^ 2 / 2 * Q) →
          a ≤ Real.sqrt L * Real.sqrt Q := by
        clear * -
        intro a Q L hQ hL h
        rcases le_or_gt a 0 with ha | ha
        · exact le_trans ha (by positivity)
        have hsq : a ^ 2 ≤ L * Q := by
          rcases hQ.lt_or_eq with hQ' | hQ'
          · have := h (a / Q)
            have e : -(a / Q) * a + (a / Q) ^ 2 / 2 * Q = -(a ^ 2 / Q) / 2 := by
              field_simp; ring
            rw [e] at this
            have : a ^ 2 / Q ≤ L := by linarith
            rwa [div_le_iff₀ hQ'] at this
          · exfalso
            have := h ((L + 1) / a)
            rw [← hQ'] at this
            have e : -((L + 1) / a) * a = -(L + 1) := by field_simp
            rw [e, mul_zero, add_zero] at this
            linarith
        rw [← Real.sqrt_mul hL]
        exact Real.le_sqrt_of_sq_le hsq
      -- per-step facts
      have hstep : ∀ j, ∃ μ : Fin n → ℝ, ∑ i, μ i = ∑ i, μ i ^ 2 ∧
          (∀ p : ℝ, (∀ i, 0 < 1 + p * μ i) →
            barrier F₀ F (xk (j + 1)) ≤ barrier F₀ F (xk j) - ∑ i, Real.log (1 + p * μ i)) ∧
          (Real.sqrt (∑ i, μ i ^ 2) < 1 → barrier F₀ F (xk j) - barrier F₀ F xs ≤
            -Real.sqrt (∑ i, μ i ^ 2) - Real.log (1 - Real.sqrt (∑ i, μ i ^ 2))) ∧
          (∑ i, μ i ^ 2 < 1 → barrier F₀ F (xk (j + 1)) - barrier F₀ F xs ≤
            -(∑ i, μ i ^ 2) - Real.log (1 - ∑ i, μ i ^ 2)) := by
        intro j
        obtain ⟨δx, ph, hN, hph, hmin, hx⟩ := hrun.2 j
        have hz := hfeas j
        set Fx := VBSDP.Duality.lmi F₀ F (xk j) with hFx
        obtain ⟨T, hT, μ, hTμ⟩ := hSD _ _ hz (hherm δx)
        obtain ⟨hpd, hlog, htr1, htr2⟩ := hLL _ _ T μ hz hT hTμ
        have hq : ∀ v : Fin m → ℝ,
            -(Fx⁻¹ * ∑ i, δx i • F i).trace +
              (1 / 2 : ℝ) * ((∑ i, δx i • F i) * Fx⁻¹ * (∑ j, δx j • F j) * Fx⁻¹).trace ≤
            -(Fx⁻¹ * ∑ i, v i • F i).trace +
              (1 / 2 : ℝ) * ((∑ i, v i • F i) * Fx⁻¹ * (∑ j, v j • F j) * Fx⁻¹).trace := hN
        rw [htr1, htr2] at hq
        have hb0 : 0 ≤ ∑ i, μ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
        have hN1 : ∑ i, μ i = ∑ i, μ i ^ 2 := by
          set a := ∑ i, μ i
          set b := ∑ i, μ i ^ 2
          have key : ∀ t : ℝ, -a + 1 / 2 * b ≤ -(t * a) + 1 / 2 * (t ^ 2 * b) := by
            intro t
            have := hq (t • δx)
            simp only [hsmulA, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
              at this
            rw [htr1, htr2] at this
            nlinarith
          have h0 := hlin0 (b - a) (b / 2) (fun u => by
            have := key (1 + u); ring_nf at this ⊢; linarith)
          linarith
        refine ⟨μ, hN1, ?_, ?_, ?_⟩
        · intro p hp
          have h1 : VBSDP.Duality.lmi F₀ F (xk j + p • δx) = Fx + p • ∑ i, δx i • F i := hlmi _ _ _
          have := hmin p (by rw [h1]; exact (hpd p).2 hp)
          rw [← hx] at this
          have e : barrier F₀ F (xk j + p • δx) = barrier F₀ F (xk j) - ∑ i, Real.log (1 + p * μ i) := by
            unfold barrier; rw [h1, hlog p hp]
          linarith
        · intro hl1
          apply hLB (xk j) hz _ (Real.sqrt_nonneg _) hl1
          intro v
          obtain ⟨T', hT', ν, hTν⟩ := hSD _ _ hz (hherm v)
          obtain ⟨-, -, htr1', htr2'⟩ := hLL _ _ T' ν hz hT' hTν
          have hQ0 : 0 ≤ ∑ i, ν i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
          rw [htr2', htr1']
          apply hdisc _ _ _ hQ0 hb0
          intro t
          have := hq (t • v)
          simp only [hsmulA, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
            at this
          rw [htr1', htr2'] at this
          rw [hN1] at this
          ring_nf at this ⊢; linarith
        · intro hl1
          set A := ∑ i, δx i • F i with hA
          have hμ1 : ∀ i, 0 < 1 + μ i := by
            intro i
            have : μ i ^ 2 ≤ ∑ i, μ i ^ 2 :=
              Finset.single_le_sum (f := fun i => μ i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i)
            have h2 : μ i ^ 2 < 1 ^ 2 := by rw [one_pow]; linarith
            have := (abs_lt_of_sq_lt_sq' h2 zero_le_one).1
            linarith
          have hμ1' : ∀ i, 0 < 1 + 1 * μ i := fun i => by simpa using hμ1 i
          have h1 : VBSDP.Duality.lmi F₀ F (xk j + (1:ℝ) • δx) = Fx + (1:ℝ) • A := hlmi _ _ _
          have hpd1 : (VBSDP.Duality.lmi F₀ F (xk j + (1:ℝ) • δx)).PosDef := by
            rw [h1]; exact (hpd 1).2 hμ1'
          have hle := hmin 1 hpd1
          rw [← hx] at hle
          suffices H : barrier F₀ F (xk j + (1:ℝ) • δx) - barrier F₀ F xs ≤
              -(∑ i, μ i ^ 2) - Real.log (1 - ∑ i, μ i ^ 2) by linarith
          apply hLB _ hpd1 _ hb0 hl1
          intro v
          -- first-order Newton condition
          have hfo : (Fx⁻¹ * ∑ i, v i • F i).trace =
              ((∑ i, v i • F i) * Fx⁻¹ * A * Fx⁻¹).trace := by
            set Av := ∑ i, v i • F i
            set α := (Fx⁻¹ * Av).trace with hα
            set β := (Av * Fx⁻¹ * A * Fx⁻¹).trace with hβ
            set γ := (Av * Fx⁻¹ * Av * Fx⁻¹).trace with hγ
            have key : ∀ t : ℝ, 0 ≤ t * (β - α) + t ^ 2 / 2 * γ := by
              intro t
              have := hq (δx + t • v)
              have e : ∑ i, (δx + t • v) i • F i = A + t • Av := by
                simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul,
                  Finset.sum_add_distrib, Finset.smul_sum, A, Av]
              rw [e] at this
              have ec : (A * Fx⁻¹ * Av * Fx⁻¹).trace = β := by
                show _ = (Av * Fx⁻¹ * A * Fx⁻¹).trace
                rw [show A * Fx⁻¹ * Av * Fx⁻¹ = (A * Fx⁻¹) * (Av * Fx⁻¹) by
                  simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
                simp only [Matrix.mul_assoc]
              simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
                Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, ec] at this
              rw [htr1, htr2, ← hα, ← hγ, ← hβ] at this
              linarith
            have h0 := hlin0 (β - α) (γ / 2) (fun u => by
              have := key u; ring_nf at this ⊢; linarith)
            show α = β
            linarith
          rw [h1]
          exact hN4b Fx A _ T μ hT hTμ (hherm v) hμ1 hfo
      clear hK hK2 hsym hN4b hSD hLL hLB hS1 hdisc hsmulA hlmi hherm hbdd
      set g : ℕ → ℝ := fun j => barrier F₀ F (xk j) - barrier F₀ F xs with hgdef
      have hg0 : ∀ j, 0 ≤ g j := fun j => sub_nonneg.2 (hxs.2 _ (hfeas j))
      have hmono : ∀ j, g (j + 1) ≤ g j := by
        intro j
        obtain ⟨δx, p, -, -, hmin, hx⟩ := hrun.2 j
        have h0 := hmin 0 (by simpa using hfeas j)
        simp only [hgdef, hx]
        simp only [zero_smul, add_zero] at h0
        linarith
      have hAB : ∀ j, g (j + 1) ≤ 7 / 2 * g j ^ 2 ∧ (1 / 5 < g j → g (j + 1) ≤ g j - 1 / 11) := by
        intro j
        obtain ⟨μ, hN1, hdec, hlow, hW⟩ := hstep j
        have hL0 : 0 ≤ ∑ i, μ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
        set L := ∑ i, μ i ^ 2 with hL
        set lam := Real.sqrt L with hlam
        have hlam0 : 0 ≤ lam := Real.sqrt_nonneg _
        have hlam2 : lam ^ 2 = L := Real.sq_sqrt hL0
        have hm := hmono j
        have hd : g (j + 1) ≤ g j - (lam - Real.log (1 + lam)) := by
          rcases hlam0.lt_or_eq with hpos | hz
          · have habs : ∀ i, |μ i| ≤ lam := by
              intro i
              have : μ i ^ 2 ≤ L :=
                Finset.single_le_sum (f := fun i => μ i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i)
              rw [hlam]; exact Real.abs_le_sqrt this
            have hdecr := hdecrL μ lam hpos hN1 hlam2 habs
            have hp : 0 < 1 + lam := by linarith only [hlam0]
            have hfeas' : ∀ i, 0 < 1 + 1 / (1 + lam) * μ i := by
              intro i
              have h1 : -lam ≤ μ i := by linarith only [neg_abs_le (μ i), habs i]
              have e : 1 + 1 / (1 + lam) * μ i = (1 + lam + μ i) * (1 + lam)⁻¹ := by
                rw [add_mul, mul_inv_cancel₀ hp.ne']; ring
              rw [e]; exact mul_pos (by linarith only [h1]) (inv_pos.2 hp)
            have := hdec _ hfeas'
            show barrier F₀ F (xk (j + 1)) - barrier F₀ F xs ≤
              barrier F₀ F (xk j) - barrier F₀ F xs - (lam - Real.log (1 + lam))
            linarith only [this, hdecr]
          · rw [← hz]
            simp only [add_zero, Real.log_one, sub_zero]
            exact hm
        have hW' : lam ^ 2 < 1 → g (j + 1) ≤ -lam ^ 2 - Real.log (1 - lam ^ 2) := by
          rw [hlam2]; exact hW
        exact hSc lam (g j) (g (j + 1)) hlam0 (hg0 (j + 1)) hd hlow hW'
      have hB : ∀ j, g (j + 1) ≤ 7 / 2 * g j ^ 2 := fun j => (hAB j).1
      have hA : ∀ j, 1 / 5 < g j → g (j + 1) ≤ g j - 1 / 11 := fun j => (hAB j).2
      clear hAB hstep hdecrL hSc
      -- Phase 1: the first index where the gap is at most 1/5.
      have hlin : ∀ j, (∀ i < j, 1 / 5 < g i) → g j ≤ g 0 - j / 11 := by
        intro j
        induction j with
        | zero => intro _; simp
        | succ j ih =>
          intro h
          have h1 := ih (fun i hi => h i (by omega))
          have h2 := hA j (h j (by omega))
          push_cast; linarith
      have hex : ∃ s, g s ≤ 1 / 5 := by
        by_contra hne
        push Not at hne
        obtain ⟨N, hN⟩ := exists_nat_gt (11 * g 0)
        have := hlin N (fun i _ => hne i)
        have := hne N
        have := hg0 N
        have : (N : ℝ) / 11 > g 0 := by linarith
        linarith
      set s := Nat.find hex with hsdef
      have hs : g s ≤ 1 / 5 := Nat.find_spec hex
      have hbefore : ∀ i < s, 1 / 5 < g i := by
        intro i hi
        have := Nat.find_min hex hi
        push Not at this; exact this
      have hsle : (s : ℝ) ≤ 11 * g 0 := by
        rcases Nat.eq_zero_or_pos s with h | h
        · rw [h]; simp; linarith [hg0 0]
        · have h1 := hlin (s - 1) (fun i hi => hbefore i (lt_of_lt_of_le hi (Nat.sub_le s 1)))
          have h2 := hbefore (s - 1) (Nat.sub_lt h Nat.one_pos)
          have h3 : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by
            rw [Nat.cast_sub h]; simp
          rw [h3] at h1
          linarith
      -- Phase 2: quadratic convergence.
      have hu : ∃ u : ℕ, g u ≤ 1 / 7 ∧ (u : ℝ) ≤ 11 * g 0 := by
        rcases le_or_gt (g s) (1 / 7) with h | h
        · exact ⟨s, h, hsle⟩
        · refine ⟨s + 1, ?_, ?_⟩
          · have h1 := hB s
            have h0 := hg0 s
            have h2 : g s * g s ≤ g s * (1 / 5) := mul_le_mul_of_nonneg_left hs h0
            linarith only [h1, h2, hs]
          · rcases Nat.eq_zero_or_pos s with h' | h'
            · rw [h'] at h ⊢; push_cast; linarith only [h]
            · have h1 := hlin (s - 1) (fun i hi => hbefore i (lt_of_lt_of_le hi (Nat.sub_le s 1)))
              have h2 := hbefore (s - 1) (Nat.sub_lt h' Nat.one_pos)
              have h3 : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by
                rw [Nat.cast_sub h']; simp
              rw [h3] at h1
              push_cast
              linarith only [h1, h2]
      obtain ⟨u, hu1, hu2⟩ := hu
      -- Phase 2: quadratic convergence.
      have hquad : ∀ t : ℕ, 7 / 2 * g (u + t) ≤ (1 / 2 : ℝ) ^ (2 ^ t) := by
        intro t
        induction t with
        | zero => rw [add_zero, pow_zero, pow_one]; linarith only [hu1]
        | succ t ih =>
          have h1 := hB (u + t)
          have h0 := hg0 (u + t)
          have : (7 / 2 * g (u + t)) ^ 2 ≤ ((1 / 2 : ℝ) ^ (2 ^ t)) ^ 2 :=
            pow_le_pow_left₀ (by linarith only [h0]) ih 2
          rw [← pow_mul, ← pow_succ] at this
          rw [← add_assoc]
          linarith only [this, h1]
      -- Final counting.
      have hL1 : 1 ≤ Real.logb 2 (1 / ε) := by
        rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
        rw [Real.rpow_one, le_div_iff₀ hε₀]; norm_num at hε₁; linarith
      have hks : u ≤ k := by
        have : (u : ℝ) ≤ k := by
          have : 0 ≤ Real.logb 2 (Real.logb 2 (1 / ε)) :=
            Real.logb_nonneg (by norm_num) hL1
          linarith
        exact_mod_cast this
      set t := k - u with htdef
      have hkt : k = u + t := by omega
      have htR : Real.logb 2 (Real.logb 2 (1 / ε)) ≤ (t : ℝ) := by
        have : (t : ℝ) = k - u := by rw [htdef, Nat.cast_sub hks]
        linarith
      have h2t : Real.logb 2 (1 / ε) ≤ ((2 ^ t : ℕ) : ℝ) := by
        rw [Real.logb_le_iff_le_rpow (by norm_num) (by linarith)] at htR
        have : (2 : ℝ) ^ (t : ℝ) = ((2 ^ t : ℕ) : ℝ) := by
          rw [Real.rpow_natCast]; push_cast; ring
        linarith
      have hfin : (1 / 2 : ℝ) ^ (2 ^ t) ≤ ε := by
        have e1 : (1 / 2 : ℝ) ^ (2 ^ t) = (2 : ℝ) ^ (-(((2 ^ t : ℕ) : ℝ))) := by
          rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]; simp
        have e2 : ε = (2 : ℝ) ^ (-(Real.logb 2 (1 / ε))) := by
          rw [Real.rpow_neg (by norm_num), Real.rpow_logb (by norm_num) (by norm_num)
            (by positivity)]; simp
        rw [e1, e2]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      have := hquad t
      rw [← hkt] at this
      show g k ≤ ε
      have := hg0 k
      linarith
