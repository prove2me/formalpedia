-- Prove2me | solution 1 for TradingPostNSW.Leontief.Supplement.theorem_3_6
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:13:56.274792+00:00
-- url     : https://prove2.me/submissions/63fe99f7-4d9a-4b07-88d5-ea00dfa7f13b

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting
import Definitions.Def_TradingPostNSW_Leontief_Supplement_Setting

open TradingPostNSW
open TradingPostNSW.Leontief
open TradingPostNSW.Leontief.Supplement

theorem solution (c : ℝ) (hc : c < Real.exp (1 / Real.exp 1)) :
    ∃ (n m : ℕ) (I : Instance n m), LinStanding I ∧
      ∃ y : Fin n → Fin m → ℝ, Feasible I y ∧
        ∀ O : (Fin n → Fin m → ℝ) → (Fin m → ℝ) × (Fin n → Fin m → ℝ),
          IsPartialOutcomeRule (· ∈ orthant m) (linMechEq I) O →
          SelectsPreferred (· ∈ orthant m) (linMechEq I) (linU I) O →
          ∃ s : Fin n → Fin m → ℝ, IsMechPNE (· ∈ orthant m) (linMechEq I) (linU I) O s ∧
            0 < NSWU I (linU I) (O s).2 ∧
            c * NSWU I (linU I) (O s).2 ≤ NSWU I (linU I) y := by
              obtain ⟨x, hx1, hx2, hcx⟩ : ∃ x : ℝ, 1 < x ∧ x ≤ 2 ∧ c * x ≤ Real.exp (1 / Real.exp 1) := by
                by_cases hc0 : c ≤ 0
                · refine ⟨2, by norm_num, le_refl _, ?_⟩
                  have := Real.exp_pos (1 / Real.exp 1); nlinarith
                · rw [not_le] at hc0
                  refine ⟨min (Real.exp (1 / Real.exp 1) / c) 2, ?_, min_le_right _ _, ?_⟩
                  · apply lt_min _ (by norm_num); rw [lt_div_iff₀ hc0]; linarith
                  · calc c * min (Real.exp (1 / Real.exp 1) / c) 2
                        ≤ c * (Real.exp (1 / Real.exp 1) / c) := by gcongr; exact min_le_left _ _
                      _ = _ := by field_simp
              have he2 : (2:ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
              set e := Real.exp 1 with he_def
              have he0 : 0 < e := by linarith
              let I : Instance 2 2 := ⟨![![1,0],![0,1]], ![1, e - 1]⟩
              have hU0 : ∀ w : Fin 2 → ℝ, linU I 0 w = w 0 := by
                intro w; simp [linU, I, Fin.sum_univ_two]
              have hU1 : ∀ w : Fin 2 → ℝ, linU I 1 w = w 1 := by
                intro w; simp [linU, I, Fin.sum_univ_two]
              have hNSW : ∀ w : Fin 2 → Fin 2 → ℝ,
                  NSWU I (linU I) w = ((w 0 0) ^ (1:ℝ) * (w 1 1) ^ (e - 1)) ^ (1 / e) := by
                intro w
                simp only [NSWU, totalBudget, Fin.prod_univ_two, Fin.sum_univ_two, hU0, hU1]
                simp [I]
              -- core facts about any equilibrium where agent 1 reports (1, x-1)
              have hcore : ∀ (t : Fin 2 → Fin 2 → ℝ) (p : Fin 2 → ℝ) (z : Fin 2 → Fin 2 → ℝ),
                  t 1 = ![1, x - 1] → linMechEq I t p z →
                  0 < p 0 ∧ 0 < p 1 ∧ p 0 + p 1 = e ∧ 0 ≤ z 0 0 ∧ 0 ≤ z 0 1 ∧ 0 ≤ z 1 0 ∧ 0 ≤ z 1 1 ∧
                  z 0 0 + z 1 0 = 1 ∧ z 0 1 + z 1 1 = 1 ∧ z 0 0 * p 0 + z 0 1 * p 1 = 1 ∧
                  z 1 0 * p 0 + z 1 1 * p 1 = e - 1 ∧
                  (∀ y0 y1 : ℝ, 0 ≤ y0 → 0 ≤ y1 → p 0 * y0 + p 1 * y1 ≤ e - 1 →
                    y0 + (x - 1) * y1 ≤ z 1 0 + (x - 1) * z 1 1) := by
                intro t p z ht h
                obtain ⟨⟨hp, hz, hsup, hsold, hbud, hopt⟩, _⟩ := h
                have hM : ∀ y0 y1 : ℝ, 0 ≤ y0 → 0 ≤ y1 → p 0 * y0 + p 1 * y1 ≤ e - 1 →
                    y0 + (x - 1) * y1 ≤ z 1 0 + (x - 1) * z 1 1 := by
                  intro y0 y1 h0 h1 hcost
                  have := hopt 1 ![y0, y1] (by intro j; fin_cases j <;> simp [h0, h1])
                    (by simpa [Fin.sum_univ_two, I] using hcost)
                  simpa [linRep, ht, Fin.sum_univ_two] using this
                have hb0 := hbud 0
                have hb1 := hbud 1
                simp only [Fin.sum_univ_two] at hb0 hb1
                have hB0 : I.B 0 = 1 := by simp [I]
                have hB1 : I.B 1 = e - 1 := by simp [I]
                rw [hB0] at hb0; rw [hB1] at hb1
                have hz00 := hz 0 0; have hz01 := hz 0 1; have hz10 := hz 1 0; have hz11 := hz 1 1
                have hp0 : 0 < p 0 := by
                  rcases (hp 0).lt_or_eq with h | h
                  · exact h
                  · exfalso
                    have := hM (z 1 0 + (x - 1) * z 1 1 + 1) 0 (by nlinarith) le_rfl
                      (by rw [← h]; simp; linarith)
                    linarith
                have hp1 : 0 < p 1 := by
                  rcases (hp 1).lt_or_eq with h | h
                  · exact h
                  · exfalso
                    have hx0 : 0 < x - 1 := by linarith
                    have := hM 0 ((z 1 0 + (x - 1) * z 1 1 + 1) / (x - 1)) le_rfl
                      (by apply div_nonneg _ hx0.le; nlinarith) (by rw [← h]; simp; linarith)
                    rw [mul_div_cancel₀ _ hx0.ne'] at this
                    linarith
                have hs0 := hsold 0 hp0
                have hs1 := hsold 1 hp1
                simp only [Fin.sum_univ_two] at hs0 hs1
                refine ⟨hp0, hp1, ?_, hz00, hz01, hz10, hz11, hs0, hs1, hb0, hb1, hM⟩
                linear_combination (-(p 0)) * hs0 - p 1 * hs1 + hb0 + hb1
              have hUB : ∀ (t : Fin 2 → Fin 2 → ℝ) (p : Fin 2 → ℝ) (z : Fin 2 → Fin 2 → ℝ),
                  t 1 = ![1, x - 1] → linMechEq I t p z → z 0 0 ≤ x / e := by
                intro t p z ht h
                obtain ⟨hp0, hp1, hsum, hz00, hz01, hz10, hz11, hs0, hs1, hb0, hb1, hM⟩ := hcore t p z ht h
                rw [le_div_iff₀ he0]
                by_cases hcase : e ≤ p 0 * x
                · have h1 : z 0 0 * p 0 ≤ 1 := by nlinarith [mul_nonneg hz01 hp1.le]
                  nlinarith [mul_le_mul_of_nonneg_left hcase hz00]
                · rw [not_le] at hcase
                  have hy := hM ((e - 1) / p 0) 0 (div_nonneg (by linarith) hp0.le) le_rfl
                    (by rw [mul_div_cancel₀ _ hp0.ne']; simp)
                  have hy' : e - 1 ≤ z 1 0 * p 0 + (x - 1) * z 1 1 * p 0 := by
                    have := mul_le_mul_of_nonneg_right hy hp0.le
                    rw [mul_zero, add_zero, div_mul_cancel₀ _ hp0.ne'] at this
                    linarith
                  have hz11' : z 1 1 = 0 := by
                    have hpos : 0 < e - x * p 0 := by linarith
                    have : z 1 1 * (e - x * p 0) ≤ 0 := by
                      have E2 : z 1 1 * (p 0 + p 1) = z 1 1 * e := by rw [hsum]
                      linarith
                    nlinarith [mul_nonneg hz11 hpos.le]
                  rw [hz11'] at hb1
                  have hz00' : z 0 0 = 1 - z 1 0 := by linarith
                  rw [hz00']
                  -- (1 - z10) e ≤ x, with z10 p0 = e - 1, p0 x < e
                  have hex : 0 < e - x := by linarith
                  have k1 : p 0 * x * (e - x) ≤ e * (e - x) := mul_le_mul_of_nonneg_right hcase.le hex.le
                  have k2 : e * (e - x) ≤ e * (e - 1) * x := by
                    have := mul_pos (mul_pos he0 he0) (sub_pos.2 hx1)
                    nlinarith
                  have k3 : p 0 * (e - x) ≤ e * (e - 1) := by
                    have hx0 : 0 < x := by linarith
                    have : p 0 * (e - x) * x ≤ e * (e - 1) * x := by linarith
                    exact le_of_mul_le_mul_right this hx0
                  have k4 : p 0 * ((1 - z 1 0) * e - x) = p 0 * (e - x) - e * (e - 1) := by
                    linear_combination (-e) * hb1
                  by_contra hcon
                  have := mul_pos hp0 (sub_pos.2 (not_le.1 hcon))
                  linarith
              have hLB : ∀ (p : Fin 2 → ℝ) (z : Fin 2 → Fin 2 → ℝ),
                  linMechEq I ![![1, 0], ![1, x - 1]] p z → x / e ≤ z 0 0 ∧ z 1 1 = 1 := by
                intro p z h
                obtain ⟨hp0, hp1, hsum, hz00, hz01, hz10, hz11, hs0, hs1, hb0, hb1, hM⟩ :=
                  hcore _ p z (by simp) h
                have hA : ∀ y0 y1 : ℝ, 0 ≤ y0 → 0 ≤ y1 → p 0 * y0 + p 1 * y1 ≤ 1 → y0 ≤ z 0 0 := by
                  intro y0 y1 h0 h1 hcost
                  have := h.1.opt 0 ![y0, y1] (by intro j; fin_cases j <;> simp [h0, h1])
                    (by simpa [Fin.sum_univ_two, I] using hcost)
                  simpa [linRep, Fin.sum_univ_two] using this
                have hA1 := hA (1 / p 0) 0 (by positivity) le_rfl (by rw [mul_one_div_cancel hp0.ne']; simp)
                have hzp : 1 ≤ z 0 0 * p 0 := by
                  have := mul_le_mul_of_nonneg_right hA1 hp0.le
                  rwa [one_div_mul_cancel hp0.ne'] at this
                have hz01' : z 0 1 = 0 := by nlinarith [mul_nonneg hz01 hp1.le]
                have hz11' : z 1 1 = 1 := by linarith
                refine ⟨?_, hz11'⟩
                rw [div_le_iff₀ he0]
                have hpx : p 0 * x ≤ e := by
                  by_contra hcon
                  rw [not_le] at hcon
                  have hx0 : 0 < x - 1 := by linarith
                  have hy := hM 0 ((e - 1) / p 1) le_rfl (div_nonneg (by linarith) hp1.le)
                    (by rw [mul_div_cancel₀ _ hp1.ne']; simp)
                  have hy' : (x - 1) * (e - 1) ≤ z 1 0 * p 1 + (x - 1) * z 1 1 * p 1 := by
                    have := mul_le_mul_of_nonneg_right hy hp1.le
                    rw [zero_add, mul_assoc, div_mul_cancel₀ _ hp1.ne'] at this
                    nlinarith
                  have hz10' : z 1 0 = 0 := by
                    have hpos : 0 < x * p 0 - e := by linarith
                    have : z 1 0 * (x * p 0 - e) ≤ 0 := by
                      have E1 : (x - 1) * (z 1 0 * p 0 + z 1 1 * p 1) = (x - 1) * (e - 1) := by rw [hb1]
                      have E2 : z 1 0 * (p 0 + p 1) = z 1 0 * e := by rw [hsum]
                      linarith
                    nlinarith [mul_nonneg hz10 hpos.le]
                  have : p 0 = 1 := by
                    have h00 : z 0 0 = 1 := by linarith
                    rw [h00, hz01'] at hb0; linarith
                  rw [this] at hcon; linarith
                nlinarith [mul_le_mul_of_nonneg_left hpx hz00]
              have hx0 : 0 < x := by linarith
              have hEx : linMechEq I ![![1, 0], ![1, x - 1]] ![e / x, e - e / x]
                  ![![x / e, 0], ![1 - x / e, 1]] := by
                have k2 : x / e * e = x := div_mul_cancel₀ _ he0.ne'
                have k3 : x / e * (e / x) = 1 := by field_simp
                have hex1 : 1 < e / x := by rw [lt_div_iff₀ hx0]; linarith
                have hxe1 : x / e < 1 := by rw [div_lt_one he0]; linarith
                have hxe0 : 0 < x / e := div_pos hx0 he0
                have hQ : e / x < e := by rw [div_lt_iff₀ hx0]; nlinarith
                refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
                · intro j; fin_cases j <;> simp <;> linarith
                · intro i j; fin_cases i <;> fin_cases j <;> simp <;> linarith
                · intro j; fin_cases j <;> simp [Fin.sum_univ_two]
                · intro j _; fin_cases j <;> simp [Fin.sum_univ_two]
                · intro i; fin_cases i
                  · simpa [Fin.sum_univ_two, I] using k3
                  · simp [Fin.sum_univ_two, I]; linear_combination (-1 : ℝ) * k3
                · intro i y hy hcost
                  have hy0 := hy 0; have hy1 := hy 1
                  fin_cases i
                  · simp [linRep, Fin.sum_univ_two, I] at hcost ⊢
                    have h1 : e / x * y 0 ≤ 1 := by nlinarith
                    have := mul_le_mul_of_nonneg_left h1 hxe0.le
                    rw [← mul_assoc, k3, one_mul, mul_one] at this
                    exact this
                  · simp [linRep, Fin.sum_univ_two, I] at hcost ⊢
                    have := mul_le_mul_of_nonneg_left hcost hxe0.le
                    linear_combination this + (y 1 - y 0) * k3 + (1 - y 1) * k2
                · intro j hj; exfalso; fin_cases j <;> simp [Fin.sum_univ_two] at hj; linarith
              refine ⟨2, 2, I, ⟨by norm_num, ?_, ?_⟩, ![![1, 0], ![0, 1]], ⟨?_, ?_⟩, ?_⟩
              · intro i j; fin_cases i <;> fin_cases j <;> simp [I]
              · intro i; fin_cases i <;> simp [I]; linarith
              · intro i j; fin_cases i <;> fin_cases j <;> simp
              · intro j; fin_cases j <;> simp [Fin.sum_univ_two]
              intro O hO _
              set s : Fin 2 → Fin 2 → ℝ := ![![1, 0], ![1, x - 1]] with hs_def
              have hadm : ∀ i, s i ∈ orthant 2 := by
                intro i j; fin_cases i <;> fin_cases j <;> simp [s] <;> linarith
              have hEs := hO s hadm ⟨_, _, hEx⟩
              have hlb := hLB _ _ hEs
              have hub := hUB s _ _ (by simp [s]) hEs
              have hval : (O s).2 0 0 = x / e := le_antisymm hub hlb.1
              refine ⟨s, ⟨hadm, ⟨_, _, hEx⟩, ?_⟩, ?_, ?_⟩
              · intro i r hr hex
                have hadm' : ∀ k, Function.update s i r k ∈ orthant 2 := by
                  intro k; by_cases hk : k = i
                  · subst hk; simpa using hr
                  · rw [Function.update_of_ne hk]; exact hadm k
                have hE' := hO _ hadm' hex
                obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
                · rw [hU0, hU0, hval]
                  exact hUB _ _ _ (by simp [Function.update, s]) hE'
                · rw [hU1, hU1, hlb.2]
                  have h1 := hE'.1.supply 1
                  have h2 := hE'.1.x_nonneg 0 1
                  simp only [Fin.sum_univ_two] at h1
                  linarith
              · rw [hNSW, hval, hlb.2]
                simp only [Real.rpow_one, Real.one_rpow, mul_one]
                exact Real.rpow_pos_of_pos (div_pos hx0 he0) _
              · rw [hNSW, hNSW, hval, hlb.2]
                simp only [Real.rpow_one, Real.one_rpow, mul_one, Matrix.cons_val_zero, Matrix.cons_val_one]
                rw [Real.div_rpow hx0.le he0.le]
                have hee : e ^ (1 / e) = Real.exp (1 / e) := by rw [he_def]; exact Real.exp_one_rpow _
                rw [hee, mul_div_assoc', div_le_one (Real.exp_pos _)]
                have hle : x ^ (1 / e) ≤ x := by
                  have := Real.rpow_le_rpow_of_exponent_le hx1.le
                    (show 1 / e ≤ (1:ℝ) by rw [div_le_one he0]; linarith)
                  rwa [Real.rpow_one] at this
                have hpos : 0 < x ^ (1 / e) := Real.rpow_pos_of_pos hx0 _
                rcases le_or_gt 0 c with hc0 | hc0
                · calc c * x ^ (1 / e) ≤ c * x := mul_le_mul_of_nonneg_left hle hc0
                    _ ≤ _ := hcx
                · have := Real.exp_pos (1 / e)
                  nlinarith
