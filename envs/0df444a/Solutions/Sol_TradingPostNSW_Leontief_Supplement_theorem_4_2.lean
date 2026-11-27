-- Prove2me | solution 1 for TradingPostNSW.Leontief.Supplement.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:15:16.085684+00:00
-- url     : https://prove2.me/submissions/2c1547b9-1c56-4ef7-84bd-2e57fd7cb3f0

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting
import Definitions.Def_TradingPostNSW_Leontief_Supplement_Setting

open TradingPostNSW
open TradingPostNSW.Leontief
open TradingPostNSW.Leontief.Supplement

theorem solution (c : ℝ) (hc : c < Real.exp (1 / Real.exp 1)) :
    ∃ (n m : ℕ) (I : Instance n m), LinStanding I ∧ PerfectCompetition I ∧
      ∃ b : Fin n → Fin m → ℝ, IsPNEU I (linU I) 0 b ∧
        0 < NSWU I (linU I) (tpAlloc 0 b) ∧
        ∃ y : Fin n → Fin m → ℝ, Feasible I y ∧
          c * NSWU I (linU I) (tpAlloc 0 b) ≤ NSWU I (linU I) y := by
            have he1 := Real.exp_one_gt_d9
            have he2 := Real.exp_one_lt_d9
            set e := Real.exp 1 with he
            have hepos : 0 < e := by linarith
            obtain ⟨η, hη0, hη1, hηc⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
                ∀ X : ℝ, 0 ≤ X → X ≤ 1/e + 7*η → c * X^(1/e) ≤ 1 := by
              by_cases hc0 : c ≤ 0
              · refine ⟨1, one_pos, le_rfl, fun X hX _ => ?_⟩
                have : 0 ≤ X^(1/e) := Real.rpow_nonneg hX _
                nlinarith
              · replace hc0 := not_le.mp hc0
                have hD1 : 1/e < (1/c)^e := by
                  have h1 : Real.exp (-(1/e)) < 1/c := by
                    rw [Real.exp_neg, ← one_div]; exact one_div_lt_one_div_of_lt hc0 hc
                  have h2 : (Real.exp (-(1/e)))^e < (1/c)^e :=
                    Real.rpow_lt_rpow (Real.exp_pos _).le h1 hepos
                  rw [← Real.exp_mul] at h2
                  have : -(1/e) * e = -1 := by field_simp
                  rw [this, Real.exp_neg, ← he] at h2
                  simpa [one_div] using h2
                refine ⟨min 1 (((1/c)^e - 1/e)/7), lt_min one_pos (by linarith), min_le_left _ _,
                  fun X hX hXle => ?_⟩
                have hm := min_le_right 1 (((1/c)^e - 1/e)/7)
                have hXD : X ≤ (1/c)^e := by linarith
                have h3 : X^(1/e) ≤ ((1/c)^e)^(1/e) :=
                  Real.rpow_le_rpow hX hXD (by positivity)
                rw [one_div e, Real.rpow_rpow_inv (by positivity) hepos.ne'] at h3
                have : c * X^(e⁻¹) ≤ c * (1/c) := mul_le_mul_of_nonneg_left h3 hc0.le
                rw [mul_one_div_cancel hc0.ne'] at this
                simpa [one_div] using this

            clear_value e
            obtain ⟨s, hs⟩ : ∃ s : ℝ, s = e - 1 := ⟨_, rfl⟩
            obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = η / 4 := ⟨_, rfl⟩
            obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = η ^ 3 / 192 := ⟨_, rfl⟩
            have hβ0 : 0 < β := by rw [hβ]; positivity
            have hθ0 : 0 < θ := by rw [hθ]; positivity
            have hβ1 : β ≤ 1/4 := by rw [hβ]; linarith
            have hθβ : θ ≤ β / 48 := by
              rw [hθ, hβ]; have : η ^ 3 ≤ η := by nlinarith [pow_le_one₀ hη0.le hη1 (n := 2)]
              linarith
            have hs1 : 1.718 < s := by rw [hs]; linarith
            have hs2 : s < 1.719 := by rw [hs]; linarith
            obtain ⟨pa, hpa⟩ : ∃ pa : ℝ, pa = (1 - θ) + (s - β) := ⟨_, rfl⟩
            obtain ⟨pg, hpg⟩ : ∃ pg : ℝ, pg = θ + β := ⟨_, rfl⟩
            have hpa0 : 2 < pa := by rw [hpa]; linarith
            have hpg0 : 0 < pg := by rw [hpg]; linarith
            obtain ⟨α, hα⟩ : ∃ α : ℝ, α = (s - β) * pg ^ 2 / (β * pa ^ 2) := ⟨_, rfl⟩
            obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = θ * pa ^ 2 / ((1 - θ) * pg ^ 2) := ⟨_, rfl⟩
            have hα0 : 0 < α := by
              rw [hα]; apply div_pos; apply mul_pos; linarith; positivity; positivity
            have hε0 : 0 < ε := by
              rw [hε]; apply div_pos; positivity; apply mul_pos; linarith; positivity
            have hFA : α * (β / pg ^ 2) = (s - β) / pa ^ 2 := by
              rw [hα]; field_simp
            have hFG : ε * ((1 - θ) / pa ^ 2) = θ / pg ^ 2 := by
              rw [hε]; have : (1 - θ) ≠ 0 := by linarith
              field_simp
            -- tangent line bound for y ↦ y/(y+c)
            have T : ∀ y y0 k : ℝ, 0 ≤ y → 0 ≤ y0 → 0 < k →
                y / (y + k) ≤ y0 / (y0 + k) + (k / (y0 + k) ^ 2) * (y - y0) := by
              intro y y0 k hy hy0 hk
              have h1 : 0 < y + k := by linarith
              have h2 : 0 < y0 + k := by linarith
              have key : y / (y + k) = y0 / (y0 + k) + (k / (y0 + k) ^ 2) * (y - y0)
                  - k * (y - y0) ^ 2 / ((y + k) * (y0 + k) ^ 2) := by
                field_simp; ring
              have : 0 ≤ k * (y - y0) ^ 2 / ((y + k) * (y0 + k) ^ 2) := by positivity
              linarith
            have htp : ∀ (b' : Fin 2 → Fin 2 → ℝ), (∀ i j, 0 ≤ b' i j) →
                ∀ i j, tpAlloc 0 b' i j = b' i j / (b' 0 j + b' 1 j) := by
              intro b' hb' i j
              unfold tpAlloc effBid
              simp only [hb', ite_true, Fin.sum_univ_two]
              split_ifs with h
              · rfl
              · have : b' i j = 0 := le_antisymm (not_lt.mp h) (hb' i j)
                simp [this]


            obtain ⟨UA, hUA⟩ : ∃ UA : ℝ, UA = (1 - θ) / pa + α * (θ / pg) := ⟨_, rfl⟩
            obtain ⟨UG, hUG⟩ : ∃ UG : ℝ, UG = ε * ((s - β) / pa) + β / pg := ⟨_, rfl⟩
            have hUA0 : 0 < UA := by
              rw [hUA]; have : 0 < (1 - θ) / pa := div_pos (by linarith) (by linarith)
              have : 0 < α * (θ / pg) := by positivity
              linarith
            have hUG0 : 0 < UG := by
              rw [hUG]; have : 0 < ε * ((s - β) / pa) := mul_pos hε0 (div_pos (by linarith) (by linarith))
              have : 0 < β / pg := by positivity
              linarith
            have hUAle : UA ≤ 1 / e + η := by
              clear hc hηc T hFG he hε hε0 hUG hUG0 hUA0 ε UG
              have hpe : 1 / pa - 1 / e = (θ + β) / (e * pa) := by
                rw [div_sub_div _ _ (by linarith) hepos.ne', hpa, hs]; ring_nf
              have hep : 5 ≤ e * pa := by
                have := mul_le_mul (show (2.7:ℝ) ≤ e by linarith) hpa0.le (by norm_num) hepos.le
                linarith only [this]
              have h5 : (θ + β) / (e * pa) ≤ (θ + β) / 5 :=
                div_le_div_of_nonneg_left (by linarith only [hθ0, hβ0]) (by norm_num) hep
              have h6 : (1 - θ) / pa ≤ 1 / pa :=
                div_le_div_of_nonneg_right (by linarith only [hθ0]) (by linarith only [hpa0])
              have hαle : α ≤ 2 * β := by
                have hden : 0 < β * pa ^ 2 := mul_pos hβ0 (pow_pos (by linarith only [hpa0]) 2)
                rw [hα, div_le_iff₀ hden]
                have hpgle : pg ≤ 49 / 48 * β := by rw [hpg]; linarith only [hθβ]
                have hpg2 : pg ^ 2 ≤ (49 / 48 * β) ^ 2 := pow_le_pow_left₀ hpg0.le hpgle 2
                have hpa2 : 2 * 2 ≤ pa * pa := mul_le_mul hpa0.le hpa0.le (by norm_num) (by linarith only [hpa0])
                have h8 : (s - β) * pg ^ 2 ≤ 2 * (49 / 48 * β) ^ 2 :=
                  mul_le_mul (by linarith only [hs2, hβ0]) hpg2 (sq_nonneg _) (by norm_num)
                have h9 : β ^ 2 * (2 * 2) ≤ β ^ 2 * (pa * pa) := mul_le_mul_of_nonneg_left hpa2 (sq_nonneg β)
                have h10 : 0 ≤ β ^ 2 := sq_nonneg β
                have e1 : 2 * β * (β * pa ^ 2) = 2 * (β ^ 2 * (pa * pa)) := by ring
                have e2 : 2 * (49 / 48 * β) ^ 2 = 2 * (2401 / 2304) * β ^ 2 := by ring
                rw [e1]; rw [e2] at h8
                linarith only [h8, h9, h10]
              have hθpg : θ / pg ≤ 1 / 48 := by
                rw [div_le_iff₀ hpg0, hpg]; linarith only [hθβ, hβ0]
              have h7 : α * (θ / pg) ≤ 2 * β * (1 / 48) :=
                mul_le_mul hαle hθpg (div_pos hθ0 hpg0).le (by linarith only [hβ0])
              rw [hUA]
              linarith only [hpe, h5, h6, h7, hβ, hθβ, hβ0]
            have hUGle : UG ≤ 1 + η := by
              clear hc hηc T hFA he hα hα0 hUA hUA0 hUAle α UA
              have h1 : β / pg ≤ 1 := by
                rw [div_le_one hpg0, hpg]; linarith only [hθ0]
              have h2 : (s - β) / pa ≤ 1 := by
                rw [div_le_one (show (0:ℝ) < pa by linarith only [hpa0]), hpa]; linarith only [hθβ, hβ1]
              have hθeq : θ = η * β ^ 2 / 12 := by rw [hθ, hβ]; ring
              have h3 : ε ≤ η := by
                have hden : 0 < (1 - θ) * pg ^ 2 :=
                  mul_pos (by linarith only [hθβ, hβ1]) (pow_pos hpg0 2)
                rw [hε, div_le_iff₀ hden]
                have hpale : pa ≤ 2.72 := by rw [hpa, hs]; linarith only [he2, hθ0, hβ0]
                have A1 : pa * pa ≤ 2.72 * 2.72 :=
                  mul_le_mul hpale hpale (by linarith only [hpa0]) (by norm_num)
                have A2 : β ^ 2 * (pa * pa) ≤ β ^ 2 * (2.72 * 2.72) := mul_le_mul_of_nonneg_left A1 (sq_nonneg β)
                have A3 : β ^ 2 ≤ pg ^ 2 := pow_le_pow_left₀ hβ0.le (by rw [hpg]; linarith only [hθ0]) 2
                have A4 : (99 / 100) * β ^ 2 ≤ (1 - θ) * pg ^ 2 :=
                  mul_le_mul (by linarith only [hθβ, hβ1]) A3 (sq_nonneg β) (by linarith only [hθβ, hβ1])
                have A5 : β ^ 2 * (pa * pa) / 12 ≤ (1 - θ) * pg ^ 2 := by
                  have : 0 ≤ β ^ 2 := sq_nonneg β
                  linarith only [A2, A4, this]
                have A6 := mul_le_mul_of_nonneg_left A5 hη0.le
                have e1 : θ * pa ^ 2 = η * (β ^ 2 * (pa * pa) / 12) := by rw [hθeq]; ring
                rw [e1]; exact A6
              have h4 : ε * ((s - β) / pa) ≤ η * 1 :=
                mul_le_mul h3 h2 (div_pos (by linarith only [hs1, hβ1]) (by linarith only [hpa0])).le hη0.le
              rw [hUG]; linarith only [h1, h4]
            have hprod : UA * UG ^ s ≤ 1 / e + 7 * η := by
              have g1 : UG ^ s ≤ (1 + η) ^ s := Real.rpow_le_rpow hUG0.le hUGle (by linarith only [hs1])
              have g2 : (1 + η) ^ s ≤ (1 + η) ^ (2 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith only [hη0]) (by linarith only [hs2])
              rw [Real.rpow_two] at g2
              have hq0 : 0 < 1 / e := one_div_pos.mpr hepos
              have g3 : UA * UG ^ s ≤ (1 / e + η) * (1 + η) ^ 2 :=
                mul_le_mul hUAle (g1.trans g2) (Real.rpow_nonneg hUG0.le _)
                  (by linarith only [hq0, hη0])
              have hq : 1 / e < 1 / 2 := one_div_lt_one_div_of_lt (by norm_num) (by linarith only [he1])
              obtain ⟨q, hqd⟩ : ∃ q, q = 1 / e := ⟨_, rfl⟩
              rw [← hqd] at g3 hq hq0 ⊢
              have k1 : η * η ≤ η * 1 := mul_le_mul_of_nonneg_left hη1 hη0.le
              have k2 : η * η * η ≤ η * η * 1 := mul_le_mul_of_nonneg_left hη1 (mul_nonneg hη0.le hη0.le)
              have k3 : q * η ≤ 1 / 2 * η := mul_le_mul_of_nonneg_right hq.le hη0.le
              have k4 : q * (η * η) ≤ 1 / 2 * (η * η) :=
                mul_le_mul_of_nonneg_right hq.le (mul_nonneg hη0.le hη0.le)
              have e1 : (q + η) * (1 + η) ^ 2 = q + 2 * (q * η) + q * (η * η) + η + 2 * (η * η) + η * η * η := by ring
              rw [e1] at g3
              linarith only [g3, k1, k2, k3, k4, hη0]
            have hb0 : ∀ i j, 0 ≤ (![![1 - θ, θ], ![s - β, β]] : Fin 2 → Fin 2 → ℝ) i j := by
              intro i j; fin_cases i <;> fin_cases j <;> simp <;> linarith
            refine ⟨2, 2, ⟨![![1, α], ![ε, 1]], ![1, s]⟩, ⟨by norm_num, ?_, ?_⟩, ?_,
              ![![1 - θ, θ], ![s - β, β]], ⟨?_, ?_⟩, ?_, ![![1, 0], ![0, 1]], ?_, ?_⟩
            · intro i j; fin_cases i <;> fin_cases j <;> simp <;> linarith
            · intro i; fin_cases i <;> simp <;> linarith
            · intro j; refine ⟨0, 1, by decide, ?_, ?_⟩ <;> fin_cases j <;> simp <;> linarith
            · intro i; fin_cases i <;> simp [Strategy, Fin.forall_fin_two] <;> (repeat' apply And.intro) <;> linarith
            · intro i b' hb'
              obtain ⟨hb'1, hb'2⟩ := hb'
              have hnn : ∀ i' j, 0 ≤ Function.update (![![1 - θ, θ], ![s - β, β]] : Fin 2 → Fin 2 → ℝ) i b' i' j := by
                intro i' j
                by_cases h : i' = i
                · subst h; simp [(hb'1 j).1]
                · rw [Function.update_of_ne h]; exact hb0 i' j
              simp only [linU, Fin.sum_univ_two, htp _ hnn, htp _ hb0]
              simp only [Fin.sum_univ_two] at hb'2
              fin_cases i
              · simp at hb'2 ⊢
                have h0 := (hb'1 0).1
                have h1 := (hb'1 1).1
                have T1 : b' 0 / (b' 0 + (s - β)) ≤ (1 - θ) / pa + ((s - β) / pa ^ 2) * (b' 0 - (1 - θ)) := by
                  have := T (b' 0) (1 - θ) (s - β) h0 (by linarith) (by linarith)
                  rw [← hpa] at this; exact this
                have T2 : b' 1 / (b' 1 + β) ≤ θ / pg + (β / pg ^ 2) * (b' 1 - θ) := by
                  have := T (b' 1) θ β h1 hθ0.le hβ0
                  rw [← hpg] at this; exact this
                rw [← hpa, ← hpg]
                have h2 := mul_le_mul_of_nonneg_left T2 hα0.le
                have h3 : α * (θ / pg + (β / pg ^ 2) * (b' 1 - θ)) = α * (θ / pg) + (s - β) / pa ^ 2 * (b' 1 - θ) := by
                  rw [mul_add, ← mul_assoc, hFA]
                have h4 : (s - β) / pa ^ 2 * (b' 0 - (1 - θ)) + (s - β) / pa ^ 2 * (b' 1 - θ) = 0 := by
                  rw [← mul_add]
                  have : b' 0 - (1 - θ) + (b' 1 - θ) = 0 := by linarith
                  rw [this, mul_zero]
                linarith
              · simp at hb'2 ⊢
                have h0 := (hb'1 0).1
                have h1 := (hb'1 1).1
                have T1 : b' 0 / (1 - θ + b' 0) ≤ (s - β) / pa + ((1 - θ) / pa ^ 2) * (b' 0 - (s - β)) := by
                  have := T (b' 0) (s - β) (1 - θ) h0 (by linarith) (by linarith)
                  rw [add_comm (b' 0), show s - β + (1 - θ) = pa by rw [hpa]; ring] at this; exact this
                have T2 : b' 1 / (θ + b' 1) ≤ β / pg + (θ / pg ^ 2) * (b' 1 - β) := by
                  have := T (b' 1) β θ h1 hβ0.le hθ0
                  rw [add_comm (b' 1), show β + θ = pg by rw [hpg]; ring] at this; exact this
                rw [← hpa, ← hpg]
                have h2 := mul_le_mul_of_nonneg_left T1 hε0.le
                have h3 : ε * ((s - β) / pa + ((1 - θ) / pa ^ 2) * (b' 0 - (s - β))) = ε * ((s - β) / pa) + θ / pg ^ 2 * (b' 0 - (s - β)) := by
                  rw [mul_add, ← mul_assoc, hFG]
                have h4 : θ / pg ^ 2 * (b' 0 - (s - β)) + θ / pg ^ 2 * (b' 1 - β) = 0 := by
                  rw [← mul_add]
                  have : b' 0 - (s - β) + (b' 1 - β) = 0 := by linarith
                  rw [this, mul_zero]
                linarith
            · simp only [NSWU, linU, Fin.sum_univ_two, Fin.prod_univ_two, htp _ hb0, totalBudget]
              simp
              rw [← hpa, ← hpg, ← hUA, ← hUG]
              exact Real.rpow_pos_of_pos (mul_pos hUA0 (Real.rpow_pos_of_pos hUG0 _)) _
            · refine ⟨?_, ?_⟩
              · intro i j; fin_cases i <;> fin_cases j <;> simp
              · intro j; fin_cases j <;> simp
            · simp only [NSWU, linU, Fin.sum_univ_two, Fin.prod_univ_two, htp _ hb0, totalBudget]
              simp
              rw [← hpa, ← hpg, ← hUA, ← hUG]
              have : (1 + s)⁻¹ = 1 / e := by rw [hs]; ring
              rw [this]
              exact hηc _ (mul_nonneg hUA0.le (Real.rpow_nonneg hUG0.le _)) hprod
