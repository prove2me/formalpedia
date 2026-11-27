-- Prove2me | solution 1 for RobustPrefLearn.MTP.Supplement.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:22:21.573906+00:00
-- url     : https://prove2.me/submissions/186ae129-c38d-48ec-93e1-7cbceb9a06b4

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_Supplement_SubsetAccuracy

open scoped ENNReal

open RobustPrefLearn
open RobustPrefLearn.MTP
open RobustPrefLearn.MTP.Supplement

/-- Theorem 2, p.14. One δ-indexed family, accurate on every finite specified
subset, with finite expectations and the full-model information upper bound.
The family is selected before δ and f. Empty and single-top subsets are allowed. -/
theorem solution (K : ℕ) (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (MF : Set (Pref K)) (hfinite : MF.Finite) (hsub : MF ⊆ Mp p) :
    ∃ fam : ℝ → Policy K, AccurateOn MF fam ∧
      (∀ δ ∈ Set.Ioo (0 : ℝ) 1, ∀ f ∈ MF, expTau (fam δ) f < ⊤) ∧
      (∀ f ∈ MF, rate fam f ≤ (Istar p f)⁻¹) := by
        classical
        have hr1 : ∀ (M κ n b : ℝ) (T : ℕ), 0 ≤ M → 0 < κ → 0 < n → b / κ ≤ T →
            (M * Real.exp (1 / n^3 * b)) * Real.exp (-(1 / n^3 * κ)) ^ T * (1 + 1 / (1 / n^3 * κ)) ≤ M + M / κ * n^3 := by
          intro M κ n b T hM hκ hn hT
          have hn3 : 0 < n^3 := pow_pos hn 3
          have e : M * (1 + 1 / (1 / n^3 * κ)) = M + M / κ * n^3 := by field_simp
          have h2 : 0 ≤ M * (1 + 1 / (1 / n^3 * κ)) := mul_nonneg hM (add_nonneg zero_le_one (one_div_nonneg.2 (mul_nonneg (one_div_nonneg.2 hn3.le) hκ.le)))
          have h1 : Real.exp (1 / n^3 * b) * Real.exp (-(1 / n^3 * κ)) ^ T ≤ 1 := by
            rw [← Real.exp_nat_mul, ← Real.exp_add]
            refine Real.exp_le_one_iff.2 ?_
            have a := mul_le_mul_of_nonneg_left ((div_le_iff₀ hκ).1 hT) (one_div_nonneg.2 hn3.le)
            linarith only [a]
          calc _ = (Real.exp (1 / n^3 * b) * Real.exp (-(1 / n^3 * κ)) ^ T) * (M * (1 + 1 / (1 / n^3 * κ))) := by ring
            _ ≤ 1 * (M * (1 + 1 / (1 / n^3 * κ))) := mul_le_mul_of_nonneg_right h1 h2
            _ = _ := by rw [one_mul, e]
        have hr2 : ∀ (d n : ℝ), 0 < d → 0 < n → Real.exp (-n) * (1 + 1 / (1 / n^3 * (d / (2 * n)))) ≤ 1 + 48 / d := by
          intro d n hd hn
          have e1 : (1 + 1 / (1 / n^3 * (d / (2 * n)))) = 1 + 2 * n^4 / d := by field_simp
          have h24 := Real.pow_div_factorial_le_exp n hn.le 4
          have hf : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
          rw [hf] at h24
          rw [e1, Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]
          have h1 : 1 ≤ Real.exp n := Real.one_le_exp hn.le
          have h2 : 2 * n^4 / d ≤ Real.exp n * (48 / d) := by
            rw [mul_div_assoc', div_le_div_iff_of_pos_right hd]
            linarith only [h24]
          linarith only [h1, h2]
        have hr3 : ∀ (M B d γ n b : ℝ) (N : ℕ), ((N^2 : ℕ) : ℝ) = n^2 → 0 ≤ M → 0 ≤ B → 0 < d → 1 ≤ n → b ≤ n^4 → 2 ≤ n * γ →
            (M * Real.exp (1 / n^3 * b)) * (Real.exp (1 / n^3 * B * n^2) * (M * Real.exp (-γ) ^ (N^2))) * (1 + 1 / (1 / n^3 * (d / (2 * n)))) ≤ M^2 * Real.exp B * (1 + 48 / d) := by
          intro M B d γ n b N hN hM hB hd hn hb hγ
          have hn0 : 0 < n := one_pos.trans_le hn
          have hn3 : 0 < n^3 := pow_pos hn0 3
          have e2 : (M * Real.exp (1 / n^3 * b)) * (Real.exp (1 / n^3 * B * n^2) * (M * Real.exp (-γ) ^ (N^2))) = M^2 * Real.exp (1 / n^3 * b + 1 / n^3 * B * n^2 + n^2 * (-γ)) := by
            rw [← Real.exp_nat_mul, hN, Real.exp_add, Real.exp_add]; ring
          have a1 : 1 / n^3 * b ≤ n := by
            rw [one_div, inv_mul_le_iff₀ hn3]
            have a : n^3 * n = n^4 := by ring
            rw [a]; exact hb
          have a2 : 1 / n^3 * B * n^2 ≤ B := by
            have : 1 / n^3 * B * n^2 = B / n := by field_simp
            rw [this]
            exact div_le_self hB hn
          have a3 := mul_le_mul_of_nonneg_left hγ hn0.le
          have e3 : 1 / n^3 * b + 1 / n^3 * B * n^2 + n^2 * (-γ) ≤ B + -n := by linarith only [a1, a2, a3]
          have h5 : 0 ≤ 1 + 1 / (1 / n^3 * (d / (2 * n))) := add_nonneg zero_le_one (one_div_nonneg.2 (mul_nonneg (one_div_nonneg.2 hn3.le) (div_nonneg hd.le (mul_nonneg zero_le_two hn0.le))))
          have hM2 : 0 ≤ M^2 := sq_nonneg M
          rw [e2]
          calc _ ≤ M^2 * Real.exp (B + -n) * (1 + 1 / (1 / n^3 * (d / (2 * n)))) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 e3) hM2) h5
            _ = M^2 * Real.exp B * (Real.exp (-n) * (1 + 1 / (1 / n^3 * (d / (2 * n))))) := by rw [Real.exp_add]; ring
            _ ≤ _ := mul_le_mul_of_nonneg_left (hr2 d n hd hn0) (mul_nonneg hM2 (Real.exp_pos B).le)
        have hr4 : ∀ (n B d κ I : ℝ), 1 ≤ n → 1 ≤ B → 0 < d → B ≤ n → B^2 ≤ n * d → 2 * B^2 ≤ n * d → B^2 + I ≤ n * (I - κ) →
            (1 / n^3) * B ≤ 1 ∧ (1 / n^3) * B^2 ≤ d ∧ d / (2 * n) + (1 / n^3) * B^2 ≤ (1 / n) * d ∧ κ + (1 / n^3) * B^2 ≤ (1 - 1 / n) * I := by
          intro n B d κ I hn hB hd h1 h2 h3 h4
          have hn0 : 0 < n := one_pos.trans_le hn
          have hn3 : 0 < n^3 := pow_pos hn0 3
          have hnn3 : n ≤ n^3 := le_self_pow₀ hn (by norm_num)
          have hn23 : n^2 ≤ n^3 := pow_le_pow_right₀ hn (by norm_num)
          have i1 : 1 / n^3 ≤ 1 / n := one_div_le_one_div_of_le hn0 hnn3
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [one_div, inv_mul_le_iff₀ hn3]; linarith only [h1, hnn3]
          · rw [one_div, inv_mul_le_iff₀ hn3]
            have a := mul_le_mul_of_nonneg_right hnn3 hd.le
            linarith only [a, h2]
          · have : (1 / n^3) * B^2 ≤ d / (2 * n) := by
              rw [one_div, inv_mul_le_iff₀ hn3, mul_div_assoc', le_div_iff₀ (mul_pos two_pos hn0)]
              have a := mul_le_mul_of_nonneg_right h3 hn0.le
              have b := mul_le_mul_of_nonneg_right hn23 hd.le
              linarith only [a, b]
            have e : (1 / n) * d = d / (2 * n) + d / (2 * n) := by field_simp; norm_num
            rw [e]; linarith only [this]
          · have a1 : (1 / n^3) * B^2 ≤ (1/n) * B^2 := mul_le_mul_of_nonneg_right i1 (sq_nonneg B)
            have a2 : (1/n) * (B^2 + I) ≤ I - κ := by
              rw [one_div, inv_mul_le_iff₀ hn0]; exact h4
            linarith only [a1, a2]
        have hr5 : ∀ (n y T M κ r L Q : ℝ), 1 ≤ y → y ≤ n → n ≤ y + 2 → 0 ≤ M → 0 < κ → 0 ≤ Q → 0 ≤ L → 0 < r → T ≤ y^4 / κ + 1 →
            27 * (2 + M + M / κ + Q) + L / r ≤ y * (1 / r - 1 / κ) → n^2 + T + (M + M / κ * n^3 + Q) ≤ (y^4 - L) / r := by
          intro n y T M κ r L Q hy hyn hny hM hκ hQ hL hr hT hY
          have hn : 1 ≤ n := hy.trans hyn
          have hn31 : 1 ≤ n^3 := one_le_pow₀ hn
          have hn23 : n^2 ≤ n^3 := pow_le_pow_right₀ hn (by norm_num)
          have hy3 : 1 ≤ y^3 := one_le_pow₀ hy
          have hMκ : 0 ≤ M / κ := div_nonneg hM hκ.le
          have hLr : 0 ≤ L / r := div_nonneg hL hr.le
          have t4 : n^3 ≤ 27 * y^3 := by
            have h1 : n^3 ≤ (3*y)^3 := pow_le_pow_left₀ (zero_le_one.trans hn) (by linarith only [hy, hny]) 3
            linarith only [h1]
          have hC : 0 ≤ 2 + M + M / κ + Q := by linarith only [hM, hMκ, hQ]
          have b1 := mul_le_mul_of_nonneg_left hn31 hM
          have b2 := mul_le_mul_of_nonneg_left hn31 hQ
          have t3 : n^2 + T + (M + M / κ * n^3 + Q) ≤ y^4 / κ + (2 + M + M / κ + Q) * n^3 := by
            linarith only [b1, b2, hT, hn23, hn31]
          have t6 := mul_le_mul_of_nonneg_left t4 hC
          have h1 := mul_le_mul_of_nonneg_right hY (zero_le_one.trans hy3)
          have b3 := mul_le_mul_of_nonneg_left hy3 hLr
          have h2 : (y^4 - L) / r = y * (1/r) * y^3 - L / r := by ring
          have h3 : y^4 / κ = y * (1 / κ) * y^3 := by ring
          rw [h2]; rw [h3] at t3
          linarith only [t3, t6, h1, b3]
        have hreal : ∀ (M B d γ κ I r L : ℝ), 1 ≤ M → 1 ≤ B → 0 < d → 0 < γ → 0 < r → r < κ → κ < I → 0 ≤ L → ∃ Y : ℝ, ∀ y : ℝ, Y ≤ y → ∀ (N T : ℕ),
            y ≤ N → (N : ℝ) ≤ y + 2 → T = ⌈y^4 / κ⌉₊ → (1 / (N:ℝ)^3) * B ≤ 1 ∧ (1 / (N:ℝ)^3) * B^2 ≤ d ∧ d / (2 * N) + (1 / (N:ℝ)^3) * B^2 ≤ (1 / N) * d ∧
            κ + (1 / (N:ℝ)^3) * B^2 ≤ (1 - 1 / N) * I ∧
            ((N^2 : ℕ) : ℝ) + T + ((M * Real.exp (1 / (N:ℝ)^3 * y^4)) * Real.exp (-(1 / (N:ℝ)^3 * κ)) ^ T * (1 + 1 / (1 / (N:ℝ)^3 * κ)) +
               (M * Real.exp (1 / (N:ℝ)^3 * y^4)) * (Real.exp (1 / (N:ℝ)^3 * B * (N^2 : ℕ)) * (M * Real.exp (-γ) ^ (N^2))) * (1 + 1 / (1 / (N:ℝ)^3 * (d / (2 * N))))) ≤ (y^4 - L) / r := by
          intro M B d γ κ I r L hM hB hd hγ hr hrκ hκI hL
          have hκ : 0 < κ := hr.trans hrκ
          have hM0 : 0 ≤ M := zero_le_one.trans hM
          have hB0 : 0 ≤ B := zero_le_one.trans hB
          have hQ : 0 ≤ M^2 * Real.exp B * (1 + 48 / d) := by positivity
          have ha : 0 < 1 / r - 1 / κ := sub_pos.2 (one_div_lt_one_div_of_lt hr hrκ)
          have hIκ : 0 < I - κ := sub_pos.2 hκI
          refine ⟨max (max (max 1 B) (max (B^2 / d) (2 * B^2 / d))) (max (max ((B^2 + I) / (I - κ)) (2 / γ)) ((27 * (2 + M + M / κ + M^2 * Real.exp B * (1 + 48 / d)) + L / r) / (1 / r - 1 / κ))), ?_⟩
          intro y hy N T hyN hNy hT
          simp only [max_le_iff] at hy
          obtain ⟨⟨⟨y1, y2⟩, y3, y4⟩, ⟨y5, y6⟩, y7⟩ := hy
          have hn1 : 1 ≤ (N:ℝ) := y1.trans hyN
          have hNn : ((N^2 : ℕ) : ℝ) = (N:ℝ)^2 := Nat.cast_pow N 2
          obtain ⟨c1, c2, c3, c4⟩ := hr4 N B d κ I hn1 hB hd (y2.trans hyN) ((div_le_iff₀ hd).1 (y3.trans hyN)) ((div_le_iff₀ hd).1 (y4.trans hyN)) ((div_le_iff₀ hIκ).1 (y5.trans hyN))
          refine ⟨c1, c2, c3, c4, ?_⟩
          have hy0 : 0 ≤ y := zero_le_one.trans y1
          have hy4 : 0 ≤ y^4 / κ := div_nonneg (pow_nonneg hy0 4) hκ.le
          have t1 := hr1 M κ N (y^4) T hM0 hκ (one_pos.trans_le hn1) (by rw [hT]; exact Nat.le_ceil _)
          have t2 := hr3 M B d γ N (y^4) N hNn hM0 hB0 hd hn1 (pow_le_pow_left₀ hy0 hyN 4) ((div_le_iff₀ hγ).1 (y6.trans hyN))
          have t3 := hr5 N y T M κ r L _ y1 hyN hNy hM0 hκ hQ hL hr (by rw [hT]; exact (Nat.ceil_lt_add_one hy4).le) ((div_le_iff₀ ha).1 y7)
          rw [hNn]
          exact (add_le_add_right (add_le_add t1 t2) _).trans t3
        have hnum1 : ∀ d B : ℝ, 0 < d → d ≤ 1 → 1 ≤ B → d / (2 * B^2) * B ≤ 1 ∧ d / (2 * B^2) * (d / 2) = d^2 / (4 * B^2) ∧ d / 2 + d / (2 * B^2) * B^2 = d := by
          intro d B hd hd1 hB
          have hB0 : 0 < B := one_pos.trans_le hB
          refine ⟨?_, ?_, ?_⟩
          · rw [div_mul_eq_mul_div, div_le_one (mul_pos two_pos (pow_pos hB0 2))]
            have a1 := mul_le_mul_of_nonneg_right hd1 hB0.le
            have a2 := mul_le_mul_of_nonneg_right hB hB0.le
            linarith only [a1, a2, hB0]
          · field_simp; norm_num
          · field_simp; norm_num
        have hnum2 : ∀ d B ε : ℝ, 0 < d → d ≤ 1 → 1 ≤ B → 0 < ε → ε ≤ 1 → 0 < (ε * d) / (2 * B^2) ∧ (ε * d) / (2 * B^2) * B^2 = (ε * d) / 2 ∧ (ε * d) / (2 * B^2) * B ≤ 1 ∧ (ε * d) / (2 * B^2) * B^2 ≤ d ∧ 0 < (ε * d) / 2 := by
          intro d B ε hd hd1 hB hε hε1
          have hB0 : 0 < B := one_pos.trans_le hB
          have h0 : 0 < ε * d := mul_pos hε hd
          have h1 : ε * d ≤ d := mul_le_of_le_one_left hd.le hε1
          have e : (ε * d) / (2 * B^2) * B^2 = (ε * d) / 2 := by field_simp
          refine ⟨div_pos h0 (mul_pos two_pos (pow_pos hB0 2)), e, (hnum1 (ε * d) B h0 (h1.trans hd1) hB).1, ?_, half_pos h0⟩
          rw [e]; linarith only [h0, h1]
        have hfnn : ∀ (p : ℝ) (f : Pref K), f ∈ (Mp p : Set (Pref K)) → ∀ S X, 0 ≤ f S X := by
          intro p f hf S X
          by_cases hX : X ∈ S.1
          · exact ((hf.1 S X).1 hX).le
          · exact ((hf.1 S X).2 hX).ge
        have hfsum : ∀ (p : ℝ) (f : Pref K), f ∈ (Mp p : Set (Pref K)) → ∀ S, ∑ X, f S X = 1 := by
          intro p f hf S
          rw [← hf.2.1 S]
          symm
          refine Finset.sum_subset (Finset.subset_univ _) fun X _ hX => (hf.1 S X).2 hX
        have hpath : ∀ (p : ℝ) (π : Policy K) (f : Pref K), f ∈ (Mp p : Set (Pref K)) → ∀ h : List (Step K),
           pathProb π f h = pathProb π (fun _ _ => 1) h * ENNReal.ofReal ((h.map (fun x => f x.1 x.2)).prod) := by
          intro p π f hf h
          induction h with
          | nil => simp [pathProb]
          | cons x h ih =>
            obtain ⟨S, X⟩ := x
            simp only [pathProb, List.map_cons, List.prod_cons]
            rw [ih, ENNReal.ofReal_mul (hfnn p f hf S X)]
            simp only [ENNReal.ofReal_one, mul_one]
            ring
        have hliknn : ∀ (p : ℝ) (f : Pref K), f ∈ (Mp p : Set (Pref K)) → ∀ h : List (Step K), 0 ≤ (h.map (fun x => f x.1 x.2)).prod := by
          intro p f hf h
          apply List.prod_nonneg
          intro a ha
          obtain ⟨x, _, rfl⟩ := List.mem_map.1 ha
          exact hfnn p f hf _ _
        have hlikpos : ∀ (p : ℝ) (π : Policy K) (f : Pref K), f ∈ (Mp p : Set (Pref K)) → ∀ h : List (Step K), pathProb π f h ≠ 0 →
            0 < (h.map (fun x => f x.1 x.2)).prod := by
          intro p π f hf h h0
          rw [hpath p π f hf] at h0
          have := right_ne_zero_of_mul h0
          simpa using this
        have hlikratio : ∀ (p : ℝ) (f g : Pref K), f ∈ (Mp p : Set (Pref K)) → g ∈ (Mp p : Set (Pref K)) → ∀ h : List (Step K),
            0 < (h.map (fun x => f x.1 x.2)).prod → (h.map (fun x => g x.1 x.2)).prod = (h.map (fun x => f x.1 x.2)).prod *
              Real.exp (-(h.map (fun x => Real.log (f x.1 x.2 / g x.1 x.2))).sum) := by
          intro p f g hf hg h
          induction h with
          | nil => simp
          | cons x h ih =>
            intro h0
            simp only [List.map_cons, List.prod_cons, List.sum_cons] at *
            have hx : f x.1 x.2 ≠ 0 := by
              intro h; rw [h] at h0; simp at h0
            have hfx : 0 < f x.1 x.2 := lt_of_le_of_ne (hfnn p f hf _ _) (Ne.symm hx)
            have hmem : x.2 ∈ x.1.1 := by
              by_contra hc
              exact hx ((hf.1 _ _).2 hc)
            have hgx : 0 < g x.1 x.2 := (hg.1 _ _).1 hmem
            have hp : 0 < (h.map (fun x => f x.1 x.2)).prod := (pos_iff_pos_of_mul_pos h0).1 hfx
            rw [ih hp, neg_add, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log (by positivity)]
            field_simp
        have hpathle : ∀ (p : ℝ) (π : Policy K) (f g : Pref K), f ∈ (Mp p : Set (Pref K)) → g ∈ (Mp p : Set (Pref K)) → ∀ (h : List (Step K)) (c : ℝ), 0 ≤ c →
            (h.map (fun x => f x.1 x.2)).prod ≤ c * (h.map (fun x => g x.1 x.2)).prod → pathProb π f h ≤ ENNReal.ofReal c * pathProb π g h := by
          intro p π f g hf hg h c hc H
          rw [hpath p π f hf, hpath p π g hg]
          calc _ ≤ pathProb π (fun _ _ => 1) h * ENNReal.ofReal (c * (h.map (fun x => g x.1 x.2)).prod) := by gcongr
            _ = _ := by rw [ENNReal.ofReal_mul hc]; ring
        have hDSnn : ∀ (p : ℝ) (f g : Pref K), f ∈ (Mp p : Set (Pref K)) → g ∈ (Mp p : Set (Pref K)) → ∀ S,
            0 ≤ DS_ f g S ∧ (DS_ f g S = 0 → f S = g S) := by
          intro p f g hf hg S
          have hpt : ∀ X ∈ S.1, f S X - g S X ≤ f S X * Real.log (f S X / g S X) ∧ (f S X ≠ g S X → f S X - g S X < f S X * Real.log (f S X / g S X)) := by
            intro X hX
            have h1 := (hf.1 S X).1 hX
            have h2 := (hg.1 S X).1 hX
            have e : Real.log (f S X / g S X) = - Real.log (g S X / f S X) := by
              rw [← Real.log_inv, inv_div]
            have e2 : f S X * (g S X / f S X - 1) = g S X - f S X := by field_simp
            constructor
            · have := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos h2 h1)) h1.le
              rw [e]; linarith
            · intro hne
              have : g S X / f S X ≠ 1 := by
                intro h; exact hne ((div_eq_one_iff_eq h1.ne').1 h).symm
              have := mul_lt_mul_of_pos_left (Real.log_lt_sub_one_of_pos (div_pos h2 h1) this) h1
              rw [e]; linarith
          have hz : ∑ X ∈ S.1, (f S X - g S X) = 0 := by
            rw [Finset.sum_sub_distrib, hf.2.1, hg.2.1, sub_self]
          constructor
          · rw [← hz]; exact Finset.sum_le_sum fun X hX => (hpt X hX).1
          · intro h0
            funext X
            by_cases hX : X ∈ S.1
            · by_contra hne
              have : ∑ X ∈ S.1, (f S X - g S X) < DS_ f g S := Finset.sum_lt_sum (fun X hX => (hpt X hX).1) ⟨X, hX, (hpt X hX).2 hne⟩
              linarith
            · rw [(hf.1 S X).2 hX, (hg.1 S X).2 hX]
        have hstepKL : ∀ (p : ℝ) (f g : Pref K) (B s : ℝ) (w : DS K → ℝ), f ∈ (Mp p : Set (Pref K)) → g ∈ (Mp p : Set (Pref K)) →
            (∀ S X, |Real.log (f S X / g S X)| ≤ B) → 0 ≤ s → s * B ≤ 1 → (∀ S, 0 ≤ w S) → ∑ S, w S = 1 →
            ∑ x : Step K, ENNReal.ofReal (w x.1) * ENNReal.ofReal (f x.1 x.2) * ENNReal.ofReal (Real.exp (-s * Real.log (f x.1 x.2 / g x.1 x.2))) ≤
              ENNReal.ofReal (1 - s * Dlam w f g + s^2 * B^2) := by
          intro p f g B s w hf hg hB hs hsB hw hw1
          have hB0 : ∀ S : DS K, ∀ X : Fin K, 0 ≤ B := fun S X => (abs_nonneg _).trans (hB S X)
          simp_rw [← ENNReal.ofReal_mul (hw _)]
          have hnn : ∀ x : Step K, 0 ≤ w x.1 * f x.1 x.2 := fun x => mul_nonneg (hw _) (hfnn p f hf _ _)
          simp_rw [← ENNReal.ofReal_mul (hnn _)]
          rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => mul_nonneg (hnn x) (Real.exp_pos _).le)]
          apply ENNReal.ofReal_le_ofReal
          rw [Fintype.sum_prod_type]
          have key : ∀ S, ∑ X, w S * f S X * Real.exp (-s * Real.log (f S X / g S X)) ≤ w S * (1 - s * DS_ f g S + s^2 * B^2) := by
            intro S
            have : DS_ f g S = ∑ X, f S X * Real.log (f S X / g S X) := by
              refine Finset.sum_subset (Finset.subset_univ _) fun X _ hX => ?_
              rw [(hf.1 S X).2 hX, zero_mul]
            rw [this]
            have e : w S * (1 - s * ∑ X, f S X * Real.log (f S X / g S X) + s^2 * B^2) =
              ∑ X, w S * f S X * (1 - s * Real.log (f S X / g S X) + s^2 * B^2) := by
              have : ∀ X, w S * f S X * (1 - s * Real.log (f S X / g S X) + s^2 * B^2) = (w S * (1 + s^2*B^2)) * f S X - w S * s * (f S X * Real.log (f S X / g S X)) := fun X => by ring
              simp_rw [this]
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hfsum p f hf]
              ring
            rw [e]
            refine Finset.sum_le_sum fun X _ => mul_le_mul_of_nonneg_left ?_ (hnn (S, X))
            have habs : |-s * Real.log (f S X / g S X)| ≤ s * B := by
              rw [abs_mul, abs_neg, abs_of_nonneg hs]
              exact mul_le_mul_of_nonneg_left (hB S X) hs
            have h1 := Real.abs_exp_sub_one_sub_id_le (habs.trans hsB)
            have h2 : (-s * Real.log (f S X / g S X))^2 ≤ (s*B)^2 := by
              rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) habs 2
            have h3 := (abs_le.1 h1).2
            have h4 : (s*B)^2 = s^2 * B^2 := mul_pow s B 2
            linarith only [h2, h3, h4]
          refine (Finset.sum_le_sum fun S _ => key S).trans (le_of_eq ?_)
          have : ∀ S, w S * (1 - s * DS_ f g S + s^2 * B^2) = (1 + s^2*B^2) * w S - s * (w S * DS_ f g S) := fun S => by ring
          simp_rw [this]
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hw1, Dlam]
          ring
        have htopuniq : ∀ (f : Pref K) (k k' : Fin K), IsTop f k → IsTop f k' → k = k' := by
          rintro f k k' ⟨σ, hσ, h0⟩ ⟨σ', hσ', h0'⟩
          by_contra hne
          let S : DS K := ⟨{k, k'}, by rw [Finset.card_pair hne]⟩
          have hk : k ∈ S.1 := by simp [S]
          have hk' : k' ∈ S.1 := by simp [S]
          have l1 : ∀ (τ : Equiv.Perm (Fin K)) (a b : Fin K), a ≠ b → (τ a).val = 0 → τ a < τ b := by
            intro τ a b hab h
            rw [Fin.lt_def, h]
            by_contra hc
            exact hab (τ.injective (Fin.ext (by omega)))
          have a1 := (hσ S k k' hk hk' hne).2 (l1 σ k k' hne h0)
          have a2 := (hσ' S k' k hk' hk (Ne.symm hne)).2 (l1 σ' k' k (Ne.symm hne) h0')
          have a3 := (hσ S k' k hk' hk (Ne.symm hne)).1 a2
          exact absurd (l1 σ k k' hne h0) (not_lt.2 a3.le)
        have htopex : 2 ≤ K → ∀ (p : ℝ) (f : Pref K), f ∈ (Mp p : Set (Pref K)) → ∃ k, IsTop f k := by
          intro hK p f hf
          obtain ⟨σ, hσ, _⟩ := hf.2.2
          exact ⟨σ.symm ⟨0, by omega⟩, σ, hσ, by simp⟩
        have hlam : ∀ (p : ℝ) (S0 : DS K) (MF : Set (Pref K)), MF.Finite → MF ⊆ Mp p → ∀ f ∈ MF, ∃ lam ∈ simplex K, ∀ g ∈ MF, g ∈ alt p f →
            Istar p f ≤ ENNReal.ofReal (Dlam lam f g) := by
          classical
          intro p S0 MF hfin hsub f hf
          have hne : (simplex K).Nonempty := ⟨fun S => if S = S0 then 1 else 0, fun S => by dsimp only; split_ifs <;> norm_num, by simp⟩
          have hcomp : IsCompact (simplex K) := isCompact_stdSimplex ℝ (DS K)
          set A := hfin.toFinset.filter (fun g => g ∈ alt p f) with hA
          by_cases hAe : A.Nonempty
          · have hc : Continuous (fun lam : DS K → ℝ => A.inf' hAe (fun g => Dlam lam f g)) := by
              apply Continuous.finset_inf'_apply
              intro g _
              unfold Dlam
              fun_prop
            obtain ⟨lam, hl, hmax⟩ := hcomp.exists_isMaxOn hne hc.continuousOn
            refine ⟨lam, hl, fun g hg hga => ?_⟩
            have hgA : g ∈ A := by simp [hA, hg, hga]
            refine iSup₂_le fun lam' hl' => ?_
            obtain ⟨g', hg', he⟩ := A.exists_mem_eq_inf' hAe (fun g => Dlam lam' f g)
            have hg'2 : g' ∈ alt p f := (Finset.mem_filter.1 hg').2
            refine (iInf₂_le g' hg'2).trans (ENNReal.ofReal_le_ofReal ?_)
            rw [← he]
            exact (hmax hl').trans (Finset.inf'_le _ hgA)
          · obtain ⟨lam, hl⟩ := hne
            refine ⟨lam, hl, fun g hg hga => ?_⟩
            exact absurd ⟨g, by simp [hA, hg, hga]⟩ hAe
        have hgeo : ∀ u : ℝ, 0 < u → ∑' m : ℕ, ENNReal.ofReal (Real.exp (-u)) ^ m ≤ ENNReal.ofReal (1 + 1 / u) := by
          intro u hu
          rw [ENNReal.tsum_geometric, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (Real.exp_pos _).le]
          have h1 : Real.exp (-u) ≤ 1 / (1 + u) := by
            rw [Real.exp_neg, ← one_div]
            apply one_div_le_one_div_of_le (by linarith)
            have := Real.add_one_le_exp u
            linarith
          have h2 : u / (1 + u) ≤ 1 - Real.exp (-u) := by
            have : u / (1 + u) = 1 - 1 / (1 + u) := by field_simp; ring
            linarith
          have h3 : 0 < u / (1+u) := by positivity
          rw [← ENNReal.ofReal_inv_of_pos (by linarith)]
          apply ENNReal.ofReal_le_ofReal
          calc _ ≤ (u / (1+u))⁻¹ := inv_anti₀ h3 h2
            _ = _ := by field_simp; ring
        have hsumG : ∀ (G : ℕ → ℝ≥0∞) (n0 T : ℕ) (c D u v : ℝ), 0 ≤ c → 0 ≤ D → 0 < u → 0 < v → (∀ t, G t ≤ 1) →
            (∀ m, G (n0 + m) ≤ ENNReal.ofReal c * (ENNReal.ofReal (Real.exp (-u)) ^ m + ENNReal.ofReal D * ENNReal.ofReal (Real.exp (-v)) ^ m)) →
            ∑' t, G t ≤ ENNReal.ofReal (n0 + T + (c * Real.exp (-u) ^ T * (1 + 1/u) + c * D * (1 + 1 / v))) := by
          intro G n0 T c D u v hc hD hu hv h1 hG
          rw [← Summable.sum_add_tsum_nat_add' (k := n0 + T) ENNReal.summable]
          rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add (by positivity) (by positivity)]
          refine add_le_add ?_ ?_
          · refine (Finset.sum_le_sum fun i _ => h1 i).trans (le_of_eq ?_)
            rw [ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
            simp
          · calc _ ≤ ∑' m : ℕ, (ENNReal.ofReal (c * Real.exp (-u) ^ T) * ENNReal.ofReal (Real.exp (-u)) ^ m + ENNReal.ofReal (c * D) * ENNReal.ofReal (Real.exp (-v)) ^ m) := by
                  refine ENNReal.tsum_le_tsum fun m => ?_
                  rw [show m + (n0 + T) = n0 + (T + m) by ring]
                  refine (hG _).trans ?_
                  rw [mul_add, ENNReal.ofReal_mul hc, ENNReal.ofReal_mul hc, ENNReal.ofReal_pow (Real.exp_pos _).le, pow_add, pow_add, mul_assoc, mul_assoc]
                  refine add_le_add_right ?_ _
                  refine mul_le_mul_right (mul_le_mul_right ?_ _) _
                  refine mul_le_of_le_one_left zero_le ?_
                  refine pow_le_one₀ zero_le ?_
                  rw [← ENNReal.ofReal_one]
                  apply ENNReal.ofReal_le_ofReal
                  exact Real.exp_le_one_iff.2 (by linarith)
              _ ≤ _ := by
                  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity : 0 ≤ c * Real.exp (-u) ^ T), ENNReal.ofReal_mul (by positivity : 0 ≤ c * D)]
                  exact add_le_add (mul_le_mul_right (hgeo u hu) _) (mul_le_mul_right (hgeo v hv) _)
        have hU : 2 ≤ K → ∃ U ∈ simplex K, ∀ S, 0 < U S := by
          intro hK
          have hne : Nonempty (DS K) := ⟨⟨Finset.univ, by simpa using hK⟩⟩
          have hc : (0:ℝ) < Fintype.card (DS K) := by exact_mod_cast Fintype.card_pos
          refine ⟨fun _ => (Fintype.card (DS K) : ℝ)⁻¹, ⟨fun S => by positivity, ?_⟩, fun S => by positivity⟩
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
          exact mul_inv_cancel₀ hc.ne'
        have hd : ∀ (p : ℝ) (U : DS K → ℝ) (F : Finset (Pref K)) (f : Pref K), (∀ S, 0 < U S) → (∀ g ∈ F, g ∈ (Mp p : Set (Pref K))) → f ∈ F →
            ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ ∀ g ∈ F, g ≠ f → d ≤ Dlam U f g := by
          classical
          intro p U F f hU hF hf
          have hpos : ∀ g ∈ F, g ≠ f → 0 < Dlam U f g := by
            intro g hg hgf
            obtain ⟨S, hS⟩ : ∃ S, f S ≠ g S := by
              by_contra hc
              push Not at hc
              exact hgf (funext fun S => (hc S).symm)
            unfold Dlam
            refine Finset.sum_pos' (fun S _ => mul_nonneg (hU S).le (hDSnn p f g (hF f hf) (hF g hg) S).1) ⟨S, Finset.mem_univ _, mul_pos (hU S) ?_⟩
            exact lt_of_le_of_ne (hDSnn p f g (hF f hf) (hF g hg) S).1 (fun h => hS ((hDSnn p f g (hF f hf) (hF g hg) S).2 h.symm))
          by_cases hne : (F.filter (fun g => g ≠ f)).Nonempty
          · obtain ⟨g, hg, hmin⟩ := Finset.exists_min_image _ (fun g => Dlam U f g) hne
            rw [Finset.mem_filter] at hg
            refine ⟨min 1 (Dlam U f g), lt_min one_pos (hpos g hg.1 hg.2), min_le_left _ _, fun g' hg' hgf' => (min_le_right _ _).trans (hmin g' (Finset.mem_filter.2 ⟨hg', hgf'⟩))⟩
          · refine ⟨1, one_pos, le_rfl, fun g hg hgf => absurd ⟨g, Finset.mem_filter.2 ⟨hg, hgf⟩⟩ hne⟩
        have hB : ∀ (F : Finset (Pref K)) (f : Pref K), ∃ B : ℝ, 1 ≤ B ∧ ∀ g ∈ F, ∀ S X, |Real.log (f S X / g S X)| ≤ B := by
          intro F f
          refine ⟨1 + ∑ g ∈ F, ∑ S, ∑ X, |Real.log (f S X / g S X)|, ?_, ?_⟩
          · have : 0 ≤ ∑ g ∈ F, ∑ S, ∑ X, |Real.log (f S X / g S X)| := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
            linarith
          · intro g hg S X
            have a1 := Finset.single_le_sum (f := fun X => |Real.log (f S X / g S X)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ X)
            have a2 := Finset.single_le_sum (f := fun S => ∑ X, |Real.log (f S X / g S X)|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ S)
            have a3 := Finset.single_le_sum (f := fun g => ∑ S, ∑ X, |Real.log (f S X / g S X)|) (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) hg
            beta_reduce at a1 a2 a3
            linarith
        obtain ⟨E, hE⟩ : ∃ E : Policy K → Pref K → ℕ → (List (Step K) → ℝ≥0∞) → ℝ≥0∞, ∀ (π : Policy K) (f : Pref K) (t : ℕ) (φ : List (Step K) → ℝ≥0∞), E π f t φ = ∑ v : Fin t → Step K, pathProb π f (toHist v) * φ (toHist v) := ⟨fun π f t φ => ∑ v : Fin t → Step K, pathProb π f (toHist v) * φ (toHist v), fun _ _ _ _ => rfl⟩
        have hlen : ∀ (t : ℕ) (v : Fin t → Step K), (toHist v).length = t := by
          intro t v
          simp [toHist]
        have E_zero : ∀ (π : Policy K) (f : Pref K) (φ : List (Step K) → ℝ≥0∞), E π f 0 φ = φ [] := by
          intro π f φ
          simp [hE, toHist, pathProb]
        have E_succ : ∀ (π : Policy K) (f : Pref K) (t : ℕ) (φ : List (Step K) → ℝ≥0∞),
            E π f (t+1) φ = ∑ v : Fin t → Step K, pathProb π f (toHist v) *
              ∑ x : Step K, π.disp (toHist v) x.1 * ENNReal.ofReal (f x.1 x.2) * φ (x :: toHist v) := by
          intro π f t φ
          rw [hE, ← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (t+1) => Step K)), Fintype.sum_prod_type,
            Finset.sum_comm]
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          have h1 : toHist (Fin.snocEquiv (fun _ : Fin (t+1) => Step K) (x, v)) = x :: toHist v := by
            unfold toHist
            rw [List.ofFn_succ']
            simp [Fin.snocEquiv, List.concat_eq_append]
          rw [h1]
          obtain ⟨S, X⟩ := x
          simp only [pathProb]
          ring
        have E_step_le : ∀ (π : Policy K) (f : Pref K) (t : ℕ) (φ φ' : List (Step K) → ℝ≥0∞) (r : ℝ≥0∞),
            (∀ h : List (Step K), h.length = t → ∑ x : Step K, π.disp h x.1 * ENNReal.ofReal (f x.1 x.2) * φ (x :: h) ≤ r * φ' h) →
            E π f (t+1) φ ≤ r * E π f t φ' := by
          intro π f t φ φ' r H
          rw [E_succ, hE, Finset.mul_sum]
          refine Finset.sum_le_sum fun v _ => ?_
          calc _ ≤ pathProb π f (toHist v) * (r * φ' (toHist v)) := by
                gcongr
                exact H _ (hlen t v)
            _ = _ := by ring
        have E_step_eq : ∀ (π : Policy K) (f : Pref K) (t : ℕ) (φ φ' : List (Step K) → ℝ≥0∞),
            (∀ h : List (Step K), h.length = t → ∑ x : Step K, π.disp h x.1 * ENNReal.ofReal (f x.1 x.2) * φ (x :: h) = φ' h) →
            E π f (t+1) φ = E π f t φ' := by
          intro π f t φ φ' H
          rw [E_succ, hE]
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [H _ (hlen t v)]
        have E_mono : ∀ (π : Policy K) (f : Pref K) (t : ℕ) (φ φ' : List (Step K) → ℝ≥0∞),
            (∀ h : List (Step K), h.length = t → pathProb π f h ≠ 0 → φ h ≤ φ' h) →
            E π f t φ ≤ E π f t φ' := by
          intro π f t φ φ' H
          rw [hE, hE]
          refine Finset.sum_le_sum fun v _ => ?_
          by_cases h0 : pathProb π f (toHist v) = 0
          · simp [h0]
          · gcongr
            exact H _ (hlen t v) h0
        have E_add : ∀ (π : Policy K) (f : Pref K) (t : ℕ) (φ φ' : List (Step K) → ℝ≥0∞),
            E π f t (fun h => φ h + φ' h) = E π f t φ + E π f t φ' := by
          intro π f t φ φ'
          simp only [hE, mul_add, Finset.sum_add_distrib]
        have E_smul : ∀ (π : Policy K) (f : Pref K) (t : ℕ) (c : ℝ≥0∞) (φ : List (Step K) → ℝ≥0∞),
            E π f t (fun h => c * φ h) = c * E π f t φ := by
          intro π f t c φ
          simp only [hE, Finset.mul_sum]
          refine Finset.sum_congr rfl fun v _ => ?_
          ring
        have E_sum : ∀ (π : Policy K) (f : Pref K) (t : ℕ) (A : Finset (Pref K)) (φ : Pref K → List (Step K) → ℝ≥0∞),
            E π f t (fun h => ∑ g ∈ A, φ g h) = ∑ g ∈ A, E π f t (φ g) := by
          intro π f t A φ
          simp only [hE, Finset.mul_sum]
          rw [Finset.sum_comm]
        have hstep1 : ∀ (p : ℝ) (π : Policy K) (f : Pref K), Admissible π → f ∈ (Mp p : Set (Pref K)) → ∀ h : List (Step K),
            ∑ x : Step K, π.disp h x.1 * ENNReal.ofReal (f x.1 x.2) = 1 := by
          intro p π f hπ hf h
          rw [Fintype.sum_prod_type, ← hπ h]
          refine Finset.sum_congr rfl fun S _ => ?_
          show ∑ X : Fin K, π.disp h S * ENNReal.ofReal (f S X) = _
          rw [← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg]
          · have : ∑ X, f S X = 1 := by
              rw [← hf.2.1 S]
              symm
              refine Finset.sum_subset (Finset.subset_univ _) fun X _ hX => (hf.1 S X).2 hX
            simp [this]
          · intro X _
            by_cases hX : X ∈ S.1
            · exact ((hf.1 S X).1 hX).le
            · exact ((hf.1 S X).2 hX).ge
        have E_one : ∀ (p : ℝ) (π : Policy K) (f : Pref K), Admissible π → f ∈ (Mp p : Set (Pref K)) → ∀ t : ℕ,
            E π f t (fun _ => 1) = 1 := by
          intro p π f hπ hf t
          induction t with
          | zero => rw [E_zero]
          | succ t ih =>
            refine Eq.trans ?_ ih
            apply E_step_eq
            intro h _
            refine Eq.trans ?_ (hstep1 p π f hπ hf h)
            refine Finset.sum_congr rfl fun x _ => ?_
            exact mul_one (π.disp h x.1 * ENNReal.ofReal (f x.1 x.2))
        have hGT : ∀ (π : Policy K) (f : Pref K) (t : ℕ), probGT π f t = E π f t (fun h => if survives π h then 1 else 0) := by
          intro π f t
          rw [hE]
          unfold probGT
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [mul_ite, mul_one, mul_zero]
        have hSTOP : ∀ (π : Policy K) (f : Pref K), probStop π f = ∑' t, E π f t (fun h => if stopsAt π h then 1 else 0) := by
          intro π f
          unfold probStop
          refine tsum_congr fun t => ?_
          rw [hE]
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [mul_ite, mul_one, mul_zero]
        have hsurv : ∀ (π : Policy K) (x : Step K) (h : List (Step K)), survives π (x :: h) ↔ ¬ π.stop (x::h) ∧ survives π h := by
          intro π x h
          constructor
          · intro H
            refine ⟨by simpa using H 0 (by simp), fun j hj => by simpa using H (j+1) (by simpa using hj)⟩
          · rintro ⟨H1, H2⟩ j hj
            cases j with
            | zero => simpa using H1
            | succ j => simpa using H2 j (by simpa using hj)
        have hstops : ∀ (π : Policy K) (x : Step K) (h : List (Step K)), stopsAt π (x :: h) ↔ π.stop (x::h) ∧ survives π h := by
          intro π x h
          constructor
          · rintro ⟨H1, H⟩
            refine ⟨H1, fun j hj => by simpa using H (j+1) (by omega) (by simpa using hj)⟩
          · rintro ⟨H1, H2⟩ 
            refine ⟨H1, fun j hj1 hj => ?_⟩
            cases j with
            | zero => omega
            | succ j => simpa using H2 j (by simpa using hj)
        have hcons : ∀ (p : ℝ) (π : Policy K) (f : Pref K), Admissible π → f ∈ (Mp p : Set (Pref K)) → ∀ t : ℕ,
            ∑ i ∈ Finset.range (t+1), E π f i (fun h => if stopsAt π h then 1 else 0) + probGT π f t = 1 := by
          intro p π f hπ hf t
          induction t with
          | zero =>
            simp only [hGT, zero_add, Finset.sum_range_one, E_zero]
            by_cases h : π.stop []
            · have h1 : stopsAt π [] := ⟨h, fun j h1 h2 => by simp at h2; omega⟩
              have h2 : ¬ survives π [] := fun H => H 0 (by simp) (by simpa using h)
              simp [h1, h2]
            · have h1 : ¬ stopsAt π [] := fun H => h H.1
              have h2 : survives π [] := fun j _ => by simpa using h
              simp [h1, h2]
          | succ t ih =>
            rw [Finset.sum_range_succ, add_assoc]
            have : E π f (t+1) (fun h => if stopsAt π h then 1 else 0) + probGT π f (t+1) = probGT π f t := by
              rw [hGT, hGT, ← E_add]
              apply E_step_eq
              intro h _
              by_cases hs : survives π h
              · rw [if_pos hs]
                refine Eq.trans ?_ (hstep1 p π f hπ hf h)
                refine Finset.sum_congr rfl fun x _ => ?_
                by_cases hx : π.stop (x :: h)
                · have a1 : stopsAt π (x :: h) := (hstops π x h).2 ⟨hx, hs⟩
                  have a2 : ¬ survives π (x :: h) := fun H => ((hsurv π x h).1 H).1 hx
                  simp only [if_pos a1, if_neg a2, add_zero, mul_one]
                · have a1 : ¬ stopsAt π (x :: h) := fun H => hx ((hstops π x h).1 H).1
                  have a2 : survives π (x :: h) := (hsurv π x h).2 ⟨hx, hs⟩
                  simp only [if_neg a1, if_pos a2, zero_add, mul_one]
              · simp [hsurv, hstops, hs]
            rw [this, ih]
        have hstop_le : ∀ (p : ℝ) (π : Policy K) (f : Pref K), Admissible π → f ∈ (Mp p : Set (Pref K)) → probStop π f ≤ 1 := by
          classical
          intro p π f hπ hf
          rw [hSTOP]
          refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
          calc _ ≤ ∑ i ∈ Finset.range (n+1), E π f i (fun h => if stopsAt π h then 1 else 0) :=
                Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
            _ ≤ _ := le_self_add
            _ = 1 := hcons p π f hπ hf n
        have hstop_eq : ∀ (p : ℝ) (π : Policy K) (f : Pref K), Admissible π → f ∈ (Mp p : Set (Pref K)) → expTau π f < ⊤ → probStop π f = 1 := by
          classical
          intro p π f hπ hf hτ
          refine le_antisymm (hstop_le p π f hπ hf) ?_
          have h0 : Filter.Tendsto (probGT π f) Filter.atTop (nhds 0) := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hτ.ne
          have h1 : ∀ t, 1 ≤ probStop π f + probGT π f t := by
            intro t
            rw [← hcons p π f hπ hf t, hSTOP]
            gcongr
            exact ENNReal.sum_le_tsum _
          have h2 : Filter.Tendsto (fun t => probStop π f + probGT π f t) Filter.atTop (nhds (probStop π f + 0)) :=
            h0.const_add _
          rw [add_zero] at h2
          exact ge_of_tendsto' h2 h1
        have hwrong : ∀ (p : ℝ) (π : Policy K) (f : Pref K) (F : Finset (Pref K)) (c : ℝ≥0∞), Admissible π →
            (∀ g ∈ F, g ∈ (Mp p : Set (Pref K))) → (∀ h, stopsAt π h → ¬ IsTop f (π.select h) → ∃ g ∈ F, pathProb π f h ≤ c * pathProb π g h) →
            probWrong π f ≤ c * F.card := by
          classical
          intro p π f F c hπ hF H
          have h1 : probWrong π f ≤ ∑ g ∈ F, c * probStop π g := by
            simp only [hSTOP, ← ENNReal.tsum_mul_left]
            rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
            refine ENNReal.tsum_le_tsum fun t => ?_
            simp only [hE, Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_le_sum fun v _ => ?_
            by_cases hc : stopsAt π (toHist v) ∧ ¬ IsTop f (π.select (toHist v))
            · rw [if_pos hc]
              obtain ⟨g, hg, hle⟩ := H _ hc.1 hc.2
              refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le) hg)
              simpa [hc.1] using hle
            · rw [if_neg hc]
              exact zero_le
          refine h1.trans ?_
          calc _ ≤ ∑ g ∈ F, c * 1 := by
                refine Finset.sum_le_sum fun g hg => ?_
                gcongr
                exact hstop_le p π g hπ (hF g hg)
            _ = _ := by simp [mul_comm]
        have hstepphi : ∀ (p : ℝ) (π : Policy K) (f g : Pref K) (B s κ : ℝ) (w : DS K → ℝ) (h : List (Step K)), f ∈ (Mp p : Set (Pref K)) → g ∈ (Mp p : Set (Pref K)) →
            (∀ S X, |Real.log (f S X / g S X)| ≤ B) → 0 ≤ s → s * B ≤ 1 → w ∈ simplex K → (∀ S, π.disp h S = ENNReal.ofReal (w S)) →
            κ + s * B^2 ≤ Dlam w f g →
            ∑ x : Step K, π.disp h x.1 * ENNReal.ofReal (f x.1 x.2) * ENNReal.ofReal (Real.exp (-s * ((x :: h).map (fun x => Real.log (f x.1 x.2 / g x.1 x.2))).sum)) ≤
              ENNReal.ofReal (Real.exp (-(s * κ))) * ENNReal.ofReal (Real.exp (-s * (h.map (fun x => Real.log (f x.1 x.2 / g x.1 x.2))).sum)) := by
          intro p π f g B s κ w h hf hg hB hs hsB hw hd hκ
          have h1 := hstepKL p f g B s w hf hg hB hs hsB hw.1 hw.2
          have h2 : 1 - s * Dlam w f g + s^2 * B^2 ≤ Real.exp (-(s * κ)) := by
            have a1 := Real.add_one_le_exp (-(s * κ))
            have a2 := mul_le_mul_of_nonneg_left hκ hs
            linarith only [a1, a2]
          refine le_trans (le_of_eq ?_) (mul_le_mul_left (h1.trans (ENNReal.ofReal_le_ofReal h2)) _)
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [hd, List.map_cons, List.sum_cons, mul_add, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
          ring
        have hexplore : ∀ (p : ℝ) (π : Policy K) (f g : Pref K) (B s κ : ℝ) (U : DS K → ℝ) (n0 : ℕ), f ∈ (Mp p : Set (Pref K)) → g ∈ (Mp p : Set (Pref K)) →
            (∀ S X, |Real.log (f S X / g S X)| ≤ B) → 0 ≤ s → s * B ≤ 1 → U ∈ simplex K → (∀ h : List (Step K), h.length < n0 → ∀ S, π.disp h S = ENNReal.ofReal (U S)) →
            κ + s * B^2 ≤ Dlam U f g → ∀ t ≤ n0,
            E π f t (fun h => ENNReal.ofReal (Real.exp (-s * (h.map (fun x => Real.log (f x.1 x.2 / g x.1 x.2))).sum))) ≤ ENNReal.ofReal (Real.exp (-(s * κ))) ^ t := by
          intro p π f g B s κ U n0 hf hg hB hs hsB hU hd hκ t
          induction t with
          | zero => intro _; simp [E_zero]
          | succ t ih =>
            intro ht
            rw [pow_succ']
            refine le_trans (E_step_le π f t _ _ (ENNReal.ofReal (Real.exp (-(s * κ)))) ?_) (mul_le_mul_right (ih (by omega)) _)
            intro h hh
            exact hstepphi p π f g B s κ U h hf hg hB hs hsB hU (hd h (by omega)) hκ
        have htrack : ∀ (p : ℝ) (π : Policy K) (f g : Pref K) (B s κ ε : ℝ) (U : DS K → ℝ) (lam : Pref K → DS K → ℝ) (est : List (Step K) → Pref K) (Q : Pref K → Prop) [DecidablePred Q] (n0 : ℕ), f ∈ (Mp p : Set (Pref K)) → g ∈ (Mp p : Set (Pref K)) →
            (∀ S X, |Real.log (f S X / g S X)| ≤ B) → 0 ≤ s → s * B ≤ 1 → U ∈ simplex K → (∀ h, lam (est h) ∈ simplex K) → 0 ≤ ε → ε ≤ 1 →
            (∀ h : List (Step K), n0 ≤ h.length → ∀ S, π.disp h S = ENNReal.ofReal ((1 - ε) * lam (est (h.drop (h.length - n0))) S + ε * U S)) →
            (∀ h, Q (est h) → κ + s * B^2 ≤ (1 - ε) * Dlam (lam (est h)) f g + ε * Dlam U f g) → ∀ m : ℕ,
            E π f (n0 + m) (fun h => (if Q (est (h.drop (h.length - n0))) then 1 else 0) * ENNReal.ofReal (Real.exp (-s * (h.map (fun x => Real.log (f x.1 x.2 / g x.1 x.2))).sum))) ≤ ENNReal.ofReal (Real.exp (-(s * κ))) ^ m *
             E π f n0 (fun h => (if Q (est h) then 1 else 0) * ENNReal.ofReal (Real.exp (-s * (h.map (fun x => Real.log (f x.1 x.2 / g x.1 x.2))).sum))) := by
          intro p π f g B s κ ε U lam est Q _ n0 hf hg hB hs hsB hU hlam h0 h1 hd hκ m
          induction m with
          | zero =>
            rw [pow_zero, one_mul]
            refine E_mono π f _ _ _ fun h hh _ => ?_
            rw [hh, show n0 + 0 - n0 = 0 by omega, List.drop_zero]
          | succ m ih =>
            rw [pow_succ', mul_assoc]
            refine le_trans (E_step_le π f (n0+m) _ _ (ENNReal.ofReal (Real.exp (-(s * κ)))) ?_) (mul_le_mul_right ih _)
            intro h hh
            have hdrop : ∀ x : Step K, (x :: h).drop ((x::h).length - n0) = h.drop (h.length - n0) := by
              intro x
              rw [List.length_cons, show h.length + 1 - n0 = (h.length - n0) + 1 by omega, List.drop_succ_cons]
            simp only [hdrop]
            by_cases hq : Q (est (h.drop (h.length - n0)))
            · simp only [if_pos hq, one_mul]
              set q := est (h.drop (h.length - n0)) with hqdef
              have hl : lam q ∈ simplex K := hlam _
              refine hstepphi p π f g B s κ (fun S => (1 - ε) * lam q S + ε * U S) h hf hg hB hs hsB ?_ (hd h (by omega)) ?_
              · refine ⟨fun S => add_nonneg (mul_nonneg (by linarith) (hl.1 S)) (mul_nonneg h0 (hU.1 S)), ?_⟩
                rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hl.2, hU.2]
                ring
              · refine (hκ _ hq).trans (le_of_eq ?_)
                simp only [Dlam, Finset.mul_sum, ← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun S _ => ?_
                ring
            · simp [if_neg hq]
        have hbad : ∀ (p : ℝ) (π : Policy K) (f : Pref K) (F : Finset (Pref K)) (B s κ : ℝ) (U : DS K → ℝ) (est : List (Step K) → Pref K) (n0 : ℕ), f ∈ F → (∀ g ∈ F, g ∈ (Mp p : Set (Pref K))) →
            (∀ g ∈ F, ∀ S X, |Real.log (f S X / g S X)| ≤ B) → 0 ≤ s → s * B ≤ 1 → U ∈ simplex K → (∀ h : List (Step K), h.length < n0 → ∀ S, π.disp h S = ENNReal.ofReal (U S)) →
            (∀ h, est h ∈ F) → (∀ h : List (Step K), ∀ g ∈ F, (h.map (fun x => g x.1 x.2)).prod ≤ (h.map (fun x => est h x.1 x.2)).prod) →
            (∀ g ∈ F, g ≠ f → κ + s * B^2 ≤ Dlam U f g) → 
            E π f n0 (fun h => if est h ≠ f then 1 else 0) ≤ F.card * ENNReal.ofReal (Real.exp (-(s * κ))) ^ n0 := by
          intro p π f F B s κ U est n0 hfF hF hB hs hsB hU hd hest hmax hκ
          calc _ ≤ E π f n0 (fun h => ∑ g ∈ F, if g ≠ f then ENNReal.ofReal (Real.exp (-s * (h.map (fun x => Real.log (f x.1 x.2 / g x.1 x.2))).sum)) else 0) := by
                refine E_mono π f _ _ _ fun h hh h0 => ?_
                by_cases he : est h ≠ f
                · rw [if_pos he]
                  refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le) (hest h))
                  rw [if_pos he, ← ENNReal.ofReal_one]
                  apply ENNReal.ofReal_le_ofReal
                  apply Real.one_le_exp
                  have hp := hlikpos p π f (hF f hfF) h h0
                  have e1 := hlikratio p f (est h) (hF f hfF) (hF _ (hest h)) h hp
                  have e2 := hmax h f hfF
                  rw [e1] at e2
                  have e3 : 1 ≤ Real.exp (-(h.map (fun x => Real.log (f x.1 x.2 / est h x.1 x.2))).sum) := by
                    by_contra hc
                    have a := mul_lt_mul_of_pos_left (not_le.1 hc) hp
                    linarith only [a, e2]
                  have e4 := Real.one_le_exp_iff.1 e3
                  have e5 := mul_nonneg hs e4
                  linarith only [e5]
                · rw [if_neg he]; exact zero_le
            _ = ∑ g ∈ F, E π f n0 (fun h => if g ≠ f then ENNReal.ofReal (Real.exp (-s * (h.map (fun x => Real.log (f x.1 x.2 / g x.1 x.2))).sum)) else 0) := E_sum π f n0 F (fun g h => if g ≠ f then ENNReal.ofReal (Real.exp (-s * (h.map (fun x => Real.log (f x.1 x.2 / g x.1 x.2))).sum)) else 0)
            _ ≤ ∑ g ∈ F, ENNReal.ofReal (Real.exp (-(s * κ))) ^ n0 := by
                refine Finset.sum_le_sum fun g hg => ?_
                by_cases hgf : g ≠ f
                · simp only [if_pos hgf]
                  exact hexplore p π f g B s κ U n0 (hF f hfF) (hF g hg) (hB g hg) hs hsB hU hd (hκ g hg hgf) n0 le_rfl
                · simp only [if_neg hgf]
                  simp [hE]
            _ = _ := by simp
        have hG : ∀ (p : ℝ) (π : Policy K) (f : Pref K) (F A : Finset (Pref K)) (B s κ κb s0 κ0 β ε : ℝ) (U : DS K → ℝ) (lam : Pref K → DS K → ℝ) (est : List (Step K) → Pref K) (n0 : ℕ), 
            f ∈ F → A ⊆ F → f ∉ A → (∀ g ∈ F, g ∈ (Mp p : Set (Pref K))) →
            (∀ g ∈ F, ∀ S X, |Real.log (f S X / g S X)| ≤ B) → 0 ≤ s → s * B ≤ 1 → 0 ≤ s0 → s0 * B ≤ 1 → U ∈ simplex K → (∀ h, lam (est h) ∈ simplex K) → 0 ≤ ε → ε ≤ 1 →
            (∀ h : List (Step K), h.length < n0 → ∀ S, π.disp h S = ENNReal.ofReal (U S)) →
            (∀ h : List (Step K), n0 ≤ h.length → ∀ S, π.disp h S = ENNReal.ofReal ((1 - ε) * lam (est (h.drop (h.length - n0))) S + ε * U S)) →
            (∀ h, est h ∈ F) → (∀ h : List (Step K), ∀ g ∈ F, (h.map (fun x => g x.1 x.2)).prod ≤ (h.map (fun x => est h x.1 x.2)).prod) →
            (∀ h : List (Step K), n0 ≤ h.length → ¬ π.stop h → ∃ g ∈ A, (h.map (fun x => f x.1 x.2)).prod < Real.exp β * (h.map (fun x => g x.1 x.2)).prod) →
            (∀ g ∈ F, g ≠ f → κ0 + s0 * B^2 ≤ Dlam U f g) → (∀ g ∈ F, g ≠ f → s * B^2 ≤ Dlam U f g) →
            (∀ g ∈ A, κ + s * B^2 ≤ (1 - ε) * Dlam (lam f) f g + ε * Dlam U f g) → 
            (∀ g ∈ F, g ≠ f → κb + s * B^2 ≤ ε * Dlam U f g) → ∀ m : ℕ,
            probGT π f (n0 + m) ≤ F.card * ENNReal.ofReal (Real.exp (s * β)) * (ENNReal.ofReal (Real.exp (-(s * κ))) ^ m + 
              ENNReal.ofReal (Real.exp (s * B * n0)) * (F.card * ENNReal.ofReal (Real.exp (-(s0 * κ0))) ^ n0) * ENNReal.ofReal (Real.exp (-(s * κb))) ^ m) := by
          intro p π f F A B s κ κb s0 κ0 β ε U lam est n0 hfF hAF hfA hF hB hs hsB hs0 hs0B hU hlam hε hε1 hd1 hd2 hest hmax hsv hκ0 hsU hκ hκb m
          have hfM := hF f hfF
          set φ : Pref K → List (Step K) → ℝ≥0∞ := fun g h => ENNReal.ofReal (Real.exp (-s * (h.map (fun x => Real.log (f x.1 x.2 / g x.1 x.2))).sum)) with hφ
          have hDl : ∀ g ∈ F, ∀ h, 0 ≤ Dlam (lam (est h)) f g := by
            intro g hg h
            unfold Dlam
            exact Finset.sum_nonneg fun S _ => mul_nonneg ((hlam h).1 S) (hDSnn p f g hfM (hF g hg) S).1
          have hone : ∀ g ∈ A, E π f (n0 + m) (φ g) ≤ ENNReal.ofReal (Real.exp (-(s * κ))) ^ m + 
              ENNReal.ofReal (Real.exp (s * B * n0)) * (F.card * ENNReal.ofReal (Real.exp (-(s0 * κ0))) ^ n0) * ENNReal.ofReal (Real.exp (-(s * κb))) ^ m := by
            intro g hg
            have hgF := hAF hg
            have hgf : g ≠ f := fun h => hfA (h ▸ hg)
            have hsplit : E π f (n0+m) (φ g) = E π f (n0+m) (fun h => (if est (h.drop (h.length - n0)) = f then 1 else 0) * φ g h) + E π f (n0+m) (fun h => (if est (h.drop (h.length - n0)) ≠ f then 1 else 0) * φ g h) := by
              rw [← E_add]
              congr 1
              funext h
              by_cases hq : est (h.drop (h.length - n0)) = f <;> simp [hq]
            rw [hsplit]
            refine add_le_add ?_ ?_
            · refine (htrack p π f g B s κ ε U lam est (fun q => q = f) n0 hfM (hF g hgF) (hB g hgF) hs hsB hU hlam hε hε1 hd2 ?_ m).trans ?_
              · intro h hh
                have hh' : est h = f := hh
                rw [hh']
                exact hκ g hg
              · refine mul_le_of_le_one_right zero_le ?_
                have := hexplore p π f g B s 0 U n0 hfM (hF g hgF) (hB g hgF) hs hsB hU hd1 (by simpa using hsU g hgF hgf) n0 le_rfl
                simp only [mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one, one_pow] at this
                refine le_trans (E_mono π f _ _ _ fun h _ _ => ?_) this
                split_ifs <;> simp
            · refine (htrack p π f g B s κb ε U lam est (fun q => q ≠ f) n0 hfM (hF g hgF) (hB g hgF) hs hsB hU hlam hε hε1 hd2 ?_ m).trans ?_
              · intro h hh
                have h1 := hκb g hgF hgf
                have h2 := mul_nonneg (sub_nonneg.2 hε1) (hDl g hgF h)
                linarith only [h1, h2]
              · rw [mul_comm]
                refine mul_le_mul_left ?_ _
                refine le_trans (E_mono π f n0 _ (fun h => ENNReal.ofReal (Real.exp (s * B * n0)) * (if est h ≠ f then 1 else 0)) fun h hh _ => ?_) ?_
                · rw [mul_comm]
                  refine mul_le_mul_left ?_ _
                  apply ENNReal.ofReal_le_ofReal
                  apply Real.exp_le_exp.2
                  have hsum : ∀ l : List (Step K), -(l.map (fun x => Real.log (f x.1 x.2 / g x.1 x.2))).sum ≤ B * l.length := by
                    intro l
                    induction l with
                    | nil => simp
                    | cons x l ih =>
                      simp only [List.map_cons, List.sum_cons, List.length_cons]
                      push_cast
                      have a := (abs_le.1 (hB g hgF x.1 x.2)).1
                      linarith only [a, ih]
                  have a := mul_le_mul_of_nonneg_left (hsum h) hs
                  rw [hh] at a
                  linarith only [a]
                · rw [E_smul]
                  refine mul_le_mul_right ?_ _
                  exact hbad p π f F B s0 κ0 U est n0 hfF hF hB hs0 hs0B hU hd1 hest hmax hκ0
          rw [hGT]
          calc _ ≤ E π f (n0+m) (fun h => ENNReal.ofReal (Real.exp (s * β)) * ∑ g ∈ A, φ g h) := by
                refine E_mono π f _ _ _ fun h hh h0 => ?_
                by_cases hsu : survives π h
                · rw [if_pos hsu]
                  have hns : ¬ π.stop h := by simpa using hsu 0 (by simp)
                  obtain ⟨g, hg, hlt⟩ := hsv h (by omega) hns
                  refine le_trans ?_ (mul_le_mul_right (Finset.single_le_sum (fun _ _ => zero_le) hg) _)
                  simp only [hφ]
                  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_one]
                  apply ENNReal.ofReal_le_ofReal
                  rw [← Real.exp_add]
                  apply Real.one_le_exp
                  have hp := hlikpos p π f hfM h h0
                  have e1 := hlikratio p f g hfM (hF g (hAF hg)) h hp
                  rw [e1, mul_left_comm, ← Real.exp_add] at hlt
                  have e3 : 1 ≤ Real.exp (β + -(h.map (fun x => Real.log (f x.1 x.2 / g x.1 x.2))).sum) := by
                    by_contra hc
                    have a := mul_lt_mul_of_pos_left (not_le.1 hc) hp
                    linarith only [a, hlt]
                  have e4 := Real.one_le_exp_iff.1 e3
                  have e5 := mul_nonneg hs e4
                  linarith only [e5]
                · rw [if_neg hsu]; exact zero_le
            _ = ENNReal.ofReal (Real.exp (s * β)) * ∑ g ∈ A, E π f (n0+m) (φ g) := by
                rw [E_smul, E_sum]
            _ ≤ ENNReal.ofReal (Real.exp (s * β)) * ∑ g ∈ F, (ENNReal.ofReal (Real.exp (-(s * κ))) ^ m + 
              ENNReal.ofReal (Real.exp (s * B * n0)) * (F.card * ENNReal.ofReal (Real.exp (-(s0 * κ0))) ^ n0) * ENNReal.ofReal (Real.exp (-(s * κb))) ^ m) := by
                refine mul_le_mul_right ?_ _
                exact (Finset.sum_le_sum hone).trans (Finset.sum_le_sum_of_subset hAF)
            _ = _ := by
                rw [Finset.sum_const, nsmul_eq_mul]
                ring
        obtain ⟨U, hUs, hUpos⟩ := hU hK
        let S0 : DS K := ⟨Finset.univ, by simpa using hK⟩
        rcases MF.eq_empty_or_nonempty with hemp | hMFne
        · subst hemp
          refine ⟨fun _ => ⟨fun _ S => ENNReal.ofReal (U S), fun _ => True, fun _ => ⟨0, by omega⟩⟩, ?_, ?_, ?_⟩
          · intro δ _
            refine ⟨fun h => ?_, fun f hf => absurd hf (Set.notMem_empty f)⟩
            show ∑ S, ENNReal.ofReal (U S) = 1
            rw [← ENNReal.ofReal_sum_of_nonneg (fun S _ => hUs.1 S), hUs.2, ENNReal.ofReal_one]
          · intro δ _ f hf
            exact absurd hf (Set.notMem_empty f)
          · intro f hf
            exact absurd hf (Set.notMem_empty f)
        set F : Finset (Pref K) := hfinite.toFinset with hFdef
        have hFm : ∀ g, g ∈ F ↔ g ∈ MF := fun g => hfinite.mem_toFinset
        have hFp : ∀ g ∈ F, g ∈ (Mp p : Set (Pref K)) := fun g hg => hsub ((hFm g).1 hg)
        have hFne : F.Nonempty := by
          obtain ⟨f, hf⟩ := hMFne
          exact ⟨f, (hFm f).2 hf⟩
        have hlam' : ∀ f : Pref K, ∃ l ∈ simplex K, f ∈ MF → ∀ g ∈ MF, g ∈ alt p f → Istar p f ≤ ENNReal.ofReal (Dlam l f g) := by
          intro f
          by_cases hf : f ∈ MF
          · obtain ⟨l, h1, h2⟩ := hlam p S0 MF hfinite hsub f hf
            exact ⟨l, h1, fun _ => h2⟩
          · exact ⟨U, hUs, fun h => absurd h hf⟩
        choose lam hlams hlamI using hlam'
        have hest' : ∀ h : List (Step K), ∃ q ∈ F, ∀ g ∈ F, (h.map (fun x => g x.1 x.2)).prod ≤ (h.map (fun x => q x.1 x.2)).prod := by
          intro h
          exact Finset.exists_max_image F (fun g => (h.map (fun x => g x.1 x.2)).prod) hFne
        choose est hestF hestmax using hest'
        obtain ⟨StopP, hStopP⟩ : ∃ StopP : ℝ → Pref K → List (Step K) → Prop, ∀ β f' h, StopP β f' h ↔
            ∀ g ∈ F, g ∈ alt p f' → Real.exp β * (h.map (fun x => g x.1 x.2)).prod ≤ (h.map (fun x => f' x.1 x.2)).prod := ⟨_, fun _ _ _ => Iff.rfl⟩
        have hsel' : ∀ (β : ℝ) (h : List (Step K)), ∃ k : Fin K, (∃ f' ∈ F, StopP β f' h) → ∃ f' ∈ F, StopP β f' h ∧ IsTop f' k := by
          intro β h
          by_cases hex : ∃ f' ∈ F, StopP β f' h
          · obtain ⟨f', hf', hst⟩ := hex
            obtain ⟨k, hk⟩ := htopex hK p f' (hFp f' hf')
            exact ⟨k, fun _ => ⟨f', hf', hst, hk⟩⟩
          · exact ⟨⟨0, by omega⟩, fun h => absurd h hex⟩
        choose sel hsel using hsel'
        set M : ℝ := (F.card : ℝ) with hM
        have hM1 : 1 ≤ M := by
          rw [hM]; exact_mod_cast hFne.card_pos
        have hM0 : 0 < M := one_pos.trans_le hM1
        obtain ⟨β, hβ⟩ : ∃ β : ℝ → ℝ, ∀ δ, β δ = Real.log (M / δ) := ⟨_, fun _ => rfl⟩
        obtain ⟨y, hy⟩ : ∃ y : ℝ → ℝ, ∀ δ, y δ = Real.sqrt (Real.sqrt (β δ)) := ⟨_, fun _ => rfl⟩
        obtain ⟨N, hN⟩ : ∃ N : ℝ → ℕ, ∀ δ, N δ = ⌈y δ⌉₊ + 1 := ⟨_, fun _ => rfl⟩
        obtain ⟨fam, hfam⟩ : ∃ fam : ℝ → Policy K, ∀ δ, fam δ = 
          { disp := fun h S => if h.length < (N δ)^2 then ENNReal.ofReal (U S) else
              ENNReal.ofReal ((1 - 1 / (N δ : ℝ)) * lam (est (h.drop (h.length - (N δ)^2))) S + 1 / (N δ : ℝ) * U S)
            stop := fun h => (N δ)^2 ≤ h.length ∧ ∃ f' ∈ F, StopP (β δ) f' h
            select := fun h => sel (β δ) h } := ⟨_, fun _ => rfl⟩
        have hN1 : ∀ δ, 1 ≤ (N δ : ℝ) := by
          intro δ
          rw [hN]; push_cast
          have a : (0:ℝ) ≤ (⌈y δ⌉₊ : ℝ) := Nat.cast_nonneg _
          linarith only [a]
        have hy0 : ∀ δ, 0 ≤ y δ := by
          intro δ; rw [hy]; exact Real.sqrt_nonneg _
        have hyN : ∀ δ, y δ ≤ N δ := by
          intro δ
          rw [hN]; push_cast
          have a := Nat.le_ceil (y δ)
          linarith only [a]
        have hNy : ∀ δ, (N δ : ℝ) ≤ y δ + 2 := by
          intro δ
          rw [hN]; push_cast
          have a := (Nat.ceil_lt_add_one (hy0 δ)).le
          linarith only [a]
        have hε0 : ∀ δ, 0 ≤ 1 / (N δ : ℝ) := fun δ => one_div_nonneg.2 (Nat.cast_nonneg _)
        have hε1 : ∀ δ, 1 / (N δ : ℝ) ≤ 1 := fun δ => div_le_one_of_le₀ (hN1 δ) (Nat.cast_nonneg _)
        have hd1 : ∀ δ, ∀ h : List (Step K), h.length < (N δ)^2 → ∀ S, (fam δ).disp h S = ENNReal.ofReal (U S) := by
          intro δ h hh S
          rw [hfam]
          exact if_pos hh
        have hd2 : ∀ δ, ∀ h : List (Step K), (N δ)^2 ≤ h.length → ∀ S, (fam δ).disp h S = ENNReal.ofReal ((1 - 1 / (N δ : ℝ)) * lam (est (h.drop (h.length - (N δ)^2))) S + 1 / (N δ : ℝ) * U S) := by
          intro δ h hh S
          rw [hfam]
          exact if_neg (not_lt.2 hh)
        have hadm : ∀ δ, Admissible (fam δ) := by
          intro δ h
          by_cases hh : h.length < (N δ)^2
          · simp only [hd1 δ h hh]
            rw [← ENNReal.ofReal_sum_of_nonneg (fun S _ => hUs.1 S), hUs.2, ENNReal.ofReal_one]
          · simp only [hd2 δ h (not_lt.1 hh)]
            rw [← ENNReal.ofReal_sum_of_nonneg]
            · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, (hlams _).2, hUs.2, mul_one, mul_one, sub_add_cancel, ENNReal.ofReal_one]
            · intro S _
              exact add_nonneg (mul_nonneg (sub_nonneg.2 (hε1 δ)) ((hlams _).1 S)) (mul_nonneg (hε0 δ) (hUs.1 S))
        have hβpos : ∀ δ ∈ Set.Ioo (0:ℝ) 1, 0 < β δ := by
          intro δ hδ
          rw [hβ]
          apply Real.log_pos
          rw [lt_div_iff₀ hδ.1, one_mul]
          exact hδ.2.trans_le hM1
        have hexpβ : ∀ δ ∈ Set.Ioo (0:ℝ) 1, Real.exp (β δ) = M / δ := by
          intro δ hδ
          rw [hβ, Real.exp_log (div_pos hM0 hδ.1)]
        have hwr : ∀ δ ∈ Set.Ioo (0:ℝ) 1, ∀ f ∈ MF, probWrong (fam δ) f ≤ ENNReal.ofReal δ := by
          intro δ hδ f hf
          have hfF := (hFm f).2 hf
          have := hwrong p (fam δ) f F (ENNReal.ofReal (δ / M)) (hadm δ) hFp ?_
          · refine this.trans (le_of_eq ?_)
            rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (div_nonneg hδ.1.le hM0.le), ← hM, div_mul_cancel₀ _ hM0.ne']
          · intro h hst hnt
            have hst1 : (N δ)^2 ≤ h.length ∧ ∃ f' ∈ F, StopP (β δ) f' h := by
              have := hst.1
              rw [hfam] at this
              exact this
            have hnt1 : ¬ IsTop f (sel (β δ) h) := by
              rw [hfam] at hnt
              exact hnt
            obtain ⟨f', hf', hsp, htop⟩ := hsel (β δ) h hst1.2
            refine ⟨f', hf', hpathle p (fam δ) f f' (hFp f hfF) (hFp f' hf') h _ (div_nonneg hδ.1.le hM0.le) ?_⟩
            have h1 := (hStopP _ _ _).1 hsp f hfF ⟨hFp f hfF, fun k k' hk hk' hkk => hnt1 (by
              rw [htopuniq f' _ _ htop hk, hkk]; exact hk')⟩
            rw [hexpβ δ hδ] at h1
            have h2 := mul_le_mul_of_nonneg_left h1 (div_nonneg hδ.1.le hM0.le)
            have e : δ / M * (M / δ * (h.map (fun x => f x.1 x.2)).prod) = (h.map (fun x => f x.1 x.2)).prod := by
              rw [← mul_assoc, div_mul_div_cancel₀ hM0.ne', div_self hδ.1.ne', one_mul]
            rw [e] at h2
            exact h2
        have hcore : ∀ δ ∈ Set.Ioo (0:ℝ) 1, ∀ f ∈ MF, ∀ (B d s κ κb : ℝ) (T : ℕ), 1 ≤ B → (∀ g ∈ F, ∀ S X, |Real.log (f S X / g S X)| ≤ B) → 0 < d → d ≤ 1 →
            (∀ g ∈ F, g ≠ f → d ≤ Dlam U f g) → 0 < s → s * B ≤ 1 → s * B^2 ≤ d → 0 < κ → 0 < κb → 
            (∀ g ∈ F, g ∈ alt p f → κ + s * B^2 ≤ (1 - 1 / (N δ : ℝ)) * Dlam (lam f) f g + 1 / (N δ : ℝ) * Dlam U f g) → 
            κb + s * B^2 ≤ 1 / (N δ : ℝ) * d →
            expTau (fam δ) f ≤ ENNReal.ofReal (((N δ)^2 : ℕ) + T + ((M * Real.exp (s * β δ)) * Real.exp (-(s * κ)) ^ T * (1 + 1 / (s * κ)) +
             (M * Real.exp (s * β δ)) * (Real.exp (s * B * ((N δ)^2 : ℕ)) * (M * Real.exp (-(d^2 / (4 * B^2))) ^ ((N δ)^2))) * (1 + 1 / (s * κb)))) := by
          intro δ hδ f hf B d s κ κb T hB1 hB' hd0 hdle hdU hs hsB hsB2 hκ hκb hκ' hκb'
          have hfF := (hFm f).2 hf
          have hBpos : 0 < B := one_pos.trans_le hB1
          have hge1 : ∀ t, probGT (fam δ) f t ≤ 1 := by
            intro t
            rw [← hcons p (fam δ) f (hadm δ) (hFp f hfF) t]
            exact le_add_self
          have hc0 : 0 ≤ M * Real.exp (s * β δ) := mul_nonneg hM0.le (Real.exp_pos _).le
          have hD0 : 0 ≤ Real.exp (s * B * ((N δ)^2 : ℕ)) * (M * Real.exp (-(d^2 / (4 * B^2))) ^ ((N δ)^2)) := mul_nonneg (Real.exp_pos _).le (mul_nonneg hM0.le (pow_nonneg (Real.exp_pos _).le _))
          refine hsumG (probGT (fam δ) f) ((N δ)^2) T _ _ (s * κ) (s * κb) hc0 hD0 (mul_pos hs hκ) (mul_pos hs hκb) hge1 ?_
          intro m
          have hB2 : 0 < 2 * B^2 := mul_pos two_pos (pow_pos hBpos 2)
          have hs0 : 0 ≤ d / (2 * B^2) := div_nonneg hd0.le hB2.le
          obtain ⟨hs0B, e0, e1⟩ := hnum1 d B hd0 hdle hB1
          have key := hG p (fam δ) f F (F.filter (fun g => g ∈ alt p f)) B s κ κb (d / (2 * B^2)) (d / 2) (β δ) (1 / (N δ : ℝ)) U lam est ((N δ)^2)
            hfF (Finset.filter_subset _ _) ?_ hFp hB' hs.le hsB hs0 hs0B hUs (fun h => hlams _) (hε0 δ) (hε1 δ) (hd1 δ) (hd2 δ) hestF hestmax ?_ ?_ ?_ ?_ ?_ m
          · refine key.trans (le_of_eq ?_)
            rw [e0, ENNReal.ofReal_mul hM0.le, ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_mul hM0.le, ENNReal.ofReal_pow (Real.exp_pos _).le, hM, ENNReal.ofReal_natCast]
          · intro hmem
            have ha := (Finset.mem_filter.1 hmem).2
            obtain ⟨k, hk⟩ := htopex hK p f (hFp f hfF)
            exact ha.2 k k hk hk rfl
          · intro h hh hns
            have hns1 : ¬ ((N δ)^2 ≤ h.length ∧ ∃ f' ∈ F, StopP (β δ) f' h) := by
              rw [hfam] at hns
              exact hns
            have h2 : ¬ StopP (β δ) f h := fun hsp => hns1 ⟨hh, f, hfF, hsp⟩
            rw [hStopP] at h2
            push Not at h2
            obtain ⟨g, hg, hga, hlt⟩ := h2
            exact ⟨g, Finset.mem_filter.2 ⟨hg, hga⟩, hlt⟩
          · intro g hg hgf
            exact e1.le.trans (hdU g hg hgf)
          · intro g hg hgf
            exact hsB2.trans (hdU g hg hgf)
          · intro g hg
            exact hκ' g (Finset.mem_filter.1 hg).1 (Finset.mem_filter.1 hg).2
          · intro g hg hgf
            exact hκb'.trans (mul_le_mul_of_nonneg_left (hdU g hg hgf) (hε0 δ))
        have haltne : ∀ f ∈ MF, ∀ g ∈ alt p f, g ≠ f := by
          intro f hf g hga hgf
          subst hgf
          obtain ⟨k, hk⟩ := htopex hK p g (hsub hf)
          exact hga.2 k k hk hk rfl
        have hDnn : ∀ f ∈ MF, ∀ g ∈ F, 0 ≤ Dlam (lam f) f g := by
          intro f hf g hg
          unfold Dlam
          exact Finset.sum_nonneg fun S _ => mul_nonneg ((hlams f).1 S) (hDSnn p f g (hsub hf) (hFp g hg) S).1
        have hfin : ∀ δ ∈ Set.Ioo (0 : ℝ) 1, ∀ f ∈ MF, expTau (fam δ) f < ⊤ := by
          intro δ hδ f hf
          obtain ⟨B, hB1, hB'⟩ := hB F f
          obtain ⟨d, hd0, hdle, hdU⟩ := hd p U F f hUpos hFp ((hFm f).2 hf)
          have hBpos : 0 < B := one_pos.trans_le hB1
          have hNpos : 0 < (N δ : ℝ) := one_pos.trans_le (hN1 δ)
          have hε : 0 < 1 / (N δ : ℝ) := one_div_pos.2 hNpos
          obtain ⟨hsp, hsB2, hsB, hsd, hh2⟩ := hnum2 d B (1 / (N δ : ℝ)) hd0 hdle hB1 hε (hε1 δ)
          refine lt_of_le_of_lt (hcore δ hδ f hf B d ((1 / (N δ : ℝ) * d) / (2 * B^2)) ((1 / (N δ : ℝ) * d) / 2) ((1 / (N δ : ℝ) * d) / 2) 0 hB1 hB' hd0 hdle hdU hsp hsB hsd hh2 hh2 ?_ ?_) ENNReal.ofReal_lt_top
          · intro g hg hga
            rw [hsB2]
            have h1 := mul_le_mul_of_nonneg_left (hdU g hg (haltne f hf g hga)) hε.le
            have h2 := mul_nonneg (sub_nonneg.2 (hε1 δ)) (hDnn f hf g hg)
            linarith only [h1, h2]
          · rw [hsB2, add_halves]
        refine ⟨fam, ?_, hfin, ?_⟩
        · intro δ hδ
          exact ⟨hadm δ, fun f hf => ⟨hstop_eq p (fam δ) f (hadm δ) (hsub hf) (hfin δ hδ f hf), hwr δ hδ f hf⟩⟩
        · intro f hf
          rw [ENNReal.le_inv_iff_le_inv]
          refine le_of_forall_lt_imp_le_of_dense fun c hc => ?_
          by_cases hc0 : c = 0
          · rw [hc0]; exact zero_le
          have hctop : c ≠ ⊤ := ne_top_of_lt hc
          rw [ENNReal.le_inv_iff_le_inv]
          obtain ⟨b, hcb, hbI⟩ := exists_between hc
          have hbtop : b ≠ ⊤ := ne_top_of_lt hbI
          obtain ⟨r, hr⟩ : ∃ r : ℝ, r = c.toReal := ⟨_, rfl⟩
          obtain ⟨I, hI⟩ : ∃ I : ℝ, I = b.toReal := ⟨_, rfl⟩
          have hr0 : 0 < r := by rw [hr]; exact ENNReal.toReal_pos hc0 hctop
          have hrI : r < I := by rw [hr, hI]; exact (ENNReal.toReal_lt_toReal hctop hbtop).2 hcb
          have hcr : c = ENNReal.ofReal r := by rw [hr, ENNReal.ofReal_toReal hctop]
          have hbIr : b = ENNReal.ofReal I := by rw [hI, ENNReal.ofReal_toReal hbtop]
          have hID : ∀ g ∈ F, g ∈ alt p f → I ≤ Dlam (lam f) f g := by
            intro g hg hga
            have h1 := hbI.le.trans (hlamI f hf g ((hFm g).1 hg) hga)
            rw [hbIr] at h1
            exact (ENNReal.ofReal_le_ofReal_iff (hDnn f hf g hg)).1 h1
          obtain ⟨B, hB1, hB'⟩ := hB F f
          obtain ⟨d, hd0, hdle, hdU⟩ := hd p U F f hUpos hFp ((hFm f).2 hf)
          have hBpos : 0 < B := one_pos.trans_le hB1
          obtain ⟨Y, hY⟩ := hreal M B d (d^2 / (4 * B^2)) ((r + I) / 2) I r (Real.log M) hM1 hB1 hd0 (div_pos (pow_pos hd0 2) (mul_pos four_pos (pow_pos hBpos 2))) hr0 (by linarith only [hrI]) (by linarith only [hrI]) (Real.log_nonneg hM1)
          have hlim : Filter.Tendsto y (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
            have e : y = fun δ => Real.sqrt (Real.sqrt (Real.log (M * δ⁻¹))) := by
              funext δ; rw [hy, hβ, div_eq_mul_inv]
            rw [e]
            exact Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp (tendsto_inv_nhdsGT_zero.const_mul_atTop hM0)))
          have hev : ∀ᶠ δ in nhdsWithin (0:ℝ) (Set.Ioi 0), expTau (fam δ) f / ENNReal.ofReal (Real.log (1 / δ)) ≤ c⁻¹ := by
            filter_upwards [hlim.eventually_ge_atTop Y, Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with δ hYδ hδ
            obtain ⟨c1, c2, c3, c4, c5⟩ := hY (y δ) hYδ (N δ) _ (hyN δ) (hNy δ) rfl
            have hy4 : (y δ)^4 = β δ := by
              have h1 : (y δ)^2 = Real.sqrt (β δ) := by rw [hy]; exact Real.sq_sqrt (Real.sqrt_nonneg _)
              have h2 : (Real.sqrt (β δ))^2 = β δ := Real.sq_sqrt (hβpos δ hδ).le
              rw [← h2, ← h1]; ring
            rw [hy4] at c5
            have hNpos : 0 < (N δ : ℝ) := one_pos.trans_le (hN1 δ)
            have hb := hcore δ hδ f hf B d (1 / (N δ : ℝ)^3) ((r + I) / 2) (d / (2 * N δ)) ⌈β δ / ((r + I) / 2)⌉₊ hB1 hB' hd0 hdle hdU (one_div_pos.2 (pow_pos hNpos 3)) c1 c2 (by linarith only [hrI, hr0]) (div_pos hd0 (mul_pos two_pos hNpos)) ?_ c3
            · have hx : β δ - Real.log M = Real.log (1 / δ) := by
                rw [hβ, Real.log_div hM0.ne' hδ.1.ne', one_div, Real.log_inv]; ring
              rw [hx] at c5
              have hxpos : 0 < Real.log (1 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ.1, one_mul]; exact hδ.2)
              refine ENNReal.div_le_of_le_mul ((hb.trans (ENNReal.ofReal_le_ofReal c5)).trans (le_of_eq ?_))
              rw [hcr, ← ENNReal.ofReal_inv_of_pos hr0, ← ENNReal.ofReal_mul (inv_nonneg.2 hr0.le), div_eq_inv_mul]
            · intro g hg hga
              have h1 := mul_le_mul_of_nonneg_left (hID g hg hga) (sub_nonneg.2 (hε1 δ))
              have h2 := mul_le_mul_of_nonneg_left (hdU g hg (haltne f hf g hga)) (hε0 δ)
              have h3 := mul_nonneg (hε0 δ) hd0.le
              linarith only [c4, h1, h2, h3]
          exact Filter.limsup_le_of_le (h := hev)
