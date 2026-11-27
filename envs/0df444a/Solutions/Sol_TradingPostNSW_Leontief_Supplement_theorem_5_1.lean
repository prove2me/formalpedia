-- Prove2me | solution 1 for TradingPostNSW.Leontief.Supplement.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:18:43.657949+00:00
-- url     : https://prove2.me/submissions/039e6914-d880-46be-856e-0b629d0aed6d

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting
import Definitions.Def_TradingPostNSW_Leontief_Supplement_Setting

open TradingPostNSW
open TradingPostNSW.Leontief
open TradingPostNSW.Leontief.Supplement

theorem solution :
    (∀ (n m : ℕ) (I : Instance n m), GenStanding I →
      ∀ U : Fin n → (Fin m → ℝ) → ℝ, (∀ i, IsConcaveUtility (U i)) →
      ∀ O : (Fin n → (Fin m → ℝ) → ℝ) → (Fin m → ℝ) × (Fin n → Fin m → ℝ),
        IsOutcomeRule IsConcaveUtility (concaveMarketEq I) O →
        ∀ W : Fin n → (Fin m → ℝ) → ℝ, IsMechPNE IsConcaveUtility (concaveMarketEq I) U O W →
          ∀ i, I.B i / totalBudget I * U i 1 ≤ U i ((O W).2 i)) ∧
    (∀ (n m : ℕ) (I : Instance n m), GenStanding I →
      ∀ U : Fin n → (Fin m → ℝ) → ℝ, (∀ i, IsConcaveUtility (U i)) →
      (∀ i, StrictMonoOn (U i) (box m)) →
      ∀ b : Fin n → Fin m → ℝ, IsPNEU I U 0 b →
        ∀ i, I.B i / totalBudget I * U i 1 ≤ U i (tpAlloc 0 b i)) ∧
    (∀ (n m : ℕ) (I : Instance n m), GenStanding I →
      ∀ U : Fin n → (Fin m → ℝ) → ℝ, (∀ i, IsConcaveUtility (U i)) →
      (∀ i, StrictMonoOn (U i) (box m)) →
      ∀ Δ : ℝ, 0 < Δ → Δ < 1 / (m : ℝ) →
      ∀ b : Fin n → Fin m → ℝ, IsPNEU I U Δ b →
        ∀ i, I.B i / totalBudget I * (1 - Δ * ((m : ℝ) - 1) / I.B i) * U i 1 ≤
          U i (tpAlloc Δ b i)) := by
            classical
            have hbudget : ∀ {n m : ℕ} (I : Instance n m), GenStanding I → ∀ i,
                0 < I.B i ∧ I.B i ≤ totalBudget I ∧ 0 < totalBudget I := by
              intro n m I hI i
              have hn : ∀ k, 0 ≤ I.B k := fun k => le_trans (by norm_num) (hI.one_le_B k)
              have hi : 0 < I.B i := lt_of_lt_of_le (by norm_num) (hI.one_le_B i)
              have hs : I.B i ≤ totalBudget I := Finset.single_le_sum (fun k _ => hn k) (Finset.mem_univ i)
              exact ⟨hi, hs, lt_of_lt_of_le hi hs⟩
            have hconc : ∀ {m : ℕ} (f : (Fin m → ℝ) → ℝ), IsConcaveUtility f →
                ∀ (t : ℝ), 0 ≤ t → t ≤ 1 → ∀ x ∈ box m, (∀ j, t ≤ x j) →
                t * f 1 ≤ f x := by
              intro m f hf t ht ht1 x hx htx
              have h0 : (0 : Fin m → ℝ) ∈ box m := ⟨le_refl _, zero_le_one⟩
              have h1 : (1 : Fin m → ℝ) ∈ box m := ⟨zero_le_one, le_refl _⟩
              have htbox : (t • (1 : Fin m → ℝ)) ∈ box m := by
                constructor
                · intro j; simpa using ht
                · intro j; simpa using ht1
              have hc := hf.1.2 h1 h0 ht (sub_nonneg.mpr ht1) (by ring : t + (1-t) = 1)
              simp only [smul_zero, add_zero, smul_eq_mul] at hc
              have hm := hf.2.1 htbox hx (show t • (1 : Fin m → ℝ) ≤ x from fun j => by simpa using htx j)
              have hn := mul_nonneg (sub_nonneg.mpr ht1) (hf.2.2 0 h0)
              linarith
            have hbid : ∀ {m : ℕ}, 0 < m → ∀ (q : Fin m → ℝ), (∀ j, 0 ≤ q j) →
                ∀ R ε : ℝ, 0 < ε → (m : ℝ) * ε < R →
                ∃ r : Fin m → ℝ, (∀ j, ε ≤ r j) ∧ (∑ j, r j = R) ∧
                  ∀ j, (R - ((m : ℝ) - 1) * ε) * (r j + q j) ≤
                    (R + ∑ k, q k) * r j := by
              intro m hm q hq R ε hε hR
              let Q := ∑ j, q j
              let a := R - ((m : ℝ) - 1) * ε
              let c := a / Q
              let r₀ := fun j => max ε (c * q j)
              have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
              have hQ : 0 ≤ Q := Finset.sum_nonneg (fun j _ => hq j)
              have ha : 0 < a := by dsimp [a]; nlinarith
              have hc : 0 ≤ c := div_nonneg (le_of_lt ha) hQ
              have hcQ : c * Q ≤ a := by
                by_cases hz : Q = 0
                · simp [hz, le_of_lt ha]
                · dsimp [c]; rw [div_mul_cancel₀ _ hz]
              have hs0 : ∑ j, r₀ j ≤ R := by
                by_cases hex : ∃ j, ε ≤ c * q j
                · obtain ⟨j₁, hj₁⟩ := hex
                  have hb : ∑ j, r₀ j ≤ ∑ j, (c * q j + if j = j₁ then 0 else ε) := by
                    apply Finset.sum_le_sum
                    intro j _
                    by_cases hj : j = j₁
                    · subst j; simp [r₀, max_eq_right hj₁]
                    · simp only [hj, ↓reduceIte]
                      exact max_le (by linarith [mul_nonneg hc (hq j)]) (by linarith)
                  have hsum : ∑ j, (if j = j₁ then (0 : ℝ) else ε) = ((m : ℝ) - 1) * ε := by
                    have he := Finset.sum_erase_add (s := Finset.univ) (f := fun _ : Fin m => ε) (Finset.mem_univ j₁)
                    have hh : (∑ j : Fin m, if j = j₁ then (0 : ℝ) else ε) =
                        ∑ j ∈ Finset.univ.erase j₁, ε := by
                      rw [← Finset.sum_erase (s := Finset.univ) (a := j₁) (by simp : (if j₁ = j₁ then (0 : ℝ) else ε) = 0)]
                      apply Finset.sum_congr rfl
                      intro j hj
                      simp [(Finset.mem_erase.mp hj).1]
                    rw [hh]
                    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at he
                    simp only [Finset.sum_const, nsmul_eq_mul, Fintype.card_fin] at *
                    linarith
                  rw [Finset.sum_add_distrib, hsum, ← Finset.mul_sum] at hb
                  dsimp [Q] at hcQ
                  dsimp [a] at hcQ
                  linarith
                · have hr : ∀ j, r₀ j = ε := by
                    intro j
                    exact max_eq_left (le_of_lt (lt_of_not_ge (fun h => hex ⟨j, h⟩)))
                  simp_rw [hr]
                  simpa using le_of_lt hR
              let j₀ : Fin m := ⟨0, hm⟩
              let r := fun j => r₀ j + if j = j₀ then R - ∑ k, r₀ k else 0
              have hrr : ∀ j, r₀ j ≤ r j := by
                intro j
                dsimp [r]
                split_ifs <;> linarith
              have hrpos : ∀ j, ε ≤ r j := fun j => le_trans (le_max_left _ _) (hrr j)
              refine ⟨r, hrpos, ?_, ?_⟩
              · dsimp [r]
                rw [Finset.sum_add_distrib]
                simp
              · intro j
                have hqQ : q j ≤ Q := Finset.single_le_sum (fun k _ => hq k) (Finset.mem_univ j)
                have hrel : a * q j ≤ Q * (c * q j) := by
                  by_cases hz : Q = 0
                  · have hzero : q j = 0 := le_antisymm (by simpa [hz] using hqQ) (hq j)
                    simp [hzero]
                  · dsimp [c]
                    rw [← mul_assoc, mul_div_cancel₀ _ hz]
                have hcr : c * q j ≤ r j := le_trans (le_max_right _ _) (hrr j)
                have hmult := mul_le_mul_of_nonneg_left hcr hQ
                have hrest : 0 ≤ ((m : ℝ) - 1) * ε * r j :=
                  mul_nonneg (mul_nonneg (sub_nonneg.mpr hm1) (le_of_lt hε))
                    (le_trans (le_of_lt hε) (hrpos j))
                dsimp [a] at hrel
                dsimp [Q] at hmult hrel
                nlinarith
            have htp : ∀ {n m : ℕ} (I : Instance n m), GenStanding I →
                ∀ (U : Fin n → (Fin m → ℝ) → ℝ), (∀ i, IsConcaveUtility (U i)) →
                ∀ (δ : ℝ) (b : Fin n → Fin m → ℝ), IsPNEU I U δ b →
                ∀ (i : Fin n) (ε : ℝ), 0 < ε → δ ≤ ε → (m : ℝ) * ε < I.B i →
                  (I.B i - ((m : ℝ) - 1) * ε) / totalBudget I * U i 1 ≤
                    U i (tpAlloc δ b i) := by
              intro n m I hI U hU δ b hb i ε hε hδε hmε
              obtain ⟨hBi, hBT, hT⟩ := hbudget I hI i
              have hbn : ∀ k j, 0 ≤ b k j := fun k j => (hb.1 k).1 j |>.1
              let q := fun j => ∑ k ∈ Finset.univ.erase i, b k j
              have hq : ∀ j, 0 ≤ q j := fun j => Finset.sum_nonneg (fun k _ => hbn k j)
              have hQ : I.B i + ∑ j, q j = totalBudget I := by
                dsimp [q]
                rw [Finset.sum_comm]
                simp_rw [(hb.1 _).2]
                exact Finset.add_sum_erase Finset.univ I.B (Finset.mem_univ i)
              obtain ⟨r, hrε, hrs, hrbound⟩ := hbid hI.pos_m q hq (I.B i) ε hε hmε
              have hrp : ∀ j, 0 < r j := fun j => lt_of_lt_of_le hε (hrε j)
              have hrn : ∀ j, 0 ≤ r j := fun j => le_of_lt (hrp j)
              have hstr : Strategy I i r := by
                refine ⟨fun j => ⟨hrn j, ?_⟩, hrs⟩
                rw [← hrs]
                exact Finset.single_le_sum (fun k _ => hrn k) (Finset.mem_univ j)
              let s := Function.update b i r
              have hei : ∀ j, effBid δ s i j = r j := by
                intro j
                simp [effBid, s, le_trans hδε (hrε j)]
              have hen : ∀ k j, 0 ≤ effBid δ s k j := by
                intro k j
                have hsn : 0 ≤ s k j := by
                  by_cases hk : k = i
                  · subst k; simpa [s] using hrn j
                  · simpa [s, hk] using hbn k j
                dsimp [effBid]
                split_ifs <;> linarith
              have hes : ∀ j, ∑ k, effBid δ s k j ≤ r j + q j := by
                intro j
                rw [← Finset.add_sum_erase Finset.univ (fun k => effBid δ s k j) (Finset.mem_univ i), hei]
                apply add_le_add_right
                apply Finset.sum_le_sum
                intro k hk
                have hki : k ≠ i := (Finset.mem_erase.mp hk).1
                dsimp [effBid]
                simp only [s, Function.update_of_ne hki]
                split_ifs <;> linarith [hbn k j]
              have hed : ∀ j, r j ≤ ∑ k, effBid δ s k j := by
                intro j
                rw [← hei j]
                exact Finset.single_le_sum (fun k _ => hen k j) (Finset.mem_univ i)
              have hdp : ∀ j, 0 < ∑ k, effBid δ s k j := fun j => lt_of_lt_of_le (hrp j) (hed j)
              have hx : ∀ j, tpAlloc δ s i j = r j / ∑ k, effBid δ s k j := by
                intro j
                simp [tpAlloc, hei, hrp]
              have hxbox : tpAlloc δ s i ∈ box m := by
                constructor
                · intro j
                  rw [hx]
                  exact div_nonneg (hrn j) (le_of_lt (hdp j))
                · intro j
                  rw [hx]
                  exact (div_le_one (hdp j)).mpr (hed j)
              let a := I.B i - ((m : ℝ) - 1) * ε
              have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hI.pos_m
              have ha : 0 ≤ a := by dsimp [a]; nlinarith
              have haB : a ≤ I.B i := by
                dsimp [a]
                exact sub_le_self _ (mul_nonneg (sub_nonneg.mpr hm1) (le_of_lt hε))
              have ht0 : 0 ≤ a / totalBudget I := div_nonneg ha (le_of_lt hT)
              have ht1 : a / totalBudget I ≤ 1 := (div_le_one hT).mpr (le_trans haB hBT)
              have hshare : ∀ j, a / totalBudget I ≤ tpAlloc δ s i j := by
                intro j
                rw [hx, div_le_div_iff₀ hT (hdp j)]
                have hh := mul_le_mul_of_nonneg_left (hes j) ha
                have hr := hrbound j
                rw [hQ] at hr
                dsimp [a] at hh
                nlinarith
              exact le_trans (hconc (U i) (hU i) _ ht0 ht1 _ hxbox hshare) (hb.2 i r hstr)
            constructor
            · intro n m I hI U hU O hO W hW i
              let V := Function.update W i (U i)
              have hV : ∀ k, IsConcaveUtility (V k) := by
                intro k
                by_cases hk : k = i
                · subst k; simpa [V] using hU i
                · simpa [V, hk] using hW.1 k
              have he : concaveMarketEq I V (O V).1 (O V).2 := hO V hV
              have hdev := hW.2.2 i (U i) (hU i) ⟨(O V).1, (O V).2, he⟩
              obtain ⟨hBi, hBT, hT⟩ := hbudget I hI i
              have hprice : ∑ j, (O V).1 j = totalBudget I := by
                calc
                  ∑ j, (O V).1 j = ∑ j, (∑ k, (O V).2 k j) * (O V).1 j := by
                    apply Finset.sum_congr rfl
                    intro j _
                    by_cases hp : (O V).1 j = 0
                    · simp [hp]
                    · rw [he.sold j (lt_of_le_of_ne (he.p_nonneg j) (Ne.symm hp)), one_mul]
                  _ = ∑ k, ∑ j, (O V).2 k j * (O V).1 j := by
                    simp_rw [Finset.sum_mul]
                    rw [Finset.sum_comm]
                  _ = totalBudget I := by simp_rw [he.budget]; rfl
              let t := I.B i / totalBudget I
              have ht : 0 ≤ t := le_of_lt (div_pos hBi hT)
              have ht1 : t ≤ 1 := (div_le_one hT).mpr hBT
              have hbox : (t • (1 : Fin m → ℝ)) ∈ box m := by
                constructor
                · intro j; simpa using ht
                · intro j; simpa using ht1
              have haff : ∑ j, (O V).1 j * (t • (1 : Fin m → ℝ)) j ≤ I.B i := by
                simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
                rw [← Finset.sum_mul, hprice]
                dsimp [t]
                rw [mul_div_cancel₀ _ (ne_of_gt hT)]
              have hopt := he.opt i (t • (1 : Fin m → ℝ)) hbox haff
              have hc := hconc (U i) (hU i) t ht ht1 _ hbox (by intro j; simp)
              have hh : V i = U i := by simp [V]
              rw [hh] at hopt
              exact le_trans hc (le_trans hopt hdev)
            · constructor
              · intro n m I hI U hU _ b hb i
                obtain ⟨hBi, hBT, hT⟩ := hbudget I hI i
                have hc : Continuous (fun ε : ℝ =>
                    (I.B i - ((m : ℝ) - 1) * ε) / totalBudget I * U i 1) := by fun_prop
                have hlim : Filter.Tendsto (fun ε : ℝ =>
                    (I.B i - ((m : ℝ) - 1) * ε) / totalBudget I * U i 1)
                    (nhdsWithin 0 (Set.Ioi 0)) (nhds (I.B i / totalBudget I * U i 1)) := by
                  simpa using (hc.continuousAt (x := 0)).tendsto.mono_left
                    (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0)
                apply le_of_tendsto hlim
                have hsmall : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0), (m : ℝ) * ε < I.B i := by
                  have hcont : Continuous (fun ε : ℝ => (m : ℝ) * ε) := by fun_prop
                  exact (hcont.continuousAt.eventually (gt_mem_nhds (by simpa using hBi))).filter_mono nhdsWithin_le_nhds
                filter_upwards [hsmall, self_mem_nhdsWithin] with ε hsmall hpos
                exact htp I hI U hU 0 b hb i ε hpos (le_of_lt hpos) hsmall
              · intro n m I hI U hU _ Δ hΔ hΔm b hb i
                have hm : (0 : ℝ) < m := by exact_mod_cast hI.pos_m
                have hmΔ : (m : ℝ) * Δ < I.B i := by
                  have hh : Δ * (m : ℝ) < 1 := (lt_div_iff₀ hm).mp hΔm
                  nlinarith [hI.one_le_B i]
                have h := htp I hI U hU Δ b hb i Δ hΔ le_rfl hmΔ
                have hBi := (hbudget I hI i).1
                have heq : I.B i / totalBudget I * (1 - Δ * ((m : ℝ) - 1) / I.B i) =
                    (I.B i - ((m : ℝ) - 1) * Δ) / totalBudget I := by
                  field_simp
                  <;> ring
                rw [heq]
                exact h
