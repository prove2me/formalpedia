-- Prove2me | solution 1 for TradingPostNSW.Leontief.Supplement.theorem_3_9
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:14:15.640378+00:00
-- url     : https://prove2.me/submissions/7aa3474b-49cf-4c99-9623-71900a59246c

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting
import Definitions.Def_TradingPostNSW_Leontief_Supplement_Setting

open TradingPostNSW
open TradingPostNSW.Leontief
open TradingPostNSW.Leontief.Supplement

theorem solution :
    (∀ (n m : ℕ) (I : Instance n m), Standing I →
      ∀ O : (Fin n → Fin m → ℝ) → (Fin m → ℝ) × (Fin n → Fin m → ℝ),
        IsPartialOutcomeRule (· ∈ orthant m) (leoMechEq I) O →
        ∀ s : Fin n → Fin m → ℝ, IsMechPNE (· ∈ orthant m) (leoMechEq I) (u I) O s →
          ∀ y : Fin n → Fin m → ℝ, Feasible I y → NSW I y ≤ (n : ℝ) * NSW I (O s).2) ∧
    (∀ n : ℕ, 0 < n → ∃ (m : ℕ) (I : Instance n m), Standing I ∧
      ∃ y : Fin n → Fin m → ℝ, Feasible I y ∧
        ∀ O : (Fin n → Fin m → ℝ) → (Fin m → ℝ) × (Fin n → Fin m → ℝ),
          IsPartialOutcomeRule (· ∈ orthant m) (leoMechEq I) O →
          SelectsPreferred (· ∈ orthant m) (leoMechEq I) (u I) O →
          ∃ s : Fin n → Fin m → ℝ, IsMechPNE (· ∈ orthant m) (leoMechEq I) (u I) O s ∧
            0 < NSW I (O s).2 ∧ NSW I y = (n : ℝ) * NSW I (O s).2) := by
              have exist : ∀ (n m : ℕ) (a : Fin n → Fin m → ℝ) (Bv : Fin n → ℝ), (∀ k j, 0 ≤ a k j) →
                  (∀ k, ∃ j, 0 < a k j) → (∀ k, 0 < Bv k) →
                  ∃ p : Fin m → ℝ, (∀ j, 0 ≤ p j) ∧ (∀ k, 0 < ∑ l, a k l * p l) ∧
                    (∀ j, ∑ k, Bv k * a k j / (∑ l, a k l * p l) ≤ 1) ∧
                    (∀ j, 0 < p j → ∑ k, Bv k * a k j / (∑ l, a k l * p l) = 1) := by
                  intro n m a Bv ha hapos hB
                  set C : ℝ := ∑ k, Bv k + 1 with hC
                  have hBs : 0 ≤ ∑ k, Bv k := Finset.sum_nonneg fun k _ => (hB k).le
                  let g : (Fin m → ℝ) → ℝ := fun p =>
                    (∏ k, (∑ j, a k j * p j) ^ Bv k) * Real.exp (-∑ j, p j)
                  have hgc : Continuous g := by
                    apply Continuous.mul
                    · apply continuous_finsetProd
                      intro k _
                      apply Continuous.rpow_const
                      · fun_prop
                      · intro _; right; exact (hB k).le
                    · fun_prop
                  have hne : (Set.Icc (0 : Fin m → ℝ) (fun _ => C)).Nonempty :=
                    ⟨fun _ => 1, fun _ => zero_le_one, fun _ => by simp [hC]; linarith⟩
                  obtain ⟨p, hpK, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hgc.continuousOn
                  have hp0 : ∀ j, 0 ≤ p j := fun j => hpK.1 j
                  have hpC : ∀ j, p j ≤ C := fun j => hpK.2 j
                  -- L representation
                  have hgL : ∀ q : Fin m → ℝ, (∀ k, 0 < ∑ j, a k j * q j) →
                      g q = Real.exp (∑ k, Bv k * Real.log (∑ j, a k j * q j) - ∑ j, q j) := by
                    intro q hq
                    simp only [g]
                    rw [sub_eq_add_neg, Real.exp_add, Real.exp_sum]
                    congr 1
                    apply Finset.prod_congr rfl
                    intro k _
                    rw [Real.rpow_def_of_pos (hq k), mul_comm]
                  have hc1 : ∀ k, 0 < ∑ j, a k j * (fun _ => (1:ℝ)) j := by
                    intro k
                    obtain ⟨j, hj⟩ := hapos k
                    simp only [mul_one]
                    exact lt_of_lt_of_le hj (Finset.single_le_sum (fun l _ => ha k l) (Finset.mem_univ j))
                  have hg1 : 0 < g (fun _ => 1) := by rw [hgL _ hc1]; exact Real.exp_pos _
                  have hgp : 0 < g p := lt_of_lt_of_le hg1 (hmax ⟨fun _ => zero_le_one, fun _ => by simp [hC]; linarith⟩)
                  have hcpos : ∀ k, 0 < ∑ j, a k j * p j := by
                    intro k
                    have hnn : 0 ≤ ∑ j, a k j * p j := Finset.sum_nonneg fun j _ => mul_nonneg (ha k j) (hp0 j)
                    rcases hnn.lt_or_eq with h | h
                    · exact h
                    · exfalso
                      have : g p = 0 := by
                        simp only [g]
                        rw [Finset.prod_eq_zero (Finset.mem_univ k) (by rw [← h]; exact Real.zero_rpow (hB k).ne'), zero_mul]
                      linarith
                  set c : Fin n → ℝ := fun k => ∑ j, a k j * p j with hcdef
                  set L : (Fin m → ℝ) → ℝ := fun q => ∑ k, Bv k * Real.log (∑ j, a k j * q j) - ∑ j, q j with hL
                  have hLmax : ∀ q ∈ Set.Icc (0 : Fin m → ℝ) (fun _ => C), (∀ k, 0 < ∑ j, a k j * q j) → L q ≤ L p := by
                    intro q hq hqc
                    have := hmax hq
                    simp only [Set.mem_setOf_eq] at this
                    rw [hgL q hqc, hgL p hcpos] at this
                    exact Real.exp_le_exp.mp this
                  -- perturbation
                  have key : ∀ j (δ : ℝ), -(p j / 2) ≤ δ → p j + δ ≤ C →
                      δ * (∑ k, Bv k * a k j / c k - 1) ≤ 2 * δ ^ 2 * ∑ k, Bv k * (a k j / c k) ^ 2 := by
                    intro j δ hδ1 hδ2
                    set q : Fin m → ℝ := fun l => p l + if l = j then δ else 0 with hq
                    have hqc : ∀ k, ∑ l, a k l * q l = c k + a k j * δ := by
                      intro k
                      simp only [hq, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, hcdef]
                    have hqs : ∑ l, q l = ∑ l, p l + δ := by
                      simp only [hq, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
                    have hajp : ∀ k, a k j * p j ≤ c k := fun k =>
                      Finset.single_le_sum (f := fun l => a k l * p l) (fun l _ => mul_nonneg (ha k l) (hp0 l)) (Finset.mem_univ j)
                    have hz : ∀ k, -(1/2 : ℝ) ≤ a k j * δ / c k := by
                      intro k
                      rw [le_div_iff₀ (hcpos k)]
                      have := hajp k
                      have := ha k j
                      nlinarith
                    have hqpos : ∀ k, 0 < ∑ l, a k l * q l := by
                      intro k
                      rw [hqc]
                      have := hz k
                      rw [le_div_iff₀ (hcpos k)] at this
                      have := hcpos k
                      linarith
                    have hqK : q ∈ Set.Icc (0 : Fin m → ℝ) (fun _ => C) := by
                      constructor
                      · intro l
                        simp only [hq, Pi.zero_apply]
                        split_ifs with h
                        · subst h; linarith [hp0 l]
                        · simpa using hp0 l
                      · intro l
                        simp only [hq]
                        split_ifs with h
                        · subst h; linarith
                        · simpa using hpC l
                    have hle := hLmax q hqK hqpos
                    simp only [hL, hqs] at hle
                    have hlog : ∀ k, Real.log (∑ l, a k l * q l) - Real.log (c k) ≥
                        a k j * δ / c k - 2 * (a k j * δ / c k) ^ 2 := by
                      intro k
                      have hck := hcpos k
                      set z := a k j * δ / c k with hzdef
                      have hqz : ∑ l, a k l * q l = c k * (1 + z) := by
                        rw [hqc, hzdef, mul_add, mul_one, mul_div_cancel₀]; exact hck.ne'
                      have h1z : 0 < 1 + z := by linarith [hz k]
                      rw [hqz, Real.log_mul hck.ne' h1z.ne']
                      have := Real.one_sub_inv_le_log_of_pos h1z
                      have h2 : z - 2 * z ^ 2 ≤ 1 - (1 + z)⁻¹ := by
                        rw [← sub_nonneg]
                        have : 1 - (1 + z)⁻¹ - (z - 2 * z ^ 2) = z ^ 2 * (1 + 2 * z) / (1 + z) := by
                          field_simp; ring
                        rw [this]
                        apply div_nonneg _ h1z.le
                        have := hz k
                        rw [← hzdef] at this
                        nlinarith [sq_nonneg z]
                      linarith
                    have hsum : ∑ k, Bv k * Real.log (∑ l, a k l * q l) - ∑ k, Bv k * Real.log (c k) ≥
                        ∑ k, Bv k * (a k j * δ / c k - 2 * (a k j * δ / c k) ^ 2) := by
                      rw [← Finset.sum_sub_distrib, ge_iff_le]
                      apply Finset.sum_le_sum
                      intro k _
                      rw [← mul_sub]
                      exact mul_le_mul_of_nonneg_left (hlog k) (hB k).le
                    have hexp : ∑ k, Bv k * (a k j * δ / c k - 2 * (a k j * δ / c k) ^ 2) =
                        δ * ∑ k, Bv k * a k j / c k - 2 * δ ^ 2 * ∑ k, Bv k * (a k j / c k) ^ 2 := by
                      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
                      apply Finset.sum_congr rfl
                      intro k _
                      have := (hcpos k).ne'
                      field_simp
                    have : ∑ k, Bv k * Real.log (c k) = ∑ k, Bv k * Real.log (∑ j, a k j * p j) := rfl
                    linarith
                  have hQ : ∀ j, 0 ≤ ∑ k, Bv k * (a k j / c k) ^ 2 := fun j =>
                    Finset.sum_nonneg fun k _ => mul_nonneg (hB k).le (sq_nonneg _)
                  have hB2 : ∀ j, 0 < p j → 1 ≤ ∑ k, Bv k * a k j / c k := by
                    intro j hpj
                    by_contra hS
                    push_neg at hS
                    set S := ∑ k, Bv k * a k j / c k
                    set Q := ∑ k, Bv k * (a k j / c k) ^ 2
                    have hQj := hQ j
                    set t := min (p j / 2) ((1 - S) / (4 * Q + 1)) with ht
                    have htpos : 0 < t := lt_min (by linarith) (div_pos (by linarith) (by linarith))
                    have ht1 : t ≤ p j / 2 := min_le_left _ _
                    have ht2 : t ≤ (1 - S) / (4 * Q + 1) := min_le_right _ _
                    have := key j (-t) (by linarith) (by linarith [hpC j])
                    rw [le_div_iff₀ (by linarith)] at ht2
                    nlinarith
                  have hA : ∀ j, ∑ k, Bv k * a k j / c k ≤ 1 := by
                    intro j
                    by_contra hS
                    push_neg at hS
                    rcases (hpC j).lt_or_eq with hlt | heq
                    · set S := ∑ k, Bv k * a k j / c k
                      set Q := ∑ k, Bv k * (a k j / c k) ^ 2
                      have hQj := hQ j
                      set t := min (C - p j) ((S - 1) / (4 * Q + 1)) with ht
                      have htpos : 0 < t := lt_min (by linarith) (div_pos (by linarith) (by linarith))
                      have ht1 : t ≤ C - p j := min_le_left _ _
                      have ht2 : t ≤ (S - 1) / (4 * Q + 1) := min_le_right _ _
                      have := key j t (by linarith [hp0 j]) (by linarith)
                      rw [le_div_iff₀ (by linarith)] at ht2
                      nlinarith
                    · have hpj : 0 < p j := by rw [heq]; linarith
                      have hle : ∑ k, Bv k * a k j / c k ≤ ∑ k, Bv k / p j := by
                        apply Finset.sum_le_sum
                        intro k _
                        rw [div_le_div_iff₀ (hcpos k) hpj]
                        have : a k j * p j ≤ c k := Finset.single_le_sum (f := fun l => a k l * p l) (fun l _ => mul_nonneg (ha k l) (hp0 l)) (Finset.mem_univ j)
                        have := hB k
                        nlinarith
                      rw [← Finset.sum_div, heq] at hle
                      have h1 : (∑ i, Bv i) / C < 1 := by rw [div_lt_one (by linarith)]; linarith
                      linarith
                  exact ⟨p, hp0, hcpos, hA, fun j hj => le_antisymm (hA j) (hB2 j hj)⟩
                -- equilibrium existence when every good is reported by someone
              have eqGen0 : ∀ (n m : ℕ) (I : Instance n m), 0 < m → (∀ k, 0 < I.B k) →
                  ∀ s' : Fin n → Fin m → ℝ, (∀ k j, 0 ≤ s' k j) → (∀ j, 0 < ∑ k, s' k j) →
                    ∃ p x, leoMechEq I s' p x := by
                  intro n m I hm hB0 s' hs'0 hs'pos
                  classical
                  let a : Fin n → Fin m → ℝ := fun k => if ∃ j, 0 < s' k j then s' k else fun _ => 1
                  have ha0 : ∀ k j, 0 ≤ a k j := by
                    intro k j; simp only [a]; split_ifs
                    · exact hs'0 k j
                    · exact zero_le_one
                  have hapos : ∀ k, ∃ j, 0 < a k j := by
                    intro k; simp only [a]; split_ifs with h
                    · exact h
                    · exact ⟨⟨0, hm⟩, zero_lt_one⟩
                  obtain ⟨p, hp0, hcpos, hA, hEq⟩ := exist n m a I.B ha0 hapos hB0
                  refine ⟨p, fun k j => I.B k * a k j / (∑ l, a k l * p l), ⟨⟨hp0, ?_, hA, ?_, ?_, ?_⟩, ?_⟩⟩
                  · intro k j
                    exact div_nonneg (mul_nonneg (hB0 k).le (ha0 k j)) (hcpos k).le
                  · intro j hj; exact hEq j hj
                  · intro k
                    have hc := (hcpos k).ne'
                    calc ∑ j, I.B k * a k j / (∑ l, a k l * p l) * p j
                        = I.B k / (∑ l, a k l * p l) * ∑ j, a k j * p j := by
                          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
                      _ = I.B k := by field_simp
                  · intro k y hy hbud
                    simp only [leoRep, u, D]
                    by_cases hD : (Finset.univ.filter (fun j => 0 < s' k j)).Nonempty
                    · rw [dif_pos hD, dif_pos hD]
                      have hex : ∃ j, 0 < s' k j := by
                        obtain ⟨j, hj⟩ := hD; exact ⟨j, (Finset.mem_filter.mp hj).2⟩
                      have hak : a k = s' k := by simp only [a]; rw [if_pos hex]
                      have hck := hcpos k
                      rw [hak] at hck
                      have hRHS : I.B k / (∑ l, s' k l * p l) ≤
                          (Finset.univ.filter (fun j => 0 < s' k j)).inf' hD
                            (fun j => I.B k * a k j / (∑ l, a k l * p l) / s' k j) := by
                        apply Finset.le_inf'
                        intro j hj
                        have hsj := (Finset.mem_filter.mp hj).2
                        rw [hak]
                        apply le_of_eq
                        field_simp
                      refine le_trans ?_ hRHS
                      set w := (Finset.univ.filter (fun j => 0 < s' k j)).inf' hD (fun j => y j / s' k j)
                      by_cases hw : w ≤ 0
                      · exact le_trans hw (div_nonneg (hB0 k).le hck.le)
                      · push_neg at hw
                        have hwj : ∀ j, w * s' k j ≤ y j := by
                          intro j
                          by_cases hsj : 0 < s' k j
                          · have := Finset.inf'_le (s := Finset.univ.filter (fun j => 0 < s' k j)) (fun j => y j / s' k j)
                              (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hsj⟩)
                            rw [le_div_iff₀ hsj] at this; exact this
                          · have : s' k j = 0 := le_antisymm (not_lt.mp hsj) (hs'0 k j)
                            rw [this, mul_zero]; exact hy j
                        rw [le_div_iff₀ hck, Finset.mul_sum]
                        calc ∑ j, w * (s' k j * p j) ≤ ∑ j, p j * y j := by
                              apply Finset.sum_le_sum; intro j _
                              have := hwj j; have := hp0 j; nlinarith
                          _ ≤ I.B k := hbud
                    · rw [dif_neg hD, dif_neg hD]
                  · intro j hj; exact absurd hj (hs'pos j).ne'
                -- lower bound at any equilibrium where agent i reports all-ones
              have lowB0 : ∀ (n m : ℕ) (I : Instance n m), (∀ k, 0 < I.B k) → ∀ (i : Fin n) (s' : Fin n → Fin m → ℝ), s' i = (fun _ => 1) → ∀ p' x',
                    leoMechEq I s' p' x' → ∀ j, I.B i / totalBudget I ≤ x' i j := by
                  intro n m I hB0 i s' hsi p' x' hE j
                  obtain ⟨hM, -⟩ := hE
                  have hP : ∑ l, p' l = totalBudget I := by
                    unfold totalBudget
                    rw [← Finset.sum_congr rfl (fun k _ => hM.budget k), Finset.sum_comm]
                    apply Finset.sum_congr rfl
                    intro l _
                    rcases (hM.p_nonneg l).lt_or_eq with h | h
                    · rw [← Finset.sum_mul, hM.sold l h, one_mul]
                    · rw [← h]; simp
                  have hTB : 0 < totalBudget I := by
                    unfold totalBudget
                    exact lt_of_lt_of_le (hB0 i) (Finset.single_le_sum (fun k _ => (hB0 k).le) (Finset.mem_univ i))
                  have hyopt := hM.opt i (fun _ => I.B i / totalBudget I)
                    (fun _ => div_nonneg (hB0 i).le hTB.le)
                    (by rw [← Finset.sum_mul, hP]; field_simp; rfl)
                  simp only [leoRep, u, D, hsi] at hyopt
                  have hD : (Finset.univ.filter (fun _ : Fin m => (0:ℝ) < 1)).Nonempty :=
                    ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, zero_lt_one⟩⟩
                  rw [dif_pos hD, dif_pos hD] at hyopt
                  have h1 : I.B i / totalBudget I ≤ (Finset.univ.filter (fun _ : Fin m => (0:ℝ) < 1)).inf' hD
                      (fun _ => I.B i / totalBudget I / 1) :=
                    Finset.le_inf' _ _ (fun _ _ => by rw [div_one])
                  have h2 := Finset.inf'_le (s := Finset.univ.filter (fun _ : Fin m => (0:ℝ) < 1)) (fun l => x' i l / 1)
                      (Finset.mem_filter.mpr ⟨Finset.mem_univ j, zero_lt_one⟩)
                  simp only [div_one] at h1 h2 hyopt ⊢
                  exact le_trans h1 (le_trans hyopt h2)
              refine ⟨?_, ?_⟩
              · intro n m I hI
                have hB0 : ∀ k, 0 < I.B k := fun k => lt_of_lt_of_le zero_lt_one (hI.one_le_B k)
                have eqGen := eqGen0 n m I hI.pos_m hB0
                have lowB := lowB0 n m I hB0
                intro O hO s hs y hy
                obtain ⟨hadm, hex, hdev⟩ := hs
                have hm0 := hI.pos_m
                rcases Nat.eq_zero_or_pos n with hn | hn
                · subst hn
                  exfalso
                  have := hy.2 ⟨0, hm0⟩
                  simp at this
                have hTB : 0 < totalBudget I := by
                  unfold totalBudget
                  exact lt_of_lt_of_le (hB0 ⟨0, hn⟩) (Finset.single_le_sum (fun k _ => (hB0 k).le) (Finset.mem_univ _))
                have hadm0 : ∀ k j, 0 ≤ s k j := by
                  intro k j
                  have := hadm k
                  simp only [orthant, Set.mem_setOf_eq] at this
                  exact this j
                have hy1 : ∀ i j, y i j ≤ 1 := by
                  intro i j
                  rw [← hy.2 j]
                  exact Finset.single_le_sum (fun k _ => hy.1 k j) (Finset.mem_univ i)
                have hY0 : ∀ i, 0 ≤ u I i (y i) := by
                  intro i
                  unfold u
                  rw [dif_pos (hI.D_nonempty i)]
                  apply Finset.le_inf'
                  intro j _
                  exact div_nonneg (hy.1 i j) (hI.v_nonneg i j)
                have hagent : ∀ i, I.B i / totalBudget I * u I i (y i) ≤ u I i ((O s).2 i) := by
                  intro i
                  set s' := Function.update s i (fun _ => (1:ℝ)) with hs'def
                  have hs'0 : ∀ k j, 0 ≤ s' k j := by
                    intro k j
                    by_cases h : k = i
                    · subst h; simp [s']
                    · simp only [s', Function.update_of_ne h]; exact hadm0 k j
                  have hs'i : s' i = fun _ => (1:ℝ) := by simp [s']
                  have hs'pos : ∀ j, 0 < ∑ k, s' k j := by
                    intro j
                    have : s' i j ≤ ∑ k, s' k j :=
                      Finset.single_le_sum (fun k _ => hs'0 k j) (Finset.mem_univ i)
                    rw [hs'i] at this
                    linarith
                  obtain ⟨p, x, hE⟩ := eqGen s' hs'0 hs'pos
                  have hadm' : (fun _ => (1:ℝ)) ∈ orthant m := fun _ => zero_le_one
                  have h1 := hdev i (fun _ => 1) hadm' ⟨p, x, hE⟩
                  have hadms' : ∀ k, s' k ∈ orthant m := fun k j => hs'0 k j
                  have hE' := hO s' hadms' ⟨p, x, hE⟩
                  have hlow := lowB i s' hs'i _ _ hE'
                  refine le_trans ?_ h1
                  unfold u
                  rw [dif_pos (hI.D_nonempty i), dif_pos (hI.D_nonempty i)]
                  apply Finset.le_inf'
                  intro j hj
                  have hv : 0 < I.v i j := (Finset.mem_filter.mp hj).2
                  have hwn : 0 ≤ I.B i / totalBudget I := div_nonneg (hB0 i).le hTB.le
                  calc I.B i / totalBudget I * (D I i).inf' (hI.D_nonempty i) (fun j => y i j / I.v i j)
                      ≤ I.B i / totalBudget I * (y i j / I.v i j) :=
                        mul_le_mul_of_nonneg_left (Finset.inf'_le _ hj) hwn
                    _ ≤ I.B i / totalBudget I * (1 / I.v i j) := by
                        apply mul_le_mul_of_nonneg_left _ hwn
                        exact div_le_div_of_nonneg_right (hy1 i j) hv.le
                    _ = (I.B i / totalBudget I) / I.v i j := by ring
                    _ ≤ (O s').2 i j / I.v i j := div_le_div_of_nonneg_right (hlow j) hv.le
                -- NSW assembly
                unfold NSW
                set w : Fin n → ℝ := fun i => I.B i / totalBudget I with hwdef
                have hw0 : ∀ i, 0 < w i := fun i => div_pos (hB0 i) hTB
                have hwsum : ∑ i, w i = 1 := by
                  simp only [w, ← Finset.sum_div]
                  exact div_self hTB.ne'
                have hGpos : 0 < ∏ i, w i ^ w i := Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hw0 i) _
                have hG : 1 ≤ (n : ℝ) * ∏ i, w i ^ w i := by
                  have am := Real.geom_mean_le_arith_mean_weighted Finset.univ w (fun i => (w i)⁻¹)
                    (fun i _ => (hw0 i).le) hwsum (fun i _ => inv_nonneg.mpr (hw0 i).le)
                  rw [Finset.sum_congr rfl (fun i _ => mul_inv_cancel₀ (hw0 i).ne'), Finset.sum_const,
                    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at am
                  rw [Finset.prod_congr rfl (fun i _ => Real.inv_rpow (hw0 i).le (w i)),
                    Finset.prod_inv_distrib] at am
                  have := mul_le_mul_of_nonneg_right am hGpos.le
                  rwa [inv_mul_cancel₀ hGpos.ne'] at this
                have hGeq : ∏ i, w i ^ w i = (∏ i, w i ^ I.B i) ^ (1 / totalBudget I) := by
                  rw [← Real.finsetProd_rpow _ _ (fun i _ => Real.rpow_nonneg (hw0 i).le _)]
                  apply Finset.prod_congr rfl
                  intro i _
                  rw [← Real.rpow_mul (hw0 i).le]
                  congr 1
                  simp only [w]; ring
                have hstep : (∏ i, w i ^ w i) * (∏ i, u I i (y i) ^ I.B i) ^ (1 / totalBudget I) ≤
                    (∏ i, u I i ((O s).2 i) ^ I.B i) ^ (1 / totalBudget I) := by
                  rw [hGeq, ← Real.mul_rpow (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hw0 i).le _)
                    (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hY0 i) _), ← Finset.prod_mul_distrib]
                  apply Real.rpow_le_rpow (Finset.prod_nonneg fun i _ =>
                    mul_nonneg (Real.rpow_nonneg (hw0 i).le _) (Real.rpow_nonneg (hY0 i) _))
                  · apply Finset.prod_le_prod
                    · intro i _; exact mul_nonneg (Real.rpow_nonneg (hw0 i).le _) (Real.rpow_nonneg (hY0 i) _)
                    · intro i _
                      rw [← Real.mul_rpow (hw0 i).le (hY0 i)]
                      exact Real.rpow_le_rpow (mul_nonneg (hw0 i).le (hY0 i)) (hagent i) (hB0 i).le
                  · exact div_nonneg zero_le_one hTB.le
                have hNy : 0 ≤ (∏ i, u I i (y i) ^ I.B i) ^ (1 / totalBudget I) :=
                  Real.rpow_nonneg (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hY0 i) _) _
                have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
                calc (∏ i, u I i (y i) ^ I.B i) ^ (1 / totalBudget I)
                    ≤ ((n : ℝ) * ∏ i, w i ^ w i) * (∏ i, u I i (y i) ^ I.B i) ^ (1 / totalBudget I) :=
                      le_mul_of_one_le_left hNy hG
                  _ = (n : ℝ) * ((∏ i, w i ^ w i) * (∏ i, u I i (y i) ^ I.B i) ^ (1 / totalBudget I)) := by ring
                  _ ≤ (n : ℝ) * (∏ i, u I i ((O s).2 i) ^ I.B i) ^ (1 / totalBudget I) :=
                      mul_le_mul_of_nonneg_left hstep hn0
              · intro n hn
                let I : Instance n n := ⟨fun i j => if i = j then 1 else 0, fun _ => 1⟩
                have hIv : ∀ i j, I.v i j = if i = j then 1 else 0 := fun _ _ => rfl
                have hIB : ∀ i, I.B i = 1 := fun _ => rfl
                have hDi : ∀ i, D I i = {i} := by
                  intro i; ext j
                  simp only [D, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hIv]
                  by_cases h : i = j
                  · subst h; simp
                  · simp [h, Ne.symm h]
                have hSt : Standing I := by
                  refine ⟨hn, ?_, ?_, ?_⟩
                  · intro i j; rw [hIv]; split_ifs <;> norm_num
                  · intro i; rw [hIB]
                  · intro i; rw [hDi]; exact Finset.singleton_nonempty i
                have hu : ∀ i z, u I i z = z i := by
                  intro i z
                  unfold u
                  rw [dif_pos (hSt.D_nonempty i)]
                  simp [hDi, Finset.inf'_singleton, hIv]
                have hTB : totalBudget I = n := by simp [totalBudget, hIB]
                have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
                have hB0 : ∀ k, 0 < I.B k := fun k => by rw [hIB]; exact zero_lt_one
                have eqGen := eqGen0 n n I hn hB0
                have lowB := lowB0 n n I hB0
                -- upper bound on agent i's own good when everyone else reports all-ones
                have upB : ∀ (i : Fin n) (s' : Fin n → Fin n → ℝ), (∀ k, k ≠ i → s' k = fun _ => 1) →
                    ∀ p x, leoMechEq I s' p x → x i i ≤ 1 / n := by
                  intro i s' hs' p x hE
                  have hsup := hE.1.supply i
                  have hk : ∀ k ∈ Finset.univ.erase i, 1 / (n:ℝ) ≤ x k i := by
                    intro k hk
                    have := lowB k s' (hs' k (Finset.ne_of_mem_erase hk)) p x hE i
                    rwa [hIB, hTB] at this
                  have hsum := Finset.sum_le_sum hk
                  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
                    Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub hn] at hsum
                  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hsup
                  have : ((n:ℝ) - 1) * (1 / n) = 1 - 1 / n := by field_simp
                  simp only [Nat.cast_one] at hsum
                  linarith
                set s : Fin n → Fin n → ℝ := fun _ _ => 1 with hsdef
                have hs0 : ∀ k j, 0 ≤ s k j := fun _ _ => zero_le_one
                have hspos : ∀ j, 0 < ∑ k, s k j := by
                  intro j; simp only [s, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]; exact hnR
                refine ⟨n, I, hSt, fun i j => if i = j then 1 else 0, ⟨?_, ?_⟩, ?_⟩
                · intro i j; dsimp only; split_ifs <;> norm_num
                · intro j; simp
                intro O hO _hsel
                have hadm : ∀ k, s k ∈ orthant n := fun k j => zero_le_one
                have hex : ∃ p x, leoMechEq I s p x := eqGen s hs0 hspos
                have hEs := hO s hadm hex
                have hxs : ∀ i, (O s).2 i i = 1 / n := by
                  intro i
                  apply le_antisymm (upB i s (fun k _ => rfl) _ _ hEs)
                  have := lowB i s rfl _ _ hEs i
                  rwa [hIB, hTB] at this
                refine ⟨s, ⟨hadm, hex, ?_⟩, ?_, ?_⟩
                · intro i r hr hexr
                  rw [hu, hu, hxs i]
                  have hadm' : ∀ k, Function.update s i r k ∈ orthant n := by
                    intro k
                    by_cases hk : k = i
                    · subst hk; simpa using hr
                    · rw [Function.update_of_ne hk]; exact hadm k
                  exact upB i (Function.update s i r) (fun k hk => by rw [Function.update_of_ne hk]) _ _
                    (hO _ hadm' hexr)
                · unfold NSW
                  simp only [hu, hxs, hTB, hIB, Real.rpow_one]
                  positivity
                · unfold NSW
                  simp only [hu, hxs, hTB, hIB, Real.rpow_one]
                  simp only [if_true, Finset.prod_const_one, Real.one_rpow, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
                  rw [one_div (n:ℝ), Real.pow_rpow_inv_natCast (by positivity) hn.ne']
                  field_simp
