-- Prove2me | solution 1 for PosetSecretary.ProxyLabel.label_max_prob
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T16:21:37.893829+00:00
-- url     : https://prove2.me/submissions/17330c5e-2a5d-45d5-81ec-cf28147afc3c

import Mathlib
import Definitions.Def_AppliedComb_Posets_width
import Definitions.Def_PosetSecretary_ProxyLabel_Setting

open PosetSecretary.ProxyLabel

theorem solution {α : Type*} [Fintype α] [DecidableEq α] (w : α → ℝ)
    (hinj : Function.Injective w) (k : ℕ) (hk : 1 ≤ k) (a : α) (j : ℕ) (hj : 1 ≤ j)
    (hjk : j ≤ k) (hrank : (Finset.univ.filter (fun b => w a < w b)).card = j - 1) :
    labelMaxProb w k a = (1 - 1 / (k : ℝ)) ^ (j - 1) ∧
      (1 - 1 / (k : ℝ)) ^ (k - 1) ≤ (1 - 1 / (k : ℝ)) ^ (j - 1) ∧
      1 / Real.exp 1 ≤ (1 - 1 / (k : ℝ)) ^ (k - 1) := by
  classical
  set N := Fintype.card α
  set U := Finset.univ.filter (fun b => w a < w b) with hU
  have haU : a ∉ U := by simp [hU]
  -- cardinality of the complement of U minus a
  set V := Finset.univ.filter (fun b => ¬ w a < w b ∧ b ≠ a) with hV
  have hVcard : V.card = N - j := by
    have hdisj : Disjoint U (insert a V) := by
      rw [Finset.disjoint_left]
      intro b hb hb'
      simp only [hU, hV, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert] at hb hb'
      rcases hb' with rfl | hb'
      · exact lt_irrefl _ hb
      · exact hb'.1 hb
    have hunion : U ∪ insert a V = Finset.univ := by
      ext b
      simp only [hU, hV, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, iff_true]
      by_cases h1 : w a < w b
      · exact Or.inl h1
      · by_cases h2 : b = a
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr ⟨h1, h2⟩)
    have haV : a ∉ V := by simp [hV]
    have := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_insert_of_notMem haV, Finset.card_univ] at this
    have : U.card = j - 1 := hrank
    omega
  set P : (α → Fin k) → Prop := fun ℓ => ∀ b, w a < w b → ℓ b ≠ ℓ a
  have hcount : (Finset.univ.filter P).card = k * ((k - 1) ^ (j - 1) * k ^ (N - j)) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun ℓ => ℓ a) (t := Finset.univ)
      (by intro x _; simp)]
    have hfib : ∀ i : Fin k, ((Finset.univ.filter P).filter (fun ℓ => ℓ a = i)).card
        = (k - 1) ^ (j - 1) * k ^ (N - j) := by
      intro i
      set t : ∀ b : α, Finset (Fin k) := fun b =>
        if b = a then {i} else if w a < w b then Finset.univ.erase i else Finset.univ
      have heq : (Finset.univ.filter P).filter (fun ℓ => ℓ a = i) = Fintype.piFinset t := by
        ext ℓ
        simp only [P, t, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
        constructor
        · rintro ⟨h1, h2⟩ b
          by_cases hb : b = a
          · subst hb; simp [h2]
          · simp only [hb, if_false]
            split_ifs with hab
            · simp only [Finset.mem_erase, Finset.mem_univ, and_true]
              rw [← h2]; exact h1 b hab
            · simp
        · intro h
          have ha := h a
          simp only [if_true, Finset.mem_singleton] at ha
          refine ⟨fun b hab => ?_, ha⟩
          have hb : b ≠ a := by rintro rfl; exact lt_irrefl _ hab
          have := h b
          simp only [hb, hab, if_false, if_true, Finset.mem_erase] at this
          rw [ha]; exact this.1
      rw [heq, Fintype.card_piFinset]
      have hpt : ∀ b, (t b).card =
          (if w a < w b then k - 1 else if b = a then 1 else k) := by
        intro b
        by_cases hb : b = a
        · subst hb; simp [t]
        · by_cases hab : w a < w b
          · simp [t, hb, hab, Finset.card_erase_of_mem]
          · simp [t, hb, hab]
      simp_rw [hpt]
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_ite, Finset.prod_const_one,
        Finset.prod_const, one_mul]
      congr 1
      · show (k - 1) ^ U.card = _
        rw [hrank]
      · congr 1
        rw [← hVcard, Finset.filter_filter]
    rw [Finset.sum_congr rfl (fun i _ => hfib i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (k : ℝ) ≠ 0 := by linarith
  have hNj : j ≤ N := by
    have := Finset.card_le_card (Finset.subset_univ (insert a U))
    rw [Finset.card_insert_of_notMem haU, Finset.card_univ] at this
    have h2 : U.card = j - 1 := hrank
    omega
  have hbase0 : 0 ≤ 1 - 1 / (k : ℝ) := by
    rw [sub_nonneg, div_le_one (by linarith)]; exact hkR
  have hbase1 : 1 - 1 / (k : ℝ) ≤ 1 := by
    have : 0 ≤ 1 / (k : ℝ) := by positivity
    linarith
  refine ⟨?_, ?_, ?_⟩
  · unfold labelMaxProb
    have hc : (Finset.univ.filter (fun ℓ : α → Fin k => ∀ b, w a < w b → ℓ b ≠ ℓ a)).card
        = (Finset.univ.filter P).card := by
      congr 1
    rw [hc, hcount]
    have hsub : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub hk]; simp
    push_cast
    rw [hsub]
    rw [div_eq_iff (by positivity)]
    have hN' : Fintype.card α = (j - 1) + 1 + (N - j) := by omega
    rw [hN']
    generalize N - j = d
    have : (1 - 1 / (k : ℝ)) = ((k : ℝ) - 1) / k := by field_simp
    rw [this, div_pow, pow_add, pow_add, pow_one]
    have : (k : ℝ) ^ (j - 1) ≠ 0 := by positivity
    field_simp
  · exact pow_le_pow_of_le_one hbase0 hbase1 (by omega)
  · rcases Nat.lt_or_ge k 2 with h2 | h2
    · have : k = 1 := by omega
      subst this; simp
      exact inv_le_one_of_one_le₀ (by
        have := Real.add_one_le_exp (1:ℝ); linarith)
    · have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast h2
      have hpos : 0 < 1 - 1 / (k : ℝ) := by
        rw [sub_pos, div_lt_one (by linarith)]; linarith
      have hkm : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      have hk1 : (k : ℝ) - 1 ≠ 0 := by linarith
      have hinv : (1 - 1 / (k : ℝ))⁻¹ = 1 + 1 / ((k : ℝ) - 1) := by
        have : 1 - 1 / (k : ℝ) = ((k : ℝ) - 1) / k := by field_simp
        rw [this, inv_div]
        field_simp
        ring
      have hle : (1 + 1 / ((k : ℝ) - 1)) ^ (k - 1) ≤ Real.exp 1 := by
        calc (1 + 1 / ((k : ℝ) - 1)) ^ (k - 1)
            ≤ (Real.exp (1 / ((k : ℝ) - 1))) ^ (k - 1) := by
              apply pow_le_pow_left₀ (by
                have : 0 < (k : ℝ) - 1 := by linarith
                positivity)
              have := Real.add_one_le_exp (1 / ((k : ℝ) - 1)); linarith
          _ = Real.exp 1 := by
              rw [← Real.exp_nat_mul, hkm]
              congr 1; field_simp
      have hqpos : 0 < (1 - 1 / (k : ℝ)) ^ (k - 1) := by positivity
      rw [div_le_iff₀ (Real.exp_pos 1)]
      have : ((1 - 1 / (k : ℝ)) ^ (k - 1))⁻¹ ≤ Real.exp 1 := by
        rw [← inv_pow, hinv]; exact hle
      have := mul_le_mul_of_nonneg_left this hqpos.le
      rw [mul_inv_cancel₀ hqpos.ne'] at this
      linarith
