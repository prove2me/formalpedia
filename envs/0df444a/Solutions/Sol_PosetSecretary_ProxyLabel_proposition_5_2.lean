-- Prove2me | solution 1 for PosetSecretary.ProxyLabel.proposition_5_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T16:17:49.640759+00:00
-- url     : https://prove2.me/submissions/1a44ef4b-a866-4d7f-97fd-f12dd919bd7d

import Mathlib
import Definitions.Def_AppliedComb_Posets_width
import Definitions.Def_PosetSecretary_ProxyLabel_Setting
import Theorems.Thm_PosetSecretary_ProxyLabel_selection_prob_top_k
import Theorems.Thm_PosetSecretary_ProxyLabel_value_ge_sum_top_k

open PosetSecretary.ProxyLabel

theorem solution {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]
    (w : α → ℝ) (hw : IsConsistentScoring w) (k : ℕ) (hk : 1 ≤ k) (ω' : ℕ) (c : ℝ)
    (hc : 1 ≤ c) (hω' : (AppliedComb.Posets.width α : ℝ) / c ≤ ω') :
    opt w k / (Real.exp c * (ω' + 1) / (1 - 1 / (k : ℝ)) ^ (k - 1)) ≤ proxyLabelValue w k ω' ∧
      Real.exp c * (ω' + 1) / (1 - 1 / (k : ℝ)) ^ (k - 1) ≤ Real.exp (c + 1) * (ω' + 1) := by
  classical
  obtain ⟨hw0, hinj, hmono⟩ := hw
  set q : ℝ := (1 - 1 / (k : ℝ)) ^ (k - 1) with hq
  set D : ℝ := Real.exp c * (ω' + 1) with hD
  have hDpos : 0 < D := by positivity
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  -- (1 - 1/k)^(k-1) ≥ 1/e
  have hqe : 1 / Real.exp 1 ≤ q := by
    rcases Nat.lt_or_ge k 2 with h2 | h2
    · have : k = 1 := by omega
      subst this; simp [hq]
      exact inv_le_one_of_one_le₀ (by
        have := Real.add_one_le_exp (1:ℝ); linarith)
    · have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast h2
      have hpos : 0 < 1 - 1 / (k : ℝ) := by
        rw [sub_pos, div_lt_one (by linarith)]; linarith
      -- (1 + 1/(k-1))^(k-1) ≤ e
      have hkm : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      have hk0 : (k : ℝ) ≠ 0 := by linarith
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
      have hqpos : 0 < q := by rw [hq]; positivity
      rw [div_le_iff₀ (Real.exp_pos 1)]
      have : q⁻¹ ≤ Real.exp 1 := by
        rw [hq, ← inv_pow, hinv]; exact hle
      have := mul_le_mul_of_nonneg_left this hqpos.le
      rw [mul_inv_cancel₀ hqpos.ne'] at this
      linarith
  have hqpos : 0 < q := lt_of_lt_of_le (by positivity) hqe
  refine ⟨?_, ?_⟩
  · -- top-k set
    set T : Finset α := Finset.univ.filter
      (fun a => (Finset.univ.filter (fun b => w a < w b)).card < k) with hT
    -- every element of T beats every element outside T
    have hbeat : ∀ b ∈ T, ∀ x, x ∉ T → w x < w b := by
      intro b hb x hx
      simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hb hx
      rcases lt_trichotomy (w x) (w b) with h | h | h
      · exact h
      · exact absurd (hinj h ▸ hb) (by omega)
      · exfalso
        have hsub : insert x (Finset.univ.filter (fun c => w x < w c)) ⊆
            Finset.univ.filter (fun c => w b < w c) := by
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
          rcases hy with rfl | hy
          · exact h
          · linarith
        have := Finset.card_le_card hsub
        rw [Finset.card_insert_of_notMem (by simp)] at this
        omega
    -- if T ≠ univ then |T| ≥ k
    have hTcard : ∀ x, x ∉ T → k ≤ T.card := by
      intro x hx
      have hne : (Finset.univ.filter (fun y => y ∉ T)).Nonempty := ⟨x, by simp [hx]⟩
      obtain ⟨y, hy, hymax⟩ := Finset.exists_max_image _ w hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      have hsub : Finset.univ.filter (fun c => w y < w c) ⊆ T := by
        intro z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
        by_contra hzT
        have := hymax z (by simp [hzT])
        linarith
      have := Finset.card_le_card hsub
      have hy' := hy
      simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hy'
      omega
    have hopt : opt w k ≤ ∑ a ∈ T, w a := by
      unfold opt
      apply Finset.sup'_le
      intro s hs
      simp only [Finset.mem_filter, Finset.mem_powerset] at hs
      obtain ⟨-, hsk⟩ := hs
      have h1 := Finset.sum_sdiff (f := w) (Finset.inter_subset_left : s ∩ T ⊆ s)
      have h2 := Finset.sum_sdiff (f := w) (Finset.inter_subset_right : s ∩ T ⊆ T)
      have e1 : s \ (s ∩ T) = s \ T := by ext; simp
      have e2 : T \ (s ∩ T) = T \ s := by ext; simp
      rw [e1] at h1; rw [e2] at h2
      suffices ∑ x ∈ s \ T, w x ≤ ∑ x ∈ T \ s, w x by linarith
      rcases (s \ T).eq_empty_or_nonempty with he | hne
      · rw [he, Finset.sum_empty]
        exact Finset.sum_nonneg (fun i _ => hw0 i)
      · set m := (s \ T).sup' hne w
        obtain ⟨x0, hx0⟩ := hne
        have hx0T : x0 ∉ T := (Finset.mem_sdiff.1 hx0).2
        have hcardT := hTcard x0 hx0T
        have hc1 : (s \ T).card ≤ (T \ s).card := by
          have a1 := Finset.card_sdiff_add_card_inter s T
          have a2 := Finset.card_sdiff_add_card_inter T s
          rw [Finset.inter_comm] at a2
          omega
        have hb1 : ∑ x ∈ s \ T, w x ≤ (s \ T).card • m :=
          Finset.sum_le_card_nsmul _ _ _ (fun x hx => Finset.le_sup' w hx)
        have hb2 : (T \ s).card • m ≤ ∑ x ∈ T \ s, w x := by
          apply Finset.card_nsmul_le_sum
          intro b hb
          obtain ⟨y, hy, hym⟩ := Finset.exists_mem_eq_sup' ⟨x0, hx0⟩ w
          have : m = w y := hym
          rw [this]
          exact (hbeat b (Finset.mem_sdiff.1 hb).1 y (Finset.mem_sdiff.1 hy).2).le
        have hm0 : 0 ≤ m := le_trans (hw0 x0) (Finset.le_sup' w hx0)
        have : (s \ T).card • m ≤ (T \ s).card • m := by
          simp only [nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc1) hm0
        linarith
    have hsel : ∀ a ∈ T, q * (1 / D) ≤ selectionProb k ω' a := by
      intro a ha
      simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      exact selection_prob_top_k w ⟨hw0, hinj, hmono⟩ k hk ω' c hc hω' a ha
    calc opt w k / (D / q) = q * (1 / D) * opt w k := by field_simp
      _ ≤ q * (1 / D) * ∑ a ∈ T, w a := mul_le_mul_of_nonneg_left hopt (by positivity)
      _ = ∑ a ∈ T, q * (1 / D) * w a := Finset.mul_sum _ _ _
      _ ≤ ∑ a ∈ T, selectionProb k ω' a * w a :=
          Finset.sum_le_sum (fun a ha => mul_le_mul_of_nonneg_right (hsel a ha) (hw0 a))
      _ ≤ proxyLabelValue w k ω' := value_ge_sum_top_k w hw0 k ω'
  · rw [div_le_iff₀ hqpos, Real.exp_add]
    have heq : 1 ≤ Real.exp 1 * q := by
      rw [div_le_iff₀ (Real.exp_pos 1)] at hqe; linarith
    have : D * 1 ≤ D * (Real.exp 1 * q) := mul_le_mul_of_nonneg_left heq hDpos.le
    rw [hD] at this
    nlinarith
