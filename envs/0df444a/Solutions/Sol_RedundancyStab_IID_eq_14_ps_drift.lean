-- Prove2me | solution 1 for RedundancyStab.IID.eq_14_ps_drift
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T09:11:20.167649+00:00
-- url     : https://prove2.me/submissions/8c29787f-d4b4-407c-bacd-b9537363c155

import Mathlib
import Definitions.Def_RedundancyStab_IID_Model

open RedundancyStab.IID

namespace RSEq14Aux

lemma typesAt_card (K d : ℕ) (hd : 1 ≤ d) (hdK : d ≤ K) (lam : ℝ) (s : Fin K) :
    ((typesAt K d s).card : ℝ) * lam / (K.choose d : ℝ) = lam * d / K := by
  classical
  have hcard : (typesAt K d s).card = (K - 1).choose (d - 1) := by
    have : (typesAt K d s).card =
        ((Finset.univ.erase s).powersetCard (d - 1)).card := by
      refine Finset.card_bij (fun c _ => c.1.erase s) ?_ ?_ ?_
      · intro c hc
        simp only [typesAt, Finset.mem_filter, Finset.mem_univ, true_and] at hc
        rw [Finset.mem_powersetCard]
        refine ⟨Finset.erase_subset_erase _ (Finset.subset_univ _), ?_⟩
        rw [Finset.card_erase_of_mem hc, c.2]
      · intro c₁ hc₁ c₂ hc₂ h
        simp only [typesAt, Finset.mem_filter, Finset.mem_univ, true_and] at hc₁ hc₂
        apply Subtype.ext
        have := congrArg (insert s) h
        simpa [Finset.insert_erase hc₁, Finset.insert_erase hc₂] using this
      · intro B hB
        rw [Finset.mem_powersetCard] at hB
        have hsB : s ∉ B := fun h => by simpa using hB.1 h
        refine ⟨⟨insert s B, ?_⟩, ?_, ?_⟩
        · rw [Finset.card_insert_of_notMem hsB, hB.2]; omega
        · simp [typesAt]
        · simp [Finset.erase_insert hsB]
    rw [this, Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
  rw [hcard]
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, d = j + 1 := ⟨d - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at *
  have key := Nat.add_one_mul_choose_eq k j
  have key' : ((k + 1 : ℕ) : ℝ) * (k.choose j : ℝ) =
      ((k + 1).choose (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ) := by
    exact_mod_cast key
  have hpos : (0 : ℝ) < ((k + 1).choose (j + 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hK : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  rw [div_eq_div_iff hpos.ne' hK.ne']
  push_cast at key' ⊢
  linear_combination lam * key'

lemma copies_update (K d : ℕ) (n : PSState K d) (c : JobType K d) (v : ℕ) (s : Fin K) :
    (copies K d (Function.update n c v) s : ℝ) =
      (copies K d n s : ℝ) + if s ∈ c.1 then ((v : ℝ) - (n c : ℝ)) else 0 := by
  classical
  unfold copies
  by_cases hs : s ∈ c.1
  · have hc : c ∈ typesAt K d s := by simp [typesAt, hs]
    rw [Finset.sum_update_of_mem hc, if_pos hs]
    rw [Finset.sdiff_singleton_eq_erase, ← Finset.add_sum_erase _ _ hc]
    push_cast
    ring
  · have hc : c ∉ typesAt K d s := by simp [typesAt, hs]
    rw [if_neg hs, add_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro c' hc'
    rw [Function.update_of_ne]
    rintro rfl; exact hc hc'

end RSEq14Aux

open RSEq14Aux in
theorem solution (K d : ℕ) (hd : 1 ≤ d) (hdK : d ≤ K) (lam μ : ℝ) (hlam : 0 < lam)
    (hμ : 0 < μ) (n : PSState K d) (s : Fin K) :
    ∑' y : PSState K d, psRate K d lam μ n * (psJump K d lam μ n y).toReal *
        ((copies K d y s : ℝ) - (copies K d n s : ℝ)) =
      lam * d / K - μ * ∑ c ∈ typesAt K d s, ∑ l ∈ c.1, (n c : ℝ) / (copies K d n l : ℝ) := by
  classical
  set r := psEventRate K d lam μ n with hr
  set R := psRate K d lam μ n with hR
  have hchoose : (0 : ℝ) < (K.choose d : ℝ) := by exact_mod_cast Nat.choose_pos hdK
  have hr0 : ∀ e, 0 ≤ r e := by
    intro e
    rcases e with c | c
    · exact (div_pos hlam hchoose).le
    · simp only [hr, psEventRate]
      exact mul_nonneg hμ.le (Finset.sum_nonneg fun _ _ => div_nonneg (by positivity) (by positivity))
  -- there is at least one type
  have hne : Nonempty (JobType K d) := by
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin K)))
      (n := d) (by simpa using hdK)
    exact ⟨⟨t, ht⟩⟩
  have hRpos : 0 < ∑ e, r e := by
    obtain ⟨c⟩ := hne
    have : r (Sum.inl c) ≤ ∑ e, r e :=
      Finset.single_le_sum (fun e _ => hr0 e) (Finset.mem_univ _)
    exact lt_of_lt_of_le (div_pos hlam hchoose) this
  have hRdef : R = ∑ e, r e := rfl
  have hjump : ∀ y, (psJump K d lam μ n y).toReal =
      ∑ e, if y = psApply K d n e then r e / R else 0 := by
    intro y
    unfold psJump clockStep
    rw [dif_pos ⟨hr0, hRpos⟩, PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro e _
      rw [PMF.ofFintype_apply, PMF.pure_apply]
      split_ifs
      · rw [mul_one, ENNReal.toReal_ofReal (div_nonneg (hr0 e) hRpos.le), hRdef]
      · simp
    · intro e _
      rw [PMF.ofFintype_apply, PMF.pure_apply]
      split_ifs <;> simp
  set g : PSState K d → ℝ := fun y => (copies K d y s : ℝ) - (copies K d n s : ℝ) with hg
  have hLHS : ∑' y : PSState K d, R * (psJump K d lam μ n y).toReal * g y =
      ∑ e, r e * g (psApply K d n e) := by
    have : ∀ y, R * (psJump K d lam μ n y).toReal * g y =
        ∑ e, if y = psApply K d n e then r e * g (psApply K d n e) else 0 := by
      intro y
      rw [hjump, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      split_ifs with h
      · subst h
        have hRne : R ≠ 0 := by rw [hRdef]; exact hRpos.ne'
        field_simp
      · simp
    simp_rw [this]
    rw [Summable.tsum_finsetSum]
    · apply Finset.sum_congr rfl
      intro e _
      exact tsum_ite_eq _ _
    · intro e _
      exact (hasSum_ite_eq _ _).summable
  show ∑' y : PSState K d, R * (psJump K d lam μ n y).toReal * g y = _
  rw [hLHS, Fintype.sum_sum_type]
  -- arrivals
  have harr : ∑ c, r (Sum.inl c) * g (psApply K d n (Sum.inl c)) = lam * d / K := by
    have : ∀ c, r (Sum.inl c) * g (psApply K d n (Sum.inl c)) =
        if c ∈ typesAt K d s then lam / (K.choose d : ℝ) else 0 := by
      intro c
      simp only [hr, hg, psEventRate, psApply, copies_update]
      by_cases hs : s ∈ c.1
      · have : c ∈ typesAt K d s := by simp [typesAt, hs]
        rw [if_pos hs, if_pos this]; push_cast; ring
      · have : c ∉ typesAt K d s := by simp [typesAt, hs]
        rw [if_neg hs, if_neg this]; ring
    simp_rw [this]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const,
      nsmul_eq_mul, ← typesAt_card K d hd hdK lam s]
    ring
  have hdep : ∑ c, r (Sum.inr c) * g (psApply K d n (Sum.inr c)) =
      -(μ * ∑ c ∈ typesAt K d s, ∑ l ∈ c.1, (n c : ℝ) / (copies K d n l : ℝ)) := by
    have : ∀ c, r (Sum.inr c) * g (psApply K d n (Sum.inr c)) =
        if c ∈ typesAt K d s then -(μ * ∑ l ∈ c.1, (n c : ℝ) / (copies K d n l : ℝ)) else 0 := by
      intro c
      simp only [hr, hg, psEventRate, psApply, copies_update]
      by_cases hs : s ∈ c.1
      · have : c ∈ typesAt K d s := by simp [typesAt, hs]
        rw [if_pos hs, if_pos this]
        rcases Nat.eq_zero_or_pos (n c) with h0 | hpos
        · simp [h0]
        · rw [Nat.cast_sub hpos]; push_cast; ring
      · have : c ∉ typesAt K d s := by simp [typesAt, hs]
        rw [if_neg hs, if_neg this]; ring
    simp_rw [this]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.mul_sum,
      ← Finset.sum_neg_distrib]
  rw [harr, hdep]
  ring
