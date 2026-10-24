-- Prove2me | solution 1 for StrictCompatLB.MeanField.proposition_4_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T14:33:42.870582+00:00
-- url     : https://prove2.me/submissions/a1319efb-5167-4a0e-a4f4-dbe47bef775e

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Coupling

open Filter Topology MeasureTheory Finset
open scoped ENNReal

namespace StrictCompatLB.MeanField.P47

open StrictCompatLB.MeanField

lemma Qcount_arrive {N : ℕ} (z : Fin N → ℕ) (v : Fin N) (i : ℕ) :
    Qcount (arrive z v) i = Qcount z i + if i = z v + 1 then 1 else 0 := by
  unfold Qcount arrive
  rw [card_filter, card_filter, ← Finset.add_sum_erase _ _ (mem_univ v),
    ← Finset.add_sum_erase _ _ (mem_univ v)]
  have hs : ∑ x ∈ univ.erase v, (if i ≤ Function.update z v (z v + 1) x then 1 else 0)
      = ∑ x ∈ univ.erase v, (if i ≤ z x then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  rw [hs, Function.update_self]
  split_ifs <;> omega

lemma Qcount_depart {N : ℕ} (z : Fin N → ℕ) (v : Fin N) (i : ℕ) (hi : 1 ≤ i) :
    Qcount (depart z v) i + (if i = z v then 1 else 0) = Qcount z i := by
  unfold Qcount depart
  rw [card_filter, card_filter, ← Finset.add_sum_erase _ _ (mem_univ v),
    ← Finset.add_sum_erase _ _ (mem_univ v)]
  have hs : ∑ x ∈ univ.erase v, (if i ≤ Function.update z v (z v - 1) x then 1 else 0)
      = ∑ x ∈ univ.erase v, (if i ≤ z x then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  rw [hs, Function.update_self]
  split_ifs <;> omega

lemma Qcount_eq_zero {N : ℕ} (z : Fin N → ℕ) (i : ℕ) (hi : maxLen z < i) : Qcount z i = 0 := by
  unfold Qcount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro u _ h
  have : z u ≤ maxLen z := Finset.le_sup (f := z) (mem_univ u)
  omega

lemma occDiffSum_eq {N : ℕ} (z y : Fin N → ℕ) (B : ℕ) (hz : maxLen z < B) (hy : maxLen y < B) :
    occDiffSum z y = ∑ i ∈ Ico 1 B, |(Qcount y i : ℝ) - (Qcount z i : ℝ)| := by
  unfold occDiffSum
  apply Finset.sum_subset
  · intro i hi
    simp only [mem_Ico] at hi ⊢
    have := max_lt hz hy
    omega
  · intro i hi hni
    simp only [mem_Ico] at hi hni
    have hz' : Qcount z i = 0 := Qcount_eq_zero z i (by omega)
    have hy' : Qcount y i = 0 := Qcount_eq_zero y i (by omega)
    simp [hz', hy']

lemma maxLen_le_of {N : ℕ} (z z' : Fin N → ℕ) (h : ∀ u, z' u ≤ z u + 1) :
    maxLen z' ≤ maxLen z + 1 := by
  unfold maxLen
  apply Finset.sup_le
  intro u _
  have : z u ≤ univ.sup z := Finset.le_sup (f := z) (mem_univ u)
  have := h u
  omega

lemma arrive_le {N : ℕ} (z : Fin N → ℕ) (v u : Fin N) : arrive z v u ≤ z u + 1 := by
  unfold arrive
  by_cases h : u = v
  · subst h; simp
  · rw [Function.update_of_ne h]; omega

lemma depart_le {N : ℕ} (z : Fin N → ℕ) (v u : Fin N) : depart z v u ≤ z u + 1 := by
  unfold depart
  by_cases h : u = v
  · subst h; simp; omega
  · rw [Function.update_of_ne h]; omega

lemma sorted_count {N : ℕ} (z y : Fin N → ℕ) (σ₁ σ₂ : Fin N ≃ Fin N)
    (h1 : Monotone (z ∘ σ₁)) (h2 : Monotone (y ∘ σ₂)) (k : Fin N)
    (hlt : y (σ₂ k) < z (σ₁ k)) : Qcount y (z (σ₁ k)) < Qcount z (z (σ₁ k)) := by
  unfold Qcount
  have hA : ((Finset.Ici k).map σ₁.toEmbedding) ⊆ univ.filter (fun u => z (σ₁ k) ≤ z u) := by
    intro u hu
    simp only [Finset.mem_map, mem_Ici, Equiv.coe_toEmbedding] at hu
    obtain ⟨j, hj, rfl⟩ := hu
    simp only [mem_filter, mem_univ, true_and]
    exact h1 hj
  have hB : univ.filter (fun u => z (σ₁ k) ≤ y u) ⊆ ((Finset.Ioi k).map σ₂.toEmbedding) := by
    intro u hu
    simp only [mem_filter, mem_univ, true_and] at hu
    simp only [Finset.mem_map, mem_Ioi, Equiv.coe_toEmbedding]
    refine ⟨σ₂.symm u, ?_, by simp⟩
    by_contra hc
    push Not at hc
    have := h2 hc
    simp only [Function.comp, Equiv.apply_symm_apply] at this
    omega
  have c1 := Finset.card_le_card hA
  have c2 := Finset.card_le_card hB
  rw [Finset.card_map, Fin.card_Ici] at c1
  rw [Finset.card_map, Fin.card_Ioi] at c2
  have := k.isLt
  omega

/-- One coupled step increases `occDiffSum` by at most `2 mis`. -/
lemma step_bound (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)
    (p : (ℕ → ℝ) → ℕ → ℝ) (z y z' y' : Fin N → ℕ) (mis : ℕ)
    (h : CoupledStep M G N p z y z' y' mis) :
    occDiffSum z' y' ≤ occDiffSum z y + 2 * (mis : ℝ) := by
  set B := max (maxLen z) (maxLen y) + 2 with hB
  rcases h with ⟨σ₁, σ₂, h1, h2, k, rfl, rfl, rfl⟩ | ⟨w, u, _, I₁, I₂, _, _, v₁, v₂, _, hv₁, hv₂,
    rfl, rfl, rfl⟩
  · -- departure
    have hz' : maxLen (depart z (σ₁ k)) < B :=
      lt_of_le_of_lt (maxLen_le_of _ _ (depart_le z _)) (by omega)
    have hy' : maxLen (depart y (σ₂ k)) < B :=
      lt_of_le_of_lt (maxLen_le_of _ _ (depart_le y _)) (by omega)
    rw [occDiffSum_eq _ _ B hz' hy', occDiffSum_eq z y B (by omega) (by omega)]
    simp only [Nat.cast_zero, mul_zero, add_zero]
    set a := z (σ₁ k) with ha
    set b := y (σ₂ k) with hb
    have hzB : a < B := by
      have : a ≤ maxLen z := Finset.le_sup (f := z) (mem_univ _)
      omega
    have hyB : b < B := by
      have : b ≤ maxLen y := Finset.le_sup (f := y) (mem_univ _)
      omega
    -- termwise form
    have key : ∀ i ∈ Ico 1 B,
        |(Qcount (depart y (σ₂ k)) i : ℝ) - (Qcount (depart z (σ₁ k)) i : ℝ)| =
          |((Qcount y i : ℝ) - (if i = b then 1 else 0)) -
            ((Qcount z i : ℝ) - (if i = a then 1 else 0))| := by
      intro i hi
      simp only [mem_Ico] at hi
      have e1 := Qcount_depart y (σ₂ k) i hi.1
      have e2 := Qcount_depart z (σ₁ k) i hi.1
      rw [← hb] at e1
      rw [← ha] at e2
      congr 2
      · rw [← e1]; push_cast; ring
      · rw [← e2]; push_cast; ring
    rw [Finset.sum_congr rfl key]
    rcases lt_trichotomy a b with hab | hab | hab
    · -- a < b : the gain at level b
      have hcnt := sorted_count y z σ₂ σ₁ h2 h1 k hab
      rw [← hb] at hcnt
      have hb1 : 1 ≤ b := by omega
      have term : ∀ i ∈ Ico 1 B,
          |((Qcount y i : ℝ) - (if i = b then 1 else 0)) -
            ((Qcount z i : ℝ) - (if i = a then 1 else 0))| ≤
          |(Qcount y i : ℝ) - (Qcount z i : ℝ)| - (if i = b then 1 else 0) +
            (if i = a then 1 else 0) := by
        intro i _
        by_cases hib : i = b
        · have hia : i ≠ a := by omega
          subst hib
          simp only [if_true, if_neg hia, sub_zero, add_zero]
          have : (Qcount z (y (σ₂ k)) : ℝ) + 1 ≤ Qcount y (y (σ₂ k)) := by
            exact_mod_cast hcnt
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
          linarith
        · simp only [if_neg hib, sub_zero]
          split_ifs
          · have := abs_sub_abs_le_abs_sub ((Qcount y i : ℝ) - Qcount z i + 1)
              ((Qcount y i : ℝ) - Qcount z i)
            have h3 : |(Qcount y i : ℝ) - (Qcount z i - 1)| =
                |(Qcount y i : ℝ) - Qcount z i + 1| := by ring_nf
            rw [h3]
            have : |(Qcount y i : ℝ) - Qcount z i + 1| ≤ |(Qcount y i : ℝ) - Qcount z i| + |1| :=
              abs_add_le _ _
            simp at this
            linarith
          · simp
      calc _ ≤ ∑ i ∈ Ico 1 B, (|(Qcount y i : ℝ) - (Qcount z i : ℝ)| - (if i = b then 1 else 0) +
            (if i = a then 1 else 0)) := Finset.sum_le_sum term
        _ = _ - (if b ∈ Ico 1 B then 1 else 0) + (if a ∈ Ico 1 B then 1 else 0) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq',
              Finset.sum_ite_eq']
        _ ≤ _ := by
            have : b ∈ Ico 1 B := by simp only [mem_Ico]; omega
            rw [if_pos this]
            split_ifs <;> linarith
    · -- a = b
      apply le_of_eq
      apply Finset.sum_congr rfl
      intro i _
      rw [hab]; congr 1; ring
    · -- b < a : the gain at level a
      have hcnt := sorted_count z y σ₁ σ₂ h1 h2 k hab
      rw [← ha] at hcnt
      have ha1 : 1 ≤ a := by omega
      have term : ∀ i ∈ Ico 1 B,
          |((Qcount y i : ℝ) - (if i = b then 1 else 0)) -
            ((Qcount z i : ℝ) - (if i = a then 1 else 0))| ≤
          |(Qcount y i : ℝ) - (Qcount z i : ℝ)| - (if i = a then 1 else 0) +
            (if i = b then 1 else 0) := by
        intro i _
        by_cases hia : i = a
        · have hib : i ≠ b := by omega
          subst hia
          simp only [if_true, if_neg hib, sub_zero, add_zero]
          have : (Qcount y (z (σ₁ k)) : ℝ) + 1 ≤ Qcount z (z (σ₁ k)) := by
            exact_mod_cast hcnt
          rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
          linarith
        · simp only [if_neg hia, sub_zero]
          split_ifs
          · have : |(Qcount y i : ℝ) - 1 - Qcount z i| ≤ |(Qcount y i : ℝ) - Qcount z i| + |(-1 : ℝ)| := by
              have h3 : (Qcount y i : ℝ) - 1 - Qcount z i = ((Qcount y i : ℝ) - Qcount z i) + (-1) := by ring
              rw [h3]; exact abs_add_le _ _
            simp at this
            linarith
          · simp
      calc _ ≤ ∑ i ∈ Ico 1 B, (|(Qcount y i : ℝ) - (Qcount z i : ℝ)| - (if i = a then 1 else 0) +
            (if i = b then 1 else 0)) := Finset.sum_le_sum term
        _ = _ - (if a ∈ Ico 1 B then 1 else 0) + (if b ∈ Ico 1 B then 1 else 0) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq',
              Finset.sum_ite_eq']
        _ ≤ _ := by
            have : a ∈ Ico 1 B := by simp only [mem_Ico]; omega
            rw [if_pos this]
            split_ifs <;> linarith
  · -- arrival
    have hz' : maxLen (arrive z v₁) < B :=
      lt_of_le_of_lt (maxLen_le_of _ _ (arrive_le z _)) (by omega)
    have hy' : maxLen (arrive y v₂) < B :=
      lt_of_le_of_lt (maxLen_le_of _ _ (arrive_le y _)) (by omega)
    rw [occDiffSum_eq _ _ B hz' hy', occDiffSum_eq z y B (by omega) (by omega)]
    have key : ∀ i ∈ Ico 1 B,
        |(Qcount (arrive y v₂) i : ℝ) - (Qcount (arrive z v₁) i : ℝ)| ≤
          |(Qcount y i : ℝ) - (Qcount z i : ℝ)| +
            (if I₁ = I₂ then 0 else ((if i = I₂ + 1 then 1 else 0) + (if i = I₁ + 1 then 1 else 0))) := by
      intro i _
      rw [Qcount_arrive, Qcount_arrive, hv₁, hv₂]
      push_cast
      set Y : ℝ := (Qcount y i : ℝ)
      set Z : ℝ := (Qcount z i : ℝ)
      by_cases h12 : I₁ = I₂
      · subst h12
        rw [if_pos rfl, add_zero]
        apply le_of_eq; congr 1; ring
      · rw [if_neg h12]
        set e2 : ℝ := (if i = I₂ + 1 then 1 else 0)
        set e1 : ℝ := (if i = I₁ + 1 then 1 else 0)
        have he1 : 0 ≤ e1 := by simp only [e1]; split_ifs <;> norm_num
        have he2 : 0 ≤ e2 := by simp only [e2]; split_ifs <;> norm_num
        calc |Y + e2 - (Z + e1)| = |(Y - Z + e2) + (-e1)| := by congr 1; ring
          _ ≤ |Y - Z + e2| + |-e1| := abs_add_le _ _
          _ ≤ |Y - Z| + |e2| + |-e1| := by gcongr; exact abs_add_le _ _
          _ = |Y - Z| + (e2 + e1) := by
            rw [abs_neg, abs_of_nonneg he1, abs_of_nonneg he2]; ring
    calc _ ≤ ∑ i ∈ Ico 1 B, (|(Qcount y i : ℝ) - (Qcount z i : ℝ)| +
            (if I₁ = I₂ then 0 else ((if i = I₂ + 1 then 1 else 0) + (if i = I₁ + 1 then 1 else 0)))) :=
          Finset.sum_le_sum key
      _ ≤ _ := by
          rw [Finset.sum_add_distrib]
          gcongr
          split_ifs with h12
          · simp
          · rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
            push_cast
            split_ifs <;> norm_num

end StrictCompatLB.MeanField.P47

open StrictCompatLB.MeanField in
theorem solution (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)
    (hN : 1 ≤ N) (p : (ℕ → ℝ) → ℕ → ℝ) (hp : IsAssignmentFn p) (hLip : IsLipschitzPolicy p)
    (zs ys : ℕ → Fin N → ℕ) (mis : ℕ → ℕ)
    (hstep : ∀ n, CoupledStep M G N p (zs n) (ys n) (zs (n + 1)) (ys (n + 1)) (mis n))
    (h0 : occDiffSum (zs 0) (ys 0) ≤ 2 * ((∑ j ∈ Finset.range 0, mis j : ℕ) : ℝ)) :
    ∀ n : ℕ, occDiffSum (zs n) (ys n) ≤ 2 * ((∑ j ∈ Finset.range n, mis j : ℕ) : ℝ) := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    have := StrictCompatLB.MeanField.P47.step_bound M G N p _ _ _ _ _ (hstep n)
    rw [Finset.sum_range_succ]
    push_cast at ih ⊢
    linarith
