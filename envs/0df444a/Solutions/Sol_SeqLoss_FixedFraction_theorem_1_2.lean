-- Prove2me | solution 2 for SeqLoss.FixedFraction.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T08:26:44.230706+00:00
-- url     : https://prove2.me/submissions/cc41c4bc-f28b-43f7-a016-b0f8d6e3cc58

import Mathlib
import Definitions.Def_SeqLoss_FixedFraction_Setting
import Definitions.Def_SeqLoss_FixedFraction_Axioms
import Theorems.Thm_SeqLoss_FixedFraction_lemma_1
import Theorems.Thm_SeqLoss_FixedFraction_proposition_2

-- carved verbatim out of submission 31af32e2-4782-4d53-b891-987489887aa4, lines 440-497

section
set_option autoImplicit false
open SeqLoss.FixedFraction

theorem slf_notliable (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ))
    (hφ : IsRule φ) (hzt : ZeroTruncation φ) (n : ℕ) (ℓ : Fin n → ℝ) (hℓ : IsLoss ℓ)
    (h i : Fin n) (hhi : h < i) (hsingle : ∀ j, j ≠ h → ℓ j = 0) :
    φ n ℓ i = 0 := by
  obtain ⟨hnn, hpre, htot⟩ := (hφ n ℓ hℓ).1
  have hlt : h.val + 1 < n := by
    have := hhi; rw [Fin.lt_def] at this; have := i.isLt; omega
  have hp := hpre h.val hlt
  have hL : ∑ j, ℓ j = ℓ h := by
    rw [Finset.sum_eq_single h]
    · intro j _ hj; exact hsingle j hj
    · intro hh; exact absurd (Finset.mem_univ h) hh
  have hpre' : ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val ≤ h.val), ℓ j = ℓ h := by
    rw [Finset.sum_eq_single h]
    · intro j _ hj; exact hsingle j hj
    · intro hh; exact absurd (by simp) hh
  rw [hpre'] at hp
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin n => j.val ≤ h.val)] at htot
  rw [hL] at htot
  have hrest : ∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬ j.val ≤ h.val), φ n ℓ j ≤ 0 := by linarith
  have hi' : i ∈ Finset.univ.filter (fun j : Fin n => ¬ j.val ≤ h.val) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
    exact hhi
  have := Finset.single_le_sum (f := φ n ℓ) (fun j _ => hnn j) hi'
  linarith [hnn i]

theorem slf_isLoss_elem (n : ℕ) : IsLoss (elem n) := by
  intro i; unfold elem; split_ifs <;> norm_num

theorem slf_sum_elem (n : ℕ) (hn : 1 ≤ n) : ∑ i, elem n i = 1 := by
  rw [Finset.sum_eq_single ⟨n - 1, by omega⟩]
  · simp [elem]; omega
  · intro j _ hj
    have : j.val ≠ n - 1 := fun h => hj (Fin.ext h)
    unfold elem
    rw [if_neg (by omega)]
  · intro h; exact absurd (Finset.mem_univ _) h

noncomputable def slfUnit (n j : ℕ) : Fin n → ℝ := fun x => if x.val = j then 1 else 0

lemma slf_unit_loss (n j : ℕ) : IsLoss (slfUnit n j) := by
  intro x; unfold slfUnit; split_ifs <;> norm_num

lemma slf_add_loss {n : ℕ} {ℓ ℓ' : Fin n → ℝ} (h : IsLoss ℓ) (h' : IsLoss ℓ') : IsLoss (ℓ + ℓ') :=
  fun i => add_nonneg (h i) (h' i)

lemma slf_snoc_loss {n : ℕ} {ℓ : Fin n → ℝ} (h : IsLoss ℓ) :
    IsLoss (Fin.snoc ℓ 0 : Fin (n + 1) → ℝ) := by
  intro x
  refine Fin.lastCases ?_ (fun y => ?_) x
  · simp
  · simp [Fin.snoc_castSucc]; exact h y

lemma slf_unit_zt (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hzt : ZeroTruncation φ) (j : ℕ) :
    ∀ n (hn : j + 1 ≤ n) (i : Fin n) (hi : i.val ≤ j),
      φ n (slfUnit n j) i = φ (j + 1) (elem (j + 1)) ⟨i.val, by omega⟩ := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro i hi
    have : slfUnit (j + 1) j = elem (j + 1) := by
      funext x; simp [slfUnit, elem]
    rw [this]
  | succ n hn ih =>
    intro i hi
    have hlt : i.val < n := by omega
    have hu : slfUnit (n + 1) j = (Fin.snoc (slfUnit n j) 0 : Fin (n + 1) → ℝ) := by
      funext x
      refine Fin.lastCases ?_ (fun y => ?_) x
      · simp [slfUnit]; omega
      · simp [slfUnit, Fin.snoc_castSucc]
    show φ (n + 1) (slfUnit (n + 1) j) (⟨i.val, hlt⟩ : Fin n).castSucc = _
    rw [hu, hzt n (slfUnit n j) (slf_unit_loss n j) ⟨i.val, hlt⟩]
    exact ih ⟨i.val, hlt⟩ hi

lemma slf_sum_additive (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hadd : Additive φ) (n : ℕ)
    {ι : Type} (s : Finset ι) (f : ι → (Fin n → ℝ)) (hf : ∀ k ∈ s, IsLoss (f k)) :
    φ n (∑ k ∈ s, f k) = ∑ k ∈ s, φ n (f k) := by
  classical
  have h0 : φ n 0 = 0 := by
    have := hadd n 0 0 (fun i => le_rfl) (fun i => le_rfl)
    simpa using this
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hs : IsLoss (∑ k ∈ s, f k) := by
      intro i
      rw [Finset.sum_apply]
      exact Finset.sum_nonneg (fun k hk => hf k (Finset.mem_insert_of_mem hk) i)
    rw [hadd n _ _ (hf a (Finset.mem_insert_self a s)) hs, ih (fun k hk => hf k (Finset.mem_insert_of_mem hk))]

lemma slf_forward (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hφ : IsRule φ) (hadd : Additive φ)
    (hzt : ZeroTruncation φ) (n : ℕ) (ℓ : Fin n → ℝ) (hℓ : IsLoss ℓ) (i : Fin n) :
    φ n ℓ i = ∑ j : Fin n,
        if h : i ≤ j then ℓ j * φ (j.val + 1) (elem (j.val + 1)) ⟨i.val, Nat.lt_succ_of_le h⟩
        else 0 := by
  have hdec : ∑ j : Fin n, ℓ j • slfUnit n j.val = ℓ := by
    funext x
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single x]
    · simp [slfUnit]
    · intro j _ hj
      have : x.val ≠ j.val := fun h => hj (Fin.ext h.symm)
      simp [slfUnit, this]
    · intro h; exact absurd (Finset.mem_univ x) h
  have hstep : φ n ℓ i = ∑ j : Fin n, ℓ j * φ n (slfUnit n j.val) i := by
    conv_lhs => rw [← hdec]
    rw [slf_sum_additive φ hadd n Finset.univ _ (fun k _ => by
      intro x; simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (hℓ k) (slf_unit_loss n _ x))]
    rw [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [SeqLoss.FixedFraction.lemma_1 φ hφ hadd n _ (slf_unit_loss n _) (ℓ j) (hℓ j)]
    simp
  rw [hstep]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i ≤ j
  · rw [dif_pos hij]
    congr 1
    exact slf_unit_zt φ hzt j.val n (by omega) i (Fin.le_def.mp hij)
  · rw [dif_neg hij]
    have : φ n (slfUnit n j.val) i = 0 := by
      apply slf_notliable φ hφ hzt n _ (slf_unit_loss n _) j i (not_le.1 hij)
      intro k hk
      have : k.val ≠ j.val := fun h => hk (Fin.ext h)
      simp [slfUnit, this]
    rw [this]; simp

lemma slf_ff_val (lam : ℝ) (n : ℕ) (ℓ : Fin n → ℝ) (i : Fin n) :
    fixedFraction lam n ℓ i = lam * ℓ i + if i.val = 0 then (1 - lam) * ∑ j, ℓ j else 0 := rfl

theorem solution (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hφ : IsRule φ) :
    (Additive φ ∧ ZeroTruncation φ ∧ MergingProof φ ∧ PopulationMonotone φ) ↔
    ∃ lam ∈ Set.Icc (0:ℝ) 1,
      ∀ n (ℓ : Fin n → ℝ), IsLoss ℓ → φ n ℓ = fixedFraction lam n ℓ := by
  constructor
  · rintro ⟨hadd, hzt, hmp, hpm⟩
    obtain ⟨lam, hlam, hel⟩ := (SeqLoss.FixedFraction.proposition_2 φ hφ).1 ⟨hpm, hmp⟩
    refine ⟨lam, hlam, fun n ℓ hℓ => ?_⟩
    funext i
    rw [slf_forward φ hφ hadd hzt n ℓ hℓ i, slf_ff_val]
    have hterm : ∀ j : Fin n,
        (if h : i ≤ j then ℓ j * φ (j.val + 1) (elem (j.val + 1)) ⟨i.val, Nat.lt_succ_of_le h⟩
          else 0) =
        lam * (if j = i then ℓ j else 0) + (if i.val = 0 then (1 - lam) * ℓ j else 0) := by
      intro j
      by_cases hij : i ≤ j
      · rw [dif_pos hij]
        have h1 := congrFun (hel (j.val + 1)) ⟨i.val, Nat.lt_succ_of_le hij⟩
        rw [h1, slf_ff_val, slf_sum_elem (j.val + 1) (by omega)]
        have hij' : i.val ≤ j.val := Fin.le_def.mp hij
        by_cases hji : j = i
        · subst hji
          by_cases h0 : j.val = 0
          · simp [elem, h0]; ring
          · simp [elem, h0]; ring
        · have hne : i.val + 1 ≠ j.val + 1 := fun h => hji (Fin.ext (by omega)).symm
          have : i.val ≠ j.val := fun h => hji (Fin.ext h.symm)
          by_cases h0 : i.val = 0
          · have hj0 : j.val ≠ 0 := fun h => this (by omega)
            simp [elem, h0, hji, this, hj0]; ring
          · simp [elem, h0, hji, this]
      · rw [dif_neg hij]
        have hji : j ≠ i := fun h => hij (h ▸ le_rfl)
        have h0 : i.val ≠ 0 := by
          have := not_le.1 hij
          rw [Fin.lt_def] at this
          omega
        simp [hji, h0]
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ i)]
    by_cases h0 : i.val = 0
    · simp [h0, ← Finset.mul_sum]
    · simp [h0]
  · rintro ⟨lam, hlam, hform⟩
    have hadd : Additive φ := by
      intro n ℓ ℓ' h h'
      rw [hform n _ (slf_add_loss h h'), hform n ℓ h, hform n ℓ' h']
      funext i
      simp only [fixedFraction, Pi.add_apply, Finset.sum_add_distrib]
      split_ifs <;> ring
    have hzt : ZeroTruncation φ := by
      intro n ℓ hℓ i
      rw [hform (n + 1) _ (slf_snoc_loss hℓ), hform n ℓ hℓ]
      simp only [fixedFraction, Fin.coe_castSucc, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
        Fin.snoc_last, add_zero]
    obtain ⟨hpm, hmp⟩ := (SeqLoss.FixedFraction.proposition_2 φ hφ).2 ⟨lam, hlam, fun n => hform n (elem n) (slf_isLoss_elem n)⟩
    exact ⟨hadd, hzt, hmp, hpm⟩

end
