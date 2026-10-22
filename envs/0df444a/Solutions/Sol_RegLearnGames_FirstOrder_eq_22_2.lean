-- Prove2me | solution 2 for RegLearnGames.FirstOrder.eq_22
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:14:36.399987+00:00
-- url     : https://prove2.me/submissions/a02af7c6-ec67-49e8-a522-6e01b638a1b5

import Mathlib
import Definitions.Def_RegLearnGames_FirstOrder_Setting
set_option autoImplicit false

open Finset RegLearnGames.FirstOrder


lemma oo_pp_update {n d : ℕ} (w : Fin n → Fin d → ℝ) (i : Fin n) (a : Fin d)
    (s : Fin n → Fin d) :
    AGT.profileProb (Function.update w i (Pi.single a 1)) s
      = (if s i = a then 1 else 0) * ∏ j ∈ univ.erase i, w j (s j) := by
  unfold AGT.profileProb
  rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ i)]
  congr 1
  · simp [Pi.single_apply]
  · apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma oo_pp {n d : ℕ} (w : Fin n → Fin d → ℝ) (i : Fin n) (s : Fin n → Fin d) :
    AGT.profileProb w s = w i (s i) * ∏ j ∈ univ.erase i, w j (s j) := by
  unfold AGT.profileProb
  rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ i)]


lemma oo_R_update {n d : ℕ} (w : Fin n → Fin d → ℝ) (i : Fin n) (a : Fin d)
    (s : Fin n → Fin d) :
    ∏ j ∈ univ.erase i, w j (Function.update s i a j) = ∏ j ∈ univ.erase i, w j (s j) := by
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma oo_costVec {n d : ℕ} (c : Fin n → (Fin n → Fin d) → ℝ)
    (w : Fin n → Fin d → ℝ) (i : Fin n) (hl : ∑ b, w i b = 1) (a : Fin d) :
    costVec c w i a = ∑ s, AGT.profileProb w s * c i (Function.update s i a) := by
  unfold costVec AGT.expectedPayoff
  simp only [oo_pp_update]
  have h1 : ∑ s : Fin n → Fin d, (if s i = a then 1 else 0) * (∏ j ∈ univ.erase i, w j (s j)) * c i s
      = ∑ s ∈ univ.filter (fun s : Fin n → Fin d => s i = a),
          (∏ j ∈ univ.erase i, w j (s j)) * c i s := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro s _
    by_cases h : s i = a <;> simp [h]
  rw [h1]
  rw [← Finset.sum_fiberwise univ (fun s : Fin n → Fin d => s i)
    (fun s => AGT.profileProb w s * c i (Function.update s i a))]
  have h2 : ∀ b : Fin d, ∑ s ∈ univ.filter (fun s : Fin n → Fin d => s i = b),
      AGT.profileProb w s * c i (Function.update s i a)
      = w i b * ∑ s ∈ univ.filter (fun s : Fin n → Fin d => s i = a),
          (∏ j ∈ univ.erase i, w j (s j)) * c i s := by
    intro b
    rw [Finset.mul_sum]
    refine Finset.sum_nbij' (fun s => Function.update s i a) (fun s => Function.update s i b)
      ?_ ?_ ?_ ?_ ?_
    · intro s hs; simp
    · intro s hs; simp
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      simp [hs]
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      simp [hs]
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      rw [oo_pp w i s, hs, oo_R_update]
      ring
  rw [Finset.sum_congr rfl (fun b _ => h2 b), ← Finset.sum_mul, hl, one_mul]

lemma oo_one {n d : ℕ} (c : Fin n → (Fin n → Fin d) → ℝ)
    (w : Fin n → Fin d → ℝ) :
    socialCost c w = ∑ i, (w i) ⬝ᵥ (costVec c w i) := by
  unfold socialCost socialCostPure
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  unfold costVec AGT.expectedPayoff dotProduct
  simp only [oo_pp_update, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [oo_pp w i s]
  have : ∀ a : Fin d, w i a * (((if s i = a then 1 else 0) * ∏ j ∈ univ.erase i, w j (s j)) * c i s)
      = if s i = a then w i (s i) * (∏ j ∈ univ.erase i, w j (s j)) * c i s else 0 := by
    intro a
    by_cases h : s i = a
    · subst h; simp; ring
    · simp [h]
  rw [Finset.sum_congr rfl (fun a _ => this a), Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]


lemma oo_costVec_nonneg {n d : ℕ} (c : Fin n → (Fin n → Fin d) → ℝ)
    (hc : ∀ i s, 0 ≤ c i s) (w : Fin n → Fin d → ℝ) (hw : ∀ j a, 0 ≤ w j a)
    (i : Fin n) (a : Fin d) : 0 ≤ costVec c w i a := by
  unfold costVec AGT.expectedPayoff
  apply Finset.sum_nonneg
  intro s _
  rw [oo_pp_update]
  apply mul_nonneg _ (hc i s)
  apply mul_nonneg (by split_ifs <;> norm_num)
  exact Finset.prod_nonneg (fun j _ => hw j _)

theorem oo_eq22 {n d : ℕ} [NeZero d]
    (c : Fin n → (Fin n → Fin d) → ℝ)
    (hc : ∀ i s, c i s ∈ Set.Icc (0 : ℝ) 1)
    (w : ℕ → Fin n → Fin d → ℝ) (T : ℕ)
    (hw : ∀ t ∈ Finset.Icc 1 T, AGT.IsMixedProfile (w t))
    (A₁ A₂ : ℝ) (hA₁ : 0 ≤ A₁)
    (hreg : HasFirstOrderRegret c w T A₁ A₂)
    (sstar : Fin n → Fin d) :
    (∑ t ∈ Finset.Icc 1 T, socialCost c (w t)) ≤
      (∑ t ∈ Finset.Icc 1 T, ∑ i, costVec c (w t) i (sstar i)) +
        A₁ * Real.sqrt ((n : ℝ) * Real.log (d : ℝ)) *
          Real.sqrt (∑ t ∈ Finset.Icc 1 T,
            ∑ i, costVec c (w t) i (sstar i)) +
        A₂ * (n : ℝ) * Real.log (d : ℝ) := by
  have hB : ∀ i, 0 ≤ ∑ t ∈ Finset.Icc 1 T, costVec c (w t) i (sstar i) := by
    intro i
    apply Finset.sum_nonneg
    intro t ht
    exact oo_costVec_nonneg c (fun i s => (hc i s).1) (w t) (fun j a => (hw t ht j).1 a) i _
  have hL : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by
    have : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
    exact_mod_cast this)
  have h1 : ∑ i, ((∑ t ∈ Finset.Icc 1 T, (w t i) ⬝ᵥ (costVec c (w t) i)) -
        ∑ t ∈ Finset.Icc 1 T, costVec c (w t) i (sstar i))
      ≤ ∑ i, (A₁ * Real.sqrt (Real.log (d : ℝ) * ∑ t ∈ Finset.Icc 1 T, costVec c (w t) i (sstar i))
        + A₂ * Real.log (d : ℝ)) :=
    Finset.sum_le_sum (fun i _ => hreg i (sstar i))
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, ← Finset.mul_sum] at h1
  have h2 : ∑ i, ∑ t ∈ Finset.Icc 1 T, (w t i) ⬝ᵥ (costVec c (w t) i)
      = ∑ t ∈ Finset.Icc 1 T, socialCost c (w t) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun t _ => (oo_one c (w t)).symm)
  have h3 : ∑ i, Real.sqrt (Real.log (d : ℝ) * ∑ t ∈ Finset.Icc 1 T, costVec c (w t) i (sstar i))
      ≤ Real.sqrt ((n : ℝ) * Real.log (d : ℝ)) *
          Real.sqrt (∑ i, ∑ t ∈ Finset.Icc 1 T, costVec c (w t) i (sstar i)) := by
    have := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset (Fin n))
      (f := fun _ => Real.log (d : ℝ)) (g := fun i => ∑ t ∈ Finset.Icc 1 T, costVec c (w t) i (sstar i))
      (fun _ => hL) hB
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    calc _ = ∑ i, Real.sqrt (Real.log (d : ℝ)) * Real.sqrt (∑ t ∈ Finset.Icc 1 T, costVec c (w t) i (sstar i)) :=
          Finset.sum_congr rfl (fun i _ => Real.sqrt_mul hL _)
      _ ≤ _ := this
  have hc2 : ∑ t ∈ Finset.Icc 1 T, ∑ i, costVec c (w t) i (sstar i)
      = ∑ i, ∑ t ∈ Finset.Icc 1 T, costVec c (w t) i (sstar i) := Finset.sum_comm
  rw [hc2, nsmul_eq_mul] at *
  nlinarith [mul_le_mul_of_nonneg_left h3 hA₁]

theorem solution {n d : ℕ} [NeZero d]
    (c : Fin n → (Fin n → Fin d) → ℝ)
    (hc : ∀ i s, c i s ∈ Set.Icc (0 : ℝ) 1)
    (w : ℕ → Fin n → Fin d → ℝ) (T : ℕ)
    (hw : ∀ t ∈ Finset.Icc 1 T, AGT.IsMixedProfile (w t))
    (A₁ A₂ : ℝ) (hA₁ : 0 ≤ A₁)
    (hreg : HasFirstOrderRegret c w T A₁ A₂)
    (sstar : Fin n → Fin d) :
    (∑ t ∈ Finset.Icc 1 T, socialCost c (w t)) ≤
      (∑ t ∈ Finset.Icc 1 T, ∑ i, costVec c (w t) i (sstar i)) +
        A₁ * Real.sqrt ((n : ℝ) * Real.log (d : ℝ)) *
          Real.sqrt (∑ t ∈ Finset.Icc 1 T,
            ∑ i, costVec c (w t) i (sstar i)) +
        A₂ * (n : ℝ) * Real.log (d : ℝ) :=
  oo_eq22 c hc w T hw A₁ A₂ hA₁ hreg sstar
