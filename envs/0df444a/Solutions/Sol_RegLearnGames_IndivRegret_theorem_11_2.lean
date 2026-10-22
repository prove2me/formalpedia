-- Prove2me | solution 2 for RegLearnGames.IndivRegret.theorem_11
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:27:34.551092+00:00
-- url     : https://prove2.me/submissions/329d48cd-8c7d-4e4a-a68b-db89c31d4032

import Mathlib
import Definitions.Def_RegLearnGames_TotalRegret_Setting

set_option autoImplicit false

open Finset

lemma rgt_sum_prod_one {d : ℕ} {α : Type} [Fintype α] [DecidableEq α] (a : α → Fin d → ℝ)
    (ha : ∀ k, ∑ x, a k x = 1) : ∑ t : α → Fin d, ∏ k, a k (t k) = 1 := by
  have := Finset.prod_univ_sum (fun k => (Finset.univ : Finset (Fin d))) (fun k x => a k x)
  rw [Fintype.piFinset_univ] at this
  rw [← this]
  simp [ha]

lemma rgt_tv_prod (d : ℕ) (ι : Type) [Fintype ι] : ∀ [DecidableEq ι],
    ∀ (a b : ι → Fin d → ℝ), (∀ j x, 0 ≤ a j x) → (∀ j x, 0 ≤ b j x) →
      (∀ j, ∑ x, a j x = 1) → (∀ j, ∑ x, b j x = 1) →
      ∑ s : ι → Fin d, |∏ j, a j (s j) - ∏ j, b j (s j)| ≤ ∑ j, ∑ x, |a j x - b j x| := by
  refine Fintype.induction_empty_option
    (P := fun ι _ => ∀ [DecidableEq ι],
    ∀ (a b : ι → Fin d → ℝ), (∀ j x, 0 ≤ a j x) → (∀ j x, 0 ≤ b j x) →
      (∀ j, ∑ x, a j x = 1) → (∀ j, ∑ x, b j x = 1) →
      ∑ s : ι → Fin d, |∏ j, a j (s j) - ∏ j, b j (s j)| ≤ ∑ j, ∑ x, |a j x - b j x|)
    ?_ ?_ ?_ ι
  · intro α β _ e ih _ a b ha0 hb0 ha1 hb1
    let _ : Fintype α := Fintype.ofEquiv β e.symm
    classical
    have := ih (fun k => a (e k)) (fun k => b (e k)) (fun j x => ha0 _ _) (fun j x => hb0 _ _)
      (fun j => ha1 _) (fun j => hb1 _)
    refine le_of_eq_of_le ?_ (le_of_le_of_eq this ?_)
    · rw [← (Equiv.arrowCongr e (Equiv.refl (Fin d))).sum_comp]
      refine Finset.sum_congr rfl fun s _ => ?_
      congr 1
      have h1 : ∏ j, a j ((Equiv.arrowCongr e (Equiv.refl (Fin d))) s j)
          = ∏ j, a (e j) (s j) := by
        rw [← e.prod_comp]; simp [Equiv.arrowCongr]
      have h2 : ∏ j, b j ((Equiv.arrowCongr e (Equiv.refl (Fin d))) s j)
          = ∏ j, b (e j) (s j) := by
        rw [← e.prod_comp]; simp [Equiv.arrowCongr]
      rw [h1, h2]
    · rw [← e.sum_comp]
  · intro _ a b _ _ _ _
    simp
  · intro α _ ih _ a b ha0 hb0 ha1 hb1
    classical
    have IH := ih (fun k => a (some k)) (fun k => b (some k)) (fun j x => ha0 _ _)
      (fun j x => hb0 _ _) (fun j => ha1 _) (fun j => hb1 _)
    have hA1 := rgt_sum_prod_one (fun k => a (some k)) (fun k => ha1 _)
    set A : (α → Fin d) → ℝ := fun t => ∏ k, a (some k) (t k) with hA
    set B : (α → Fin d) → ℝ := fun t => ∏ k, b (some k) (t k) with hB
    have hA0 : ∀ t, 0 ≤ A t := fun t => Finset.prod_nonneg fun k _ => ha0 _ _
    have hB0 : ∀ t, 0 ≤ B t := fun t => Finset.prod_nonneg fun k _ => hb0 _ _
    have hsum : ∑ s : Option α → Fin d, |∏ j, a j (s j) - ∏ j, b j (s j)|
        = ∑ x : Fin d, ∑ t : α → Fin d, |a none x * A t - b none x * B t| := by
      rw [← (Equiv.piOptionEquivProd (β := fun _ : Option α => Fin d)).symm.sum_comp,
        Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun t _ => ?_
      simp [Fintype.prod_option, hA, hB]
    rw [hsum, Fintype.sum_option]
    have step : ∀ x t, |a none x * A t - b none x * B t|
        ≤ |a none x - b none x| * A t + b none x * |A t - B t| := by
      intro x t
      have : a none x * A t - b none x * B t
          = (a none x - b none x) * A t + b none x * (A t - B t) := by ring
      rw [this]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg (hA0 t), abs_of_nonneg (hb0 none x)]
    calc ∑ x : Fin d, ∑ t : α → Fin d, |a none x * A t - b none x * B t|
        ≤ ∑ x : Fin d, ∑ t : α → Fin d,
            (|a none x - b none x| * A t + b none x * |A t - B t|) :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun t _ => step x t
      _ = (∑ x, |a none x - b none x|) * (∑ t, A t)
            + (∑ x, b none x) * (∑ t, |A t - B t|) := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      _ ≤ (∑ x, |a none x - b none x|) + ∑ k, ∑ x, |a (some k) x - b (some k) x| := by
          rw [hA1, hb1 none]
          simp only [mul_one, one_mul]
          linarith [IH]

lemma rgt_util_rep {n d : ℕ} (u : Fin n → (Fin n → Fin d) → ℝ) (w : Fin n → Fin d → ℝ)
    (i : Fin n) (x : Fin d) :
    RegLearnGames.TotalRegret.utilVec u w i x =
      ∑ t : {j // j ≠ i} → Fin d, (∏ j : {j // j ≠ i}, w j.1 (t j)) *
        u i ((Equiv.piSplitAt i (fun _ => Fin d)).symm (x, t)) := by
  unfold RegLearnGames.TotalRegret.utilVec AGT.expectedPayoff AGT.profileProb
  rw [← (Equiv.piSplitAt i (fun _ => Fin d)).symm.sum_comp, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single x]
  · refine Finset.sum_congr rfl fun t _ => ?_
    congr 1
    rw [Fintype.prod_eq_mul_prod_subtype_ne (fun j => Function.update w i (Pi.single x 1) j
      (((Equiv.piSplitAt i (fun _ => Fin d)).symm (x, t)) j)) i]
    have h1 : ((Equiv.piSplitAt i (fun _ => Fin d)).symm (x, t)) i = x := by
      simp [Equiv.piSplitAt]
    have h2 : ∀ j : {j // j ≠ i}, ((Equiv.piSplitAt i (fun _ => Fin d)).symm (x, t)) j.1 = t j := by
      intro j; simp [Equiv.piSplitAt, j.2]
    simp only [h1, h2, Function.update_self, Pi.single_eq_same, one_mul]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Function.update_of_ne j.2]
  · intro y _ hy
    refine Finset.sum_eq_zero fun t _ => ?_
    have h1 : ((Equiv.piSplitAt i (fun _ => Fin d)).symm (y, t)) i = y := by
      simp [Equiv.piSplitAt]
    rw [Fintype.prod_eq_mul_prod_subtype_ne (fun j => Function.update w i (Pi.single x 1) j
      (((Equiv.piSplitAt i (fun _ => Fin d)).symm (y, t)) j)) i]
    simp [h1, hy]
  · simp

lemma rgt_delta_core {n d : ℕ} (u : Fin n → (Fin n → Fin d) → ℝ)
    (hu : ∀ i s, u i s ∈ Set.Icc (0 : ℝ) 1)
    (w w' : Fin n → Fin d → ℝ) (i : Fin n) :
    ‖RegLearnGames.TotalRegret.utilVec u w i - RegLearnGames.TotalRegret.utilVec u w' i‖ ≤
      ∑ s : {j : Fin n // j ≠ i} → Fin d, |∏ j, w j.1 (s j) - ∏ j, w' j.1 (s j)| := by
  have h0 : 0 ≤ ∑ s : {j : Fin n // j ≠ i} → Fin d, |∏ j, w j.1 (s j) - ∏ j, w' j.1 (s j)| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  rw [pi_norm_le_iff_of_nonneg h0]
  intro x
  rw [Pi.sub_apply, rgt_util_rep, rgt_util_rep, Real.norm_eq_abs, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => ?_)
  rw [← sub_mul, abs_mul]
  have := hu i ((Equiv.piSplitAt i (fun _ => Fin d)).symm (x, t))
  rw [abs_of_nonneg this.1]
  exact mul_le_of_le_one_right (abs_nonneg _) this.2

lemma rgt_delta_l1 {n d : ℕ} (u : Fin n → (Fin n → Fin d) → ℝ)
    (hu : ∀ i s, u i s ∈ Set.Icc (0 : ℝ) 1)
    (w w' : Fin n → Fin d → ℝ) (hw : ∀ j, w j ∈ stdSimplex ℝ (Fin d))
    (hw' : ∀ j, w' j ∈ stdSimplex ℝ (Fin d)) (i : Fin n) :
    ∑ s : {j : Fin n // j ≠ i} → Fin d, |∏ j, w j.1 (s j) - ∏ j, w' j.1 (s j)| ≤
      ∑ j : {j : Fin n // j ≠ i}, RegLearnGames.TotalRegret.l1 (w j.1 - w' j.1) := by
  have := rgt_tv_prod d {j : Fin n // j ≠ i} (fun j => w j.1) (fun j => w' j.1)
    (fun j x => (hw j.1).1 x) (fun j x => (hw' j.1).1 x) (fun j => (hw j.1).2) (fun j => (hw' j.1).2)
  simpa [RegLearnGames.TotalRegret.l1] using this

lemma rgt_delta_le {n d : ℕ} (u : Fin n → (Fin n → Fin d) → ℝ)
    (hu : ∀ i s, u i s ∈ Set.Icc (0 : ℝ) 1)
    (w w' : Fin n → Fin d → ℝ) (hw : ∀ j, w j ∈ stdSimplex ℝ (Fin d))
    (hw' : ∀ j, w' j ∈ stdSimplex ℝ (Fin d)) (i : Fin n) :
    ‖RegLearnGames.TotalRegret.utilVec u w i - RegLearnGames.TotalRegret.utilVec u w' i‖ ≤
      ∑ j ∈ Finset.univ.erase i, RegLearnGames.TotalRegret.l1 (w j - w' j) := by
  refine (rgt_delta_core u hu w w' i).trans ((rgt_delta_l1 u hu w w' hw hw' i).trans (le_of_eq ?_))
  exact (Finset.sum_subtype (Finset.univ.erase i) (p := fun j => j ≠ i) (by simp)
    (fun j => RegLearnGames.TotalRegret.l1 (w j - w' j))).symm

lemma rgt_l1_nonneg {d : ℕ} (v : Fin d → ℝ) : 0 ≤ RegLearnGames.TotalRegret.l1 v :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma rgt_card_erase {n : ℕ} (i : Fin n) :
    ((Finset.univ.erase i).card : ℝ) = (n : ℝ) - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  have : 1 ≤ n := by have := i.2; omega
  push_cast [Nat.cast_sub this]
  ring

lemma rgt_delta_sq {n d : ℕ} (u : Fin n → (Fin n → Fin d) → ℝ)
    (hu : ∀ i s, u i s ∈ Set.Icc (0 : ℝ) 1)
    (w w' : Fin n → Fin d → ℝ) (hw : ∀ j, w j ∈ stdSimplex ℝ (Fin d))
    (hw' : ∀ j, w' j ∈ stdSimplex ℝ (Fin d)) (i : Fin n) :
    ‖RegLearnGames.TotalRegret.utilVec u w i - RegLearnGames.TotalRegret.utilVec u w' i‖ ^ 2 ≤
      ((n : ℝ) - 1) * ∑ j ∈ Finset.univ.erase i, RegLearnGames.TotalRegret.l1 (w j - w' j) ^ 2 := by
  have h1 := rgt_delta_le u hu w w' hw hw' i
  have h2 : (∑ j ∈ Finset.univ.erase i, RegLearnGames.TotalRegret.l1 (w j - w' j)) ^ 2 ≤
      ((Finset.univ.erase i).card : ℝ) *
        ∑ j ∈ Finset.univ.erase i, RegLearnGames.TotalRegret.l1 (w j - w' j) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [rgt_card_erase] at h2
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

lemma rgt_sum_erase {n : ℕ} (f : Fin n → ℝ) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, f j = ((n : ℝ) - 1) * ∑ j, f j := by
  have : ∀ i : Fin n, ∑ j ∈ Finset.univ.erase i, f j = ∑ j, f j - f i := fun i =>
    Finset.sum_erase_eq_sub (Finset.mem_univ i)
  simp only [this, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

lemma rgt_var4 {n d : ℕ} (u : Fin n → (Fin n → Fin d) → ℝ)
    (hu : ∀ i s, u i s ∈ Set.Icc (0 : ℝ) 1)
    (w w' : Fin n → Fin d → ℝ) (hw : ∀ j, w j ∈ stdSimplex ℝ (Fin d))
    (hw' : ∀ j, w' j ∈ stdSimplex ℝ (Fin d)) :
    ∑ i, ‖RegLearnGames.TotalRegret.utilVec u w i - RegLearnGames.TotalRegret.utilVec u w' i‖ ^ 2 ≤
      ((n : ℝ) - 1) * ∑ i, ∑ j ∈ Finset.univ.erase i, RegLearnGames.TotalRegret.l1 (w j - w' j) ^ 2 ∧
    ((n : ℝ) - 1) * ∑ i, ∑ j ∈ Finset.univ.erase i, RegLearnGames.TotalRegret.l1 (w j - w' j) ^ 2 =
      ((n : ℝ) - 1) ^ 2 * ∑ i, RegLearnGames.TotalRegret.l1 (w i - w' i) ^ 2 := by
  constructor
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => rgt_delta_sq u hu w w' hw hw' i
  · rw [rgt_sum_erase (fun j => RegLearnGames.TotalRegret.l1 (w j - w' j) ^ 2)]
    ring

lemma rgt_var11 {n d : ℕ} (u : Fin n → (Fin n → Fin d) → ℝ)
    (hu : ∀ i s, u i s ∈ Set.Icc (0 : ℝ) 1)
    (w w' : Fin n → Fin d → ℝ) (hw : ∀ j, w j ∈ stdSimplex ℝ (Fin d))
    (hw' : ∀ j, w' j ∈ stdSimplex ℝ (Fin d)) (κ : ℝ)
    (hκ : ∀ j, RegLearnGames.TotalRegret.l1 (w j - w' j) ≤ κ) (i : Fin n) :
    ((n : ℝ) - 1) * ∑ j ∈ Finset.univ.erase i, RegLearnGames.TotalRegret.l1 (w j - w' j) ^ 2 ≤
        ((n : ℝ) - 1) ^ 2 * κ ^ 2 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have h1 : 1 ≤ n := by have := i.2; omega
    have : (1 : ℝ) ≤ n := by exact_mod_cast h1
    linarith
  have h1 : ∑ j ∈ Finset.univ.erase i, RegLearnGames.TotalRegret.l1 (w j - w' j) ^ 2 ≤
      ∑ j ∈ Finset.univ.erase i, κ ^ 2 :=
    Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (rgt_l1_nonneg _) (hκ j) 2
  rw [Finset.sum_const, nsmul_eq_mul, rgt_card_erase] at h1
  calc _ ≤ ((n : ℝ) - 1) * (((n : ℝ) - 1) * κ ^ 2) := mul_le_mul_of_nonneg_left h1 hn
    _ = ((n : ℝ) - 1) ^ 2 * κ ^ 2 := by ring

lemma rgt_l1_neg {d : ℕ} (v : Fin d → ℝ) :
    RegLearnGames.TotalRegret.l1 (-v) = RegLearnGames.TotalRegret.l1 v := by
  simp [RegLearnGames.TotalRegret.l1]

theorem solution {n d : ℕ} (u : Fin n → (Fin n → Fin d) → ℝ)
    (hu : ∀ i s, u i s ∈ Set.Icc (0 : ℝ) 1)
    (w : ℕ → Fin n → Fin d → ℝ) (hw : ∀ t i, w t i ∈ stdSimplex ℝ (Fin d))
    (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 ≤ γ) (T : ℕ)
    (hRVU : ∀ i, ∀ v ∈ stdSimplex ℝ (Fin d),
      ∑ t ∈ Finset.Icc 1 T, (v - w t i) ⬝ᵥ RegLearnGames.TotalRegret.utilVec u (w t) i ≤
        α + β * ∑ t ∈ Finset.Icc 1 T, ‖RegLearnGames.TotalRegret.utilVec u (w t) i - RegLearnGames.TotalRegret.utilVec u (w (t - 1)) i‖ ^ 2
          - γ * ∑ t ∈ Finset.Icc 1 T, RegLearnGames.TotalRegret.l1 (w t i - w (t - 1) i) ^ 2)
    (κ : ℝ) (hκ : ∀ i, ∀ t < T, RegLearnGames.TotalRegret.l1 (w t i - w (t + 1) i) ≤ κ) :
    ∀ i, ∀ wstar ∈ stdSimplex ℝ (Fin d),
      ∑ t ∈ Finset.Icc 1 T, (wstar - w t i) ⬝ᵥ RegLearnGames.TotalRegret.utilVec u (w t) i ≤
        α + β * κ ^ 2 * ((n : ℝ) - 1) ^ 2 * T := by
  intro i wstar hwstar
  have h := hRVU i wstar hwstar
  have hb : ∀ t ∈ Finset.Icc 1 T,
      ‖RegLearnGames.TotalRegret.utilVec u (w t) i - RegLearnGames.TotalRegret.utilVec u (w (t - 1)) i‖ ^ 2 ≤
        ((n : ℝ) - 1) ^ 2 * κ ^ 2 := by
    intro t ht
    obtain ⟨ht1, htT⟩ := Finset.mem_Icc.mp ht
    have hk : ∀ j, RegLearnGames.TotalRegret.l1 (w t j - w (t - 1) j) ≤ κ := by
      intro j
      have h3 := hκ j (t - 1) (by omega)
      have e : t - 1 + 1 = t := by omega
      rw [e] at h3
      rw [show w t j - w (t - 1) j = -(w (t - 1) j - w t j) by abel, rgt_l1_neg]
      exact h3
    exact (rgt_delta_sq u hu (w t) (w (t - 1)) (hw t) (hw (t - 1)) i).trans
      (rgt_var11 u hu (w t) (w (t - 1)) (hw t) (hw (t - 1)) κ hk i)
  have h4 : ∑ t ∈ Finset.Icc 1 T,
      ‖RegLearnGames.TotalRegret.utilVec u (w t) i - RegLearnGames.TotalRegret.utilVec u (w (t - 1)) i‖ ^ 2
      ≤ T * (((n : ℝ) - 1) ^ 2 * κ ^ 2) := by
    refine (Finset.sum_le_sum hb).trans (le_of_eq ?_)
    simp
  have h5 : 0 ≤ ∑ t ∈ Finset.Icc 1 T, RegLearnGames.TotalRegret.l1 (w t i - w (t - 1) i) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h6 := mul_le_mul_of_nonneg_left h4 hβ.le
  have h7 := mul_nonneg hγ h5
  nlinarith [h6, h7]
