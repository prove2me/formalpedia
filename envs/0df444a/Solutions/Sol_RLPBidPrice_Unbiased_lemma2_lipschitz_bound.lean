-- Prove2me | solution 1 for RLPBidPrice.Unbiased.lemma2_lipschitz_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T09:29:29.750302+00:00
-- url     : https://prove2.me/submissions/191c75a9-cb0d-4f3a-bcfe-e42c338e5e64

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model

open MeasureTheory Matrix

namespace RLPSol
open RLPBidPrice.Unbiased

variable {m n : ℕ}

theorem pv_bdd (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ) (hr : 0 ≤ r)
    (x : Fin m → ℝ) (y₀ : Fin n → ℝ) :
    BddAbove {v : ℝ | ∃ y : Fin n → ℝ, A *ᵥ y ≤ x ∧ 0 ≤ y ∧ y ≤ y₀ ∧ v = r ⬝ᵥ y} :=
  ⟨r ⬝ᵥ y₀, by
    rintro _ ⟨y, -, -, hyy, rfl⟩
    exact dotProduct_le_dotProduct_of_nonneg_left hyy hr⟩

theorem le_pv {A : Matrix (Fin m) (Fin n) ℝ} {r : Fin n → ℝ} (hr : 0 ≤ r)
    {x : Fin m → ℝ} {y₀ y : Fin n → ℝ} (h1 : A *ᵥ y ≤ x) (h2 : 0 ≤ y) (h3 : y ≤ y₀) :
    r ⬝ᵥ y ≤ piValue A r x y₀ :=
  le_csSup (pv_bdd A r hr x y₀) ⟨y, h1, h2, h3, rfl⟩

theorem pv_le {A : Matrix (Fin m) (Fin n) ℝ} {r : Fin n → ℝ}
    {x : Fin m → ℝ} {y₀ : Fin n → ℝ} (hx : 0 ≤ x) (hy₀ : 0 ≤ y₀) {c : ℝ}
    (h : ∀ y, A *ᵥ y ≤ x → 0 ≤ y → y ≤ y₀ → r ⬝ᵥ y ≤ c) :
    piValue A r x y₀ ≤ c := by
  refine csSup_le ⟨0, ?_⟩ ?_
  · exact ⟨0, by simpa using hx, le_refl _, hy₀, by simp⟩
  rintro _ ⟨y, h1, h2, h3, rfl⟩
  exact h y h1 h2 h3

theorem pv_attained (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ) (hr : 0 ≤ r)
    {x : Fin m → ℝ} {y₀ : Fin n → ℝ} (hx : 0 ≤ x) (hy₀ : 0 ≤ y₀) :
    ∃ y, A *ᵥ y ≤ x ∧ 0 ≤ y ∧ y ≤ y₀ ∧ r ⬝ᵥ y = piValue A r x y₀ := by
  have hK : IsCompact (Set.Icc 0 y₀ ∩ {y : Fin n → ℝ | A *ᵥ y ≤ x}) :=
    isCompact_Icc.inter_right (isClosed_le (continuous_const.matrix_mulVec continuous_id)
      continuous_const)
  have hne : (Set.Icc 0 y₀ ∩ {y : Fin n → ℝ | A *ᵥ y ≤ x}).Nonempty :=
    ⟨0, ⟨le_refl _, hy₀⟩, by simpa using hx⟩
  obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn hne
    (continuous_const.dotProduct continuous_id : Continuous fun y : Fin n → ℝ => r ⬝ᵥ y).continuousOn
  refine ⟨y, hy.2, hy.1.1, hy.1.2, le_antisymm (le_pv hr hy.2 hy.1.1 hy.1.2) ?_⟩
  apply pv_le hx hy₀
  intro z h1 h2 h3
  exact hmax ⟨⟨h2, h3⟩, h1⟩

theorem mulVec_sum_swap (A : Matrix (Fin m) (Fin n) ℝ) (μ : Fin m → ℝ) (y : Fin n → ℝ) :
    μ ⬝ᵥ (A *ᵥ y) = ∑ j, y j * ∑ i, μ i * A i j := by
  simp only [mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem obj_split (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ) (μ : Fin m → ℝ)
    (y : Fin n → ℝ) :
    r ⬝ᵥ y = ∑ j, y j * (r j - ∑ i, μ i * A i j) + μ ⬝ᵥ (A *ᵥ y) := by
  rw [mulVec_sum_swap, ← Finset.sum_add_distrib]
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun j _ => by ring

theorem weak_duality {A : Matrix (Fin m) (Fin n) ℝ} {r : Fin n → ℝ}
    {x : Fin m → ℝ} {y₀ y : Fin n → ℝ} {μ : Fin m → ℝ} (hμ : 0 ≤ μ)
    (h1 : A *ᵥ y ≤ x) (h2 : 0 ≤ y) (h3 : y ≤ y₀) :
    r ⬝ᵥ y ≤ lagr A r x y₀ μ := by
  rw [obj_split A r μ y, lagr]
  refine add_le_add (Finset.sum_le_sum fun j _ => ?_)
    (dotProduct_le_dotProduct_of_nonneg_left h1 hμ)
  calc y j * (r j - ∑ i, μ i * A i j) ≤ y j * max 0 (r j - ∑ i, μ i * A i j) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (h2 j)
    _ ≤ y₀ j * max 0 (r j - ∑ i, μ i * A i j) :=
        mul_le_mul_of_nonneg_right (h3 j) (le_max_left _ _)

theorem pv_le_lagr {A : Matrix (Fin m) (Fin n) ℝ} {r : Fin n → ℝ}
    {x : Fin m → ℝ} {y₀ : Fin n → ℝ} (hx : 0 ≤ x) (hy₀ : 0 ≤ y₀) {μ : Fin m → ℝ} (hμ : 0 ≤ μ) :
    piValue A r x y₀ ≤ lagr A r x y₀ μ :=
  pv_le hx hy₀ fun _ h1 h2 h3 => weak_duality hμ h1 h2 h3

theorem pv_mono {A : Matrix (Fin m) (Fin n) ℝ} {r : Fin n → ℝ} (hr : 0 ≤ r)
    {x x' : Fin m → ℝ} {y₀ : Fin n → ℝ} (hx : 0 ≤ x) (hy₀ : 0 ≤ y₀) (hxx : x ≤ x') :
    piValue A r x y₀ ≤ piValue A r x' y₀ :=
  pv_le hx hy₀ fun _ h1 h2 h3 => le_pv hr (h1.trans hxx) h2 h3

theorem le_rbar (r : Fin n → ℝ) (j : Fin n) : r j ≤ ⨆ j, r j :=
  le_ciSup (Set.finite_range r).bddAbove j

theorem rbar_nonneg (r : Fin n → ℝ) (hr : 0 ≤ r) : 0 ≤ ⨆ j, r j :=
  Real.iSup_nonneg hr

/-- Lemma 2 upper bound. -/
theorem lemma2_upper {A : Matrix (Fin m) (Fin n) ℝ} {r : Fin n → ℝ}
    (hA : IsIncidence A) (hr : 0 ≤ r) {x : Fin m → ℝ} (hx : 0 ≤ x)
    {y₀ : Fin n → ℝ} (hy₀ : 0 ≤ y₀) (i : Fin m) {h : ℝ} (hh : 0 ≤ h) :
    piValue A r (x + h • Pi.single i 1) y₀ ≤ piValue A r x y₀ + h * ⨆ j, r j := by
  have hx' : 0 ≤ x + h • Pi.single i 1 := by
    intro k; simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, Pi.zero_apply]
    have : 0 ≤ x k := hx k
    split_ifs <;> nlinarith
  apply pv_le hx' hy₀
  intro y h1 h2 h3
  set R := ⨆ j, r j
  have hA01 : ∀ k j, 0 ≤ A k j ∧ A k j ≤ 1 := fun k j => by
    rcases hA.1 k j with h | h <;> rw [h] <;> norm_num
  have hAsq : ∀ k j, A k j * A k j = A k j := fun k j => by
    rcases hA.1 k j with h | h <;> rw [h] <;> norm_num
  have hoff : ∀ k, k ≠ i → (A *ᵥ y) k ≤ x k := fun k hk => by
    have := h1 k; simpa [Pi.single_apply, hk] using this
  have hon : (A *ᵥ y) i ≤ x i + h := by
    have := h1 i; simpa [Pi.single_apply] using this
  set s := (A *ᵥ y) i with hs
  have hsdef : s = ∑ j, A i j * y j := rfl
  by_cases hsx : s ≤ x i
  · have hfe : A *ᵥ y ≤ x := fun k => by
      by_cases hk : k = i
      · subst hk; exact hsx
      · exact hoff k hk
    have := le_pv hr hfe h2 h3
    have : 0 ≤ h * R := mul_nonneg hh (rbar_nonneg r hr)
    linarith
  push Not at hsx
  have hspos : 0 < s := lt_of_le_of_lt (hx i) hsx
  set t := x i / s with ht
  have ht0 : 0 ≤ t := div_nonneg (hx i) hspos.le
  have ht1 : t ≤ 1 := (div_le_one hspos).2 hsx.le
  have hts : t * s = x i := by rw [ht]; field_simp
  set y' : Fin n → ℝ := fun j => (1 - (1 - t) * A i j) * y j with hy'
  have h1t' : 0 ≤ 1 - t := by linarith
  have hc0 : ∀ j, 0 ≤ 1 - (1 - t) * A i j := fun j => by
    have := mul_le_mul_of_nonneg_left (hA01 i j).2 h1t'; nlinarith
  have hc1 : ∀ j, 1 - (1 - t) * A i j ≤ 1 := fun j => by
    have := mul_nonneg h1t' (hA01 i j).1; nlinarith
  have hy'0 : 0 ≤ y' := fun j => mul_nonneg (hc0 j) (h2 j)
  have hy'y : y' ≤ y := fun j => by
    show (1 - (1 - t) * A i j) * y j ≤ y j
    have hyj : 0 ≤ y j := h2 j
    exact mul_le_of_le_one_left hyj (hc1 j)
  have hfe : A *ᵥ y' ≤ x := by
    intro k
    by_cases hk : k = i
    · subst hk
      have : (A *ᵥ y') k = t * s := by
        simp only [mulVec, dotProduct, hy', hsdef, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have := hAsq k j
        linear_combination (-(1 - t) * y j) * this
      rw [this, hts]
    · calc (A *ᵥ y') k ≤ (A *ᵥ y) k := by
            simp only [mulVec, dotProduct]
            exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hy'y j) (hA01 k j).1
        _ ≤ x k := hoff k hk
  have hle := le_pv hr hfe hy'0 (hy'y.trans h3)
  have hdiff : r ⬝ᵥ y - r ⬝ᵥ y' = (1 - t) * ∑ j, r j * (A i j * y j) := by
    simp only [dotProduct, hy', ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  have hbound : ∑ j, r j * (A i j * y j) ≤ R * s := by
    rw [hsdef, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_right (le_rbar r j) (mul_nonneg (hA01 i j).1 (h2 j))
  have hR : 0 ≤ R := rbar_nonneg r hr
  have h1t : 0 ≤ 1 - t := by linarith
  have : (1 - t) * ∑ j, r j * (A i j * y j) ≤ (1 - t) * (R * s) :=
    mul_le_mul_of_nonneg_left hbound h1t
  have : (1 - t) * (R * s) = R * (s - x i) := by rw [← hts]; ring
  nlinarith

theorem lemma2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)
    (hA : IsIncidence A) (hr : 0 ≤ r) (x : Fin m → ℝ) (hx : 0 ≤ x)
    (y₀ : Fin n → ℝ) (hy₀ : 0 ≤ y₀) (i : Fin m) (h : ℝ) (hh : 0 ≤ h) :
    |piValue A r (x + h • Pi.single i 1) y₀ - piValue A r x y₀| ≤ h * ⨆ j, r j := by
  have hmono : piValue A r x y₀ ≤ piValue A r (x + h • Pi.single i 1) y₀ := by
    apply pv_mono hr hx hy₀
    intro k; simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> linarith
  rw [abs_of_nonneg (by linarith)]
  linarith [lemma2_upper hA hr hx hy₀ i hh]

end RLPSol

open RLPBidPrice.Unbiased in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)
    (hA : IsIncidence A) (hr : 0 ≤ r) (x : Fin m → ℝ) (hx : 0 ≤ x)
    (y₀ : Fin n → ℝ) (hy₀ : 0 ≤ y₀) (i : Fin m) (h : ℝ) (hh : 0 ≤ h) :
    |piValue A r (x + h • Pi.single i 1) y₀ - piValue A r x y₀| ≤ h * ⨆ j, r j :=
  RLPSol.lemma2 A r hA hr x hx y₀ hy₀ i h hh
