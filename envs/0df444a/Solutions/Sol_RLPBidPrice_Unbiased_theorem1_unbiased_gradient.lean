-- Prove2me | solution 1 for RLPBidPrice.Unbiased.theorem1_unbiased_gradient
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T09:52:03.571197+00:00
-- url     : https://prove2.me/submissions/075a6615-3420-44dd-915a-4b6e999d9fff

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model
import Theorems.Thm_RLPBidPrice_Unbiased_lemma4_ae_gradient_exists
import Theorems.Thm_RLPBidPrice_Unbiased_strong_duality_subgradient

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

open MeasureTheory Matrix Filter Topology

namespace RLPSol
open RLPBidPrice.Unbiased

variable {m n : ℕ}

theorem lagr_sub (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ) (x z : Fin m → ℝ)
    (y₀ : Fin n → ℝ) (μ : Fin m → ℝ) :
    lagr A r z y₀ μ = lagr A r x y₀ μ + μ ⬝ᵥ (z - x) := by
  simp only [lagr, dotProduct_sub]; ring

theorem incid01 {A : Matrix (Fin m) (Fin n) ℝ} (hA : IsIncidence A) (k : Fin m) (j : Fin n) :
    0 ≤ A k j ∧ A k j ≤ 1 := by
  rcases hA.1 k j with h | h <;> rw [h] <;> norm_num

theorem lagr_trunc {A : Matrix (Fin m) (Fin n) ℝ} {r : Fin n → ℝ}
    (hA : IsIncidence A) (hr : 0 ≤ r) {x : Fin m → ℝ} (hx : 0 ≤ x)
    {y₀ : Fin n → ℝ} (hy₀ : 0 ≤ y₀) {μ : Fin m → ℝ} (hμ : 0 ≤ μ) :
    lagr A r x y₀ (fun i => min (μ i) (⨆ j, r j)) ≤ lagr A r x y₀ μ := by
  have hR : 0 ≤ ⨆ j, r j := rbar_nonneg r hr
  set R := ⨆ j, r j
  unfold lagr
  refine add_le_add (Finset.sum_le_sum fun j _ => ?_) ?_
  · refine mul_le_mul_of_nonneg_left ?_ (hy₀ j)
    by_cases h : ∃ i, A i j = 1 ∧ R < μ i
    · obtain ⟨i, hi1, hiR⟩ := h
      have hle : min (μ i) R * A i j ≤ ∑ k, min (μ k) R * A k j := by
        apply Finset.single_le_sum (f := fun k => min (μ k) R * A k j) _ (Finset.mem_univ i)
        intro k _
        exact mul_nonneg (le_min (hμ k) hR) (incid01 hA k j).1
      rw [hi1, min_eq_right hiR.le, mul_one] at hle
      have : r j - ∑ k, min (μ k) R * A k j ≤ 0 := by linarith [le_rbar r j]
      rw [max_eq_left this]
      exact le_max_left _ _
    · push Not at h
      have : ∑ k, min (μ k) R * A k j = ∑ k, μ k * A k j := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rcases hA.1 k j with h0 | h1
        · rw [h0]; simp
        · rw [min_eq_left (h k h1)]
      rw [this]
  · exact dotProduct_le_dotProduct_of_nonneg_right (fun i => min_le_left _ _) hx

theorem gradCLM_apply' (g h : Fin m → ℝ) : gradCLM g h = g ⬝ᵥ h := by
  simp [gradCLM, dotProduct]

theorem eventually_pos {x : Fin m → ℝ} (hx : ∀ i, 0 < x i) : ∀ᶠ x' in 𝓝 x, ∀ i, 0 < x' i :=
  Filter.eventually_all.2 fun i => (continuous_apply i).continuousAt.eventually (Ioi_mem_nhds (hx i))

theorem dot_le (a b : Fin m → ℝ) : |a ⬝ᵥ b| ≤ m * (‖a‖ * ‖b‖) := by
  calc |a ⬝ᵥ b| ≤ ∑ i, |a i * b i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin m, ‖a‖ * ‖b‖ := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        have h1 := norm_le_pi_norm a i
        have h2 := norm_le_pi_norm b i
        rw [Real.norm_eq_abs] at h1 h2
        exact mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
    _ = m * (‖a‖ * ‖b‖) := by simp

theorem norm_le_of_box {R : ℝ} (hR : 0 ≤ R) {ν : Fin m → ℝ}
    (hν : ν ∈ Set.Icc (0 : Fin m → ℝ) (fun _ => R)) : ‖ν‖ ≤ R :=
  (pi_norm_le_iff_of_nonneg hR).2 fun i => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hν.1 i)]; exact hν.2 i

theorem c1_zero {A : Matrix (Fin m) (Fin n) ℝ} {x : Fin m → ℝ} (hC1 : ConditionOnePrime A x)
    {y : Fin n → ℝ} (h2 : 0 ≤ y) (d : Fin m → ℝ)
    (hd1 : ∀ j, 0 < y j → d ⬝ᵥ (fun i => A i j) = 0)
    (hd2 : ∀ i, (A *ᵥ y) i < x i → d i = 0) (h1 : A *ᵥ y ≤ x) : d = 0 := by
  classical
  set S : Finset (Fin n) := Finset.univ.filter fun j => 0 < y j
  set T : Finset (Fin m) := Finset.univ.filter fun i => (A *ᵥ y) i < x i
  have hxmem : x ∈ Submodule.span ℝ (colSet A S T) := by
    have hx : x = ∑ j ∈ S, y j • (fun i => A i j) +
        ∑ i ∈ T, (x i - (A *ᵥ y) i) • (Pi.single i 1 : Fin m → ℝ) := by
      ext k
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', S, T]
      have hS : ∑ j ∈ Finset.univ.filter (fun j => 0 < y j), y j * A k j = (A *ᵥ y) k := by
        rw [Finset.sum_filter]
        simp only [mulVec, dotProduct]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs with h
        · ring
        · have : y j = 0 := le_antisymm (not_lt.1 h) (h2 j)
          rw [this]; ring
      rw [hS]
      by_cases hk : (A *ᵥ y) k < x k
      · simp [hk]
      · have : (A *ᵥ y) k = x k := le_antisymm (h1 k) (not_lt.1 hk)
        simp [hk, this]
    rw [hx]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_)
      (Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_)
    · exact Submodule.subset_span (Or.inl ⟨j, hj, rfl⟩)
    · exact Submodule.subset_span (Or.inr ⟨i, hi, rfl⟩)
  have htop := hC1 S T hxmem
  have hker : ∀ v ∈ Submodule.span ℝ (colSet A S T), d ⬝ᵥ v = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      rcases hv with ⟨j, hj, rfl⟩ | ⟨i, hi, rfl⟩
      · exact hd1 j (Finset.mem_filter.1 hj).2
      · rw [dotProduct_single, mul_one]
        exact hd2 i (Finset.mem_filter.1 hi).2
    | zero => simp
    | add a b _ _ ha hb => rw [dotProduct_add, ha, hb, add_zero]
    | smul c a _ ha => rw [dotProduct_smul, ha, smul_zero]
  funext i
  have := hker (Pi.single i 1) (htop ▸ Submodule.mem_top)
  rw [dotProduct_single, mul_one] at this
  exact this

theorem c1_pos {A : Matrix (Fin m) (Fin n) ℝ} {x : Fin m → ℝ} (hx : 0 ≤ x)
    (hC1 : ConditionOnePrime A x) : ∀ i, 0 < x i := by
  intro i₀
  have hx0 : 0 ≤ x i₀ := hx i₀
  rcases hx0.lt_or_eq with h | h
  · exact h
  exfalso
  have hd := c1_zero hC1 (y := 0) (le_refl _) (Pi.single i₀ 1)
    (fun j hj => absurd hj (lt_irrefl _)) (fun i hi => ?_) (by simpa using hx)
  · have := congrFun hd i₀; simp at this
  · simp only [mulVec_zero, Pi.zero_apply] at hi
    have : i ≠ i₀ := by rintro rfl; linarith
    simp [Pi.single_apply, this]

end RLPSol

open MeasureTheory Matrix Filter Topology

namespace RLPSol
open RLPBidPrice.Unbiased

variable {m n : ℕ}

theorem opt_box' {A : Matrix (Fin m) (Fin n) ℝ} {r : Fin n → ℝ}
    (hA : IsIncidence A) (hr : 0 ≤ r) {x : Fin m → ℝ} (hx : 0 ≤ x)
    {y₀ : Fin n → ℝ} (hy₀ : 0 ≤ y₀) :
    ∃ μ, IsDualOpt A r x y₀ μ ∧ μ ∈ Set.Icc (0 : Fin m → ℝ) (fun _ => ⨆ j, r j) := by
  have hR : 0 ≤ ⨆ j, r j := rbar_nonneg r hr
  obtain ⟨μ, hμ⟩ := (strong_duality_subgradient A r hA hr x hx y₀ hy₀).1
  refine ⟨fun i => min (μ i) (⨆ j, r j), ⟨fun i => le_min (hμ.1 i) hR,
    fun μ' hμ' => (lagr_trunc hA hr hx hy₀ hμ.1).trans (hμ.2 μ' hμ')⟩,
    fun i => le_min (hμ.1 i) hR, fun i => min_le_right _ _⟩

theorem supergrad' {A : Matrix (Fin m) (Fin n) ℝ} {r : Fin n → ℝ}
    (hA : IsIncidence A) (hr : 0 ≤ r) {x : Fin m → ℝ} (hx : 0 ≤ x)
    {y₀ : Fin n → ℝ} (hy₀ : 0 ≤ y₀) {μ : Fin m → ℝ} (hμ : IsDualOpt A r x y₀ μ)
    {z : Fin m → ℝ} (hz : 0 ≤ z) :
    piValue A r z y₀ ≤ piValue A r x y₀ + μ ⬝ᵥ (z - x) :=
  ((strong_duality_subgradient A r hA hr x hx y₀ hy₀).2.1 μ hμ).2 z hz

/-- `v(·, y₀)` is Lipschitz on the nonnegative orthant -/
theorem pv_lip_x {A : Matrix (Fin m) (Fin n) ℝ} {r : Fin n → ℝ}
    (hA : IsIncidence A) (hr : 0 ≤ r) {y₀ : Fin n → ℝ} (hy₀ : 0 ≤ y₀)
    {a b : Fin m → ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |piValue A r a y₀ - piValue A r b y₀| ≤ m * (⨆ j, r j) * ‖a - b‖ := by
  have hR : 0 ≤ ⨆ j, r j := rbar_nonneg r hr
  obtain ⟨μa, hμa, hBa⟩ := opt_box' hA hr ha hy₀
  obtain ⟨μb, hμb, hBb⟩ := opt_box' hA hr hb hy₀
  have s1 := supergrad' hA hr ha hy₀ hμa hb
  have s2 := supergrad' hA hr hb hy₀ hμb ha
  have d1 := dot_le μa (b - a)
  have d2 := dot_le μb (a - b)
  have n1 := norm_le_of_box hR hBa
  have n2 := norm_le_of_box hR hBb
  rw [norm_sub_rev b a] at d1
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have c1 : (m : ℝ) * (‖μa‖ * ‖a - b‖) ≤ m * (⨆ j, r j) * ‖a - b‖ := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right n1 (norm_nonneg _)) hm0
  have c2 : (m : ℝ) * (‖μb‖ * ‖a - b‖) ≤ m * (⨆ j, r j) * ‖a - b‖ := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right n2 (norm_nonneg _)) hm0
  rw [abs_le]
  constructor
  · linarith [le_abs_self (μa ⬝ᵥ (b - a))]
  · linarith [le_abs_self (μb ⬝ᵥ (a - b))]

/-- `v(x, ·)` is Lipschitz in the demand -/
theorem pv_lip_y {A : Matrix (Fin m) (Fin n) ℝ} {r : Fin n → ℝ}
    (hA : IsIncidence A) (hr : 0 ≤ r) {x : Fin m → ℝ} (hx : 0 ≤ x)
    {a b : Fin n → ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    piValue A r x a ≤ piValue A r x b + ∑ j, r j * |a j - b j| := by
  apply pv_le hx ha
  intro y h1 h2 h3
  set y' : Fin n → ℝ := fun j => min (y j) (b j)
  have hy'0 : 0 ≤ y' := fun j => le_min (h2 j) (hb j)
  have hy'b : y' ≤ b := fun j => min_le_right _ _
  have hy'y : y' ≤ y := fun j => min_le_left _ _
  have hfe : A *ᵥ y' ≤ x := fun k => by
    refine le_trans ?_ (h1 k)
    simp only [mulVec, dotProduct]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hy'y j) (incid01 hA k j).1
  have hle := le_pv hr hfe hy'0 hy'b
  have : r ⬝ᵥ y ≤ r ⬝ᵥ y' + ∑ j, r j * |a j - b j| := by
    simp only [dotProduct, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have hyj : y j ≤ min (y j) (b j) + |a j - b j| := by
      rcases le_total (y j) (b j) with h | h
      · rw [min_eq_left h]; linarith [abs_nonneg (a j - b j)]
      · rw [min_eq_right h]; have := h3 j; linarith [le_abs_self (a j - b j)]
    have hrj : 0 ≤ r j := hr j
    calc r j * y j ≤ r j * (min (y j) (b j) + |a j - b j|) := mul_le_mul_of_nonneg_left hyj hrj
      _ = r j * y' j + r j * |a j - b j| := by ring
  linarith

theorem pv_cont_y {A : Matrix (Fin m) (Fin n) ℝ} {r : Fin n → ℝ}
    (hA : IsIncidence A) (hr : 0 ≤ r) {x : Fin m → ℝ} (hx : 0 ≤ x) :
    Continuous fun y : Fin n → ℝ => piValue A r x (fun j => max (y j) 0) := by
  have hS : 0 ≤ ∑ j, r j := Finset.sum_nonneg fun j _ => hr j
  apply LipschitzWith.continuous (K := (∑ j, r j).toNNReal)
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have hpa : (0 : Fin n → ℝ) ≤ fun j => max (a j) 0 := fun j => le_max_right _ _
  have hpb : (0 : Fin n → ℝ) ≤ fun j => max (b j) 0 := fun j => le_max_right _ _
  have h1 := pv_lip_y hA hr hx hpa hpb
  have h2 := pv_lip_y hA hr hx hpb hpa
  have hb : ∀ u v : Fin n → ℝ, ∑ j, r j * |max (u j) 0 - max (v j) 0| ≤ (∑ j, r j) * dist u v := by
    intro u v
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (hr j)
    calc |max (u j) 0 - max (v j) 0| ≤ |u j - v j| := abs_max_sub_max_le_abs _ _ _
      _ = dist (u j) (v j) := (Real.dist_eq _ _).symm
      _ ≤ dist u v := dist_le_pi_dist u v j
  have hb1 := hb a b
  have hb2 := hb b a
  rw [dist_comm b a] at hb2
  have e : ∑ j, r j * |max (b j) 0 - max (a j) 0| = ∑ j, r j * |max (a j) 0 - max (b j) 0| :=
    Finset.sum_congr rfl fun j _ => by rw [abs_sub_comm]
  rw [e] at h2
  rw [Real.dist_eq, abs_le, Real.coe_toNNReal _ hS]
  constructor <;> linarith

theorem aesm_pv {A : Matrix (Fin m) (Fin n) ℝ} {r : Fin n → ℝ}
    (hA : IsIncidence A) (hr : 0 ≤ r) {x : Fin m → ℝ} (hx : 0 ≤ x)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Ω → Fin n → ℝ) (hYm : Measurable Y) (hY0 : ∀ᵐ ω ∂P, 0 ≤ Y ω) :
    AEStronglyMeasurable (fun ω => piValue A r x (Y ω)) P := by
  refine ((pv_cont_y hA hr hx).measurable.comp hYm).aestronglyMeasurable.congr ?_
  filter_upwards [hY0] with ω hω
  have : (fun j => max (Y ω j) 0) = Y ω := funext fun j => max_eq_left (hω j)
  simp only [Function.comp_apply, this]

theorem pv_bound {A : Matrix (Fin m) (Fin n) ℝ} {r : Fin n → ℝ}
    (hA : IsIncidence A) (hr : 0 ≤ r) {x : Fin m → ℝ} (hx : 0 ≤ x)
    {y₀ : Fin n → ℝ} (hy₀ : 0 ≤ y₀) :
    0 ≤ piValue A r x y₀ ∧ piValue A r x y₀ ≤ (⨆ j, r j) * ∑ i, x i := by
  have hR : 0 ≤ ⨆ j, r j := rbar_nonneg r hr
  refine ⟨?_, ?_⟩
  · have := le_pv (A := A) hr (x := x) (y₀ := y₀) (y := 0) (by simpa using hx) (le_refl _) hy₀
    simpa using this
  · have h := pv_le_lagr (A := A) (r := r) hx hy₀ (μ := fun _ => ⨆ j, r j) (fun _ => hR)
    refine h.trans (le_of_eq ?_)
    unfold lagr
    have : ∀ j, max 0 (r j - ∑ i, (⨆ j, r j) * A i j) = 0 := by
      intro j
      obtain ⟨i, hi⟩ := hA.2 j
      have hi1 : A i j = 1 := (hA.1 i j).resolve_left hi
      have : (⨆ j, r j) * A i j ≤ ∑ k, (⨆ j, r j) * A k j :=
        Finset.single_le_sum (f := fun k => (⨆ j, r j) * A k j)
          (fun k _ => mul_nonneg hR (incid01 hA k j).1) (Finset.mem_univ i)
      rw [hi1, mul_one] at this
      exact max_eq_left (by linarith [le_rbar r j])
    simp only [this, mul_zero, Finset.sum_const_zero, zero_add, dotProduct, Finset.mul_sum]

theorem fderiv_eq_grad' {A : Matrix (Fin m) (Fin n) ℝ} {r : Fin n → ℝ}
    (hA : IsIncidence A) (hr : 0 ≤ r) {x : Fin m → ℝ} (hx : ∀ i, 0 < x i)
    {y₀ : Fin n → ℝ} (hy₀ : 0 ≤ y₀) {μ : Fin m → ℝ} (hμ : IsDualOpt A r x y₀ μ)
    {D : (Fin m → ℝ) →L[ℝ] ℝ} (hD : HasFDerivAt (fun x' => piValue A r x' y₀) D x) :
    D = gradCLM μ := by
  have hloc : IsLocalMax (fun x' => piValue A r x' y₀ - gradCLM μ x') x := by
    filter_upwards [eventually_pos hx] with x' hx'
    have := supergrad' hA hr (fun i => (hx i).le) hy₀ hμ (fun i => (hx' i).le)
    simp only [gradCLM_apply', dotProduct_sub] at *
    linarith
  have := hloc.hasFDerivAt_eq_zero (hD.sub (gradCLM μ).hasFDerivAt)
  exact sub_eq_zero.1 this

end RLPSol

open MeasureTheory Matrix Filter Topology

namespace RLPSol
open RLPBidPrice.Unbiased

variable {m n : ℕ}

theorem clm_decomp (T : (Fin m → ℝ) →L[ℝ] ℝ) :
    T = ∑ i, T (Pi.single i 1) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i := by
  refine ContinuousLinearMap.ext fun h => ?_
  have hh : h = ∑ i, h i • (Pi.single i 1 : Fin m → ℝ) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  calc T h = T (∑ i, h i • (Pi.single i 1 : Fin m → ℝ)) := by rw [← hh]
    _ = ∑ i, h i * T (Pi.single i 1) := by simp [map_sum, map_smul]
    _ = _ := by simp [ContinuousLinearMap.sum_apply, mul_comm]

theorem aesm_fderiv {A : Matrix (Fin m) (Fin n) ℝ} {r : Fin n → ℝ}
    (hA : IsIncidence A) (hr : 0 ≤ r) {x : Fin m → ℝ} (hx : ∀ i, 0 < x i)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Ω → Fin n → ℝ) (hYm : Measurable Y) (hY0 : ∀ᵐ ω ∂P, 0 ≤ Y ω)
    (hdiff : ∀ᵐ ω ∂P, DifferentiableAt ℝ (fun x' => piValue A r x' (Y ω)) x) :
    AEStronglyMeasurable (fun ω => fderiv ℝ (fun x' => piValue A r x' (Y ω)) x) P := by
  have hx0 : 0 ≤ x := fun i => (hx i).le
  set u : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hu
  have hu0 : ∀ k, 0 < u k := fun k => by positivity
  have hut : Tendsto u atTop (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall fun k => (hu0 k).ne'⟩
  set e : Fin m → (Fin m → ℝ) := fun i => Pi.single i 1 with he
  set G : ℕ → Ω → ((Fin m → ℝ) →L[ℝ] ℝ) := fun k ω => ∑ i,
    ((u k)⁻¹ * (piValue A r (x + u k • e i) (Y ω) - piValue A r x (Y ω))) •
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i with hG
  refine aestronglyMeasurable_of_tendsto_ae atTop (f := G) (fun k => ?_) ?_
  · have hnn : ∀ i, 0 ≤ x + u k • e i := fun i j => by
      simp only [e, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, Pi.zero_apply]
      have := hx j; have := hu0 k
      split_ifs <;> nlinarith
    exact Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      (((aesm_pv hA hr (hnn i) P Y hYm hY0).sub (aesm_pv hA hr hx0 P Y hYm hY0)).const_mul _).smul_const _
  · filter_upwards [hdiff] with ω hω
    set f := fun x' => piValue A r x' (Y ω) with hf
    set T := fderiv ℝ f x with hT
    rw [clm_decomp T]
    refine tendsto_finset_sum _ fun i _ => Tendsto.smul_const ?_ _
    have hl : HasDerivAt (fun t : ℝ => x + t • e i) (e i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (e i)).const_add x
    have hline : HasDerivAt (fun t : ℝ => f (x + t • e i)) (T (e i)) 0 :=
      HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hω.hasFDerivAt hl (by simp)
    have := (hasDerivAt_iff_tendsto_slope.mp hline).comp hut
    refine this.congr fun k => ?_
    simp only [Function.comp_apply, slope, vsub_eq_sub, sub_zero, zero_smul, add_zero,
      smul_eq_mul, f]

theorem theorem1 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)
    (hA : IsIncidence A) (hr : 0 ≤ r) (x : Fin m → ℝ) (hx : 0 ≤ x)
    (hC1 : ConditionOnePrime A x)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → Fin n → ℝ) (hYm : Measurable Y) (hY0 : ∀ᵐ ω ∂P, 0 ≤ Y ω)
    (hC2 : ConditionTwo P Y) (hind : ProbabilityTheory.iIndepFun (fun j ω => Y ω j) P) :
    (∀ᵐ ω ∂P, DifferentiableAt ℝ (fun x' => piValue A r x' (Y ω)) x) ∧
    HasFDerivAt (JPI P A r Y) (∫ ω, fderiv ℝ (fun x' => piValue A r x' (Y ω)) x ∂P) x ∧
    (∀ μ : Ω → Fin m → ℝ, AEStronglyMeasurable μ P →
      (∀ᵐ ω ∂P, IsDualOpt A r x (Y ω) (μ ω)) →
      HasFDerivAt (JPI P A r Y) (gradCLM (fun i => ∫ ω, μ ω i ∂P)) x) := by
  have hxpos : ∀ i, 0 < x i := c1_pos hx hC1
  have hR : 0 ≤ ⨆ j, r j := rbar_nonneg r hr
  have hdiff := lemma4_ae_gradient_exists A r hA hr x hx hC1 P Y hYm hY0 hC2 hind
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (eventually_pos hxpos)
  have hF_meas : ∀ᶠ x' in 𝓝 x, AEStronglyMeasurable (fun ω => piValue A r x' (Y ω)) P := by
    filter_upwards [eventually_pos hxpos] with x' hx'
    exact aesm_pv hA hr (fun i => (hx' i).le) P Y hYm hY0
  have hF_int : Integrable (fun ω => piValue A r x (Y ω)) P := by
    refine Integrable.of_bound (aesm_pv hA hr hx P Y hYm hY0) ((⨆ j, r j) * ∑ i, x i) ?_
    filter_upwards [hY0] with ω hω
    obtain ⟨h1, h2⟩ := pv_bound hA hr hx hω
    rw [Real.norm_eq_abs, abs_of_nonneg h1]; exact h2
  have hF'_meas := aesm_fderiv hA hr hxpos P Y hYm hY0 hdiff
  have h_lip : ∀ᵐ ω ∂P, LipschitzOnWith (Real.nnabs ((m : ℝ) * ⨆ j, r j))
      (fun x' => piValue A r x' (Y ω)) (Metric.ball x ε) := by
    filter_upwards [hY0] with ω hω
    apply LipschitzOnWith.of_dist_le_mul
    intro a ha b hb
    have ha' : 0 ≤ a := fun i => (hball ha i).le
    have hb' : 0 ≤ b := fun i => (hball hb i).le
    rw [Real.dist_eq, dist_eq_norm]
    have : ((Real.nnabs ((m : ℝ) * ⨆ j, r j) : NNReal) : ℝ) = m * ⨆ j, r j := by
      rw [Real.coe_nnabs, abs_of_nonneg (by positivity)]
    rw [this]
    exact pv_lip_x hA hr hω ha' hb'
  have h_diff' : ∀ᵐ ω ∂P, HasFDerivAt (fun x' => piValue A r x' (Y ω))
      (fderiv ℝ (fun x' => piValue A r x' (Y ω)) x) x :=
    hdiff.mono fun ω h => h.hasFDerivAt
  have key := hasFDerivAt_integral_of_dominated_loc_of_lip (μ := P)
    (F := fun x' ω => piValue A r x' (Y ω)) (x₀ := x)
    (bound := fun _ => (m : ℝ) * ⨆ j, r j) (Metric.ball_mem_nhds x hε) hF_meas hF_int hF'_meas
    h_lip (integrable_const _) h_diff'
  have hJ : JPI P A r Y = fun x' => ∫ ω, piValue A r x' (Y ω) ∂P := rfl
  refine ⟨hdiff, by rw [hJ]; exact key.2, fun μ _ hμopt => ?_⟩
  have hae : (fun ω => fderiv ℝ (fun x' => piValue A r x' (Y ω)) x) =ᵐ[P]
      fun ω => gradCLM (μ ω) := by
    filter_upwards [hdiff, hμopt, hY0] with ω h1 h2 h3
    exact fderiv_eq_grad' hA hr hxpos h3 h2 h1.hasFDerivAt
  have hμi : ∀ i, Integrable (fun ω => μ ω i) P := by
    intro i
    have := (ContinuousLinearMap.apply ℝ ℝ (Pi.single i (1 : ℝ) : Fin m → ℝ)).integrable_comp key.1
    refine this.congr ?_
    filter_upwards [hae] with ω hω
    simp only [ContinuousLinearMap.apply_apply]
    rw [hω, gradCLM_apply', dotProduct_single, mul_one]
  have hint_eq : ∫ ω, fderiv ℝ (fun x' => piValue A r x' (Y ω)) x ∂P =
      gradCLM (fun i => ∫ ω, μ ω i ∂P) := by
    rw [integral_congr_ae hae]
    simp only [gradCLM]
    rw [integral_finsetSum _ fun i _ => (hμi i).smul_const _]
    exact Finset.sum_congr rfl fun i _ => integral_smul_const _ _
  rw [hJ, ← hint_eq]
  exact key.2

end RLPSol

open MeasureTheory Matrix RLPBidPrice.Unbiased in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)
    (hA : IsIncidence A) (hr : 0 ≤ r) (x : Fin m → ℝ) (hx : 0 ≤ x)
    (hC1 : ConditionOnePrime A x)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → Fin n → ℝ) (hYm : Measurable Y) (hY0 : ∀ᵐ ω ∂P, 0 ≤ Y ω)
    (hC2 : ConditionTwo P Y) (hind : ProbabilityTheory.iIndepFun (fun j ω => Y ω j) P) :
    (∀ᵐ ω ∂P, DifferentiableAt ℝ (fun x' => piValue A r x' (Y ω)) x) ∧
    HasFDerivAt (JPI P A r Y) (∫ ω, fderiv ℝ (fun x' => piValue A r x' (Y ω)) x ∂P) x ∧
    (∀ μ : Ω → Fin m → ℝ, AEStronglyMeasurable μ P →
      (∀ᵐ ω ∂P, IsDualOpt A r x (Y ω) (μ ω)) →
      HasFDerivAt (JPI P A r Y) (gradCLM (fun i => ∫ ω, μ ω i ∂P)) x) :=
  RLPSol.theorem1 A r hA hr x hx hC1 P Y hYm hY0 hC2 hind
