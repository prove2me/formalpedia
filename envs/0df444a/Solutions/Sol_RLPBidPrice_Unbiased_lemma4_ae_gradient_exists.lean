-- Prove2me | solution 1 for RLPBidPrice.Unbiased.lemma4_ae_gradient_exists
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T09:47:06.332381+00:00
-- url     : https://prove2.me/submissions/dc052515-f156-4222-9e05-9890c9eec1e0

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

open MeasureTheory Matrix Filter Topology

namespace RLPSol
open RLPBidPrice.Unbiased

variable {m n : ℕ}

theorem lagr_sub (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ) (x z : Fin m → ℝ)
    (y₀ : Fin n → ℝ) (μ : Fin m → ℝ) :
    lagr A r z y₀ μ = lagr A r x y₀ μ + μ ⬝ᵥ (z - x) := by
  simp only [lagr, dotProduct_sub]; ring

theorem lagr_continuous (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ) (x : Fin m → ℝ)
    (y₀ : Fin n → ℝ) : Continuous (fun μ => lagr A r x y₀ μ) := by
  unfold lagr
  refine Continuous.add (continuous_finsetSum _ fun j _ => ?_) (continuous_id.dotProduct continuous_const)
  refine continuous_const.mul (continuous_const.max (continuous_const.sub
    (continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const)))

theorem incid01 {A : Matrix (Fin m) (Fin n) ℝ} (hA : IsIncidence A) (k : Fin m) (j : Fin n) :
    0 ≤ A k j ∧ A k j ≤ 1 := by
  rcases hA.1 k j with h | h <;> rw [h] <;> norm_num

/-- truncating dual prices at `r̄` does not increase the Lagrangian -/
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

/-- an optimal dual price vector exists, and can be chosen in the box `[0, r̄]` -/
theorem exists_dualOpt_box {A : Matrix (Fin m) (Fin n) ℝ} {r : Fin n → ℝ}
    (hA : IsIncidence A) (hr : 0 ≤ r) {x : Fin m → ℝ} (hx : 0 ≤ x)
    {y₀ : Fin n → ℝ} (hy₀ : 0 ≤ y₀) :
    ∃ μ, IsDualOpt A r x y₀ μ ∧ μ ∈ Set.Icc (0 : Fin m → ℝ) (fun _ => ⨆ j, r j) := by
  have hR : 0 ≤ ⨆ j, r j := rbar_nonneg r hr
  obtain ⟨μ, hμ, hmin⟩ := (isCompact_Icc (a := (0 : Fin m → ℝ)) (b := fun _ => ⨆ j, r j)).exists_isMinOn
    ⟨0, le_refl _, fun _ => hR⟩ (lagr_continuous A r x y₀).continuousOn
  refine ⟨μ, ⟨hμ.1, fun μ' hμ' => ?_⟩, hμ⟩
  have h1 : (fun i => min (μ' i) (⨆ j, r j)) ∈ Set.Icc (0 : Fin m → ℝ) (fun _ => ⨆ j, r j) :=
    ⟨fun i => le_min (hμ' i) hR, fun i => min_le_right _ _⟩
  exact (hmin h1).trans (lagr_trunc hA hr hx hy₀ hμ')


/-- the linear functional on `ℝᵐ × ℝ` in coordinates -/
theorem functional_coords (f : StrongDual ℝ ((Fin m → ℝ) × ℝ)) (z : Fin m → ℝ) (w : ℝ) :
    f (z, w) = ∑ i, z i * f ((Pi.single i 1 : Fin m → ℝ), (0 : ℝ)) + w * f (0, 1) := by
  have : ((z, w) : (Fin m → ℝ) × ℝ) =
      ∑ i, z i • (((Pi.single i 1 : Fin m → ℝ), (0 : ℝ)) : (Fin m → ℝ) × ℝ) +
        w • (((0 : Fin m → ℝ), (1 : ℝ)) : (Fin m → ℝ) × ℝ) := by
    ext k
    · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [Prod.snd_sum]
  rw [this, map_add, map_sum, map_smul]
  simp only [map_smul, smul_eq_mul]

/-- LP strong duality under Slater's condition `x > 0`. -/
theorem strong_duality_pos {A : Matrix (Fin m) (Fin n) ℝ} {r : Fin n → ℝ}
    (hr : 0 ≤ r) {x : Fin m → ℝ} (hx : ∀ i, 0 < x i)
    {y₀ : Fin n → ℝ} (hy₀ : 0 ≤ y₀) :
    ∃ μ, 0 ≤ μ ∧ lagr A r x y₀ μ ≤ piValue A r x y₀ := by
  have hx0 : 0 ≤ x := fun i => (hx i).le
  set v := piValue A r x y₀ with hv
  set K : Set ((Fin m → ℝ) × ℝ) :=
    {p | ∃ y, 0 ≤ y ∧ y ≤ y₀ ∧ A *ᵥ y ≤ p.1 ∧ p.2 ≤ r ⬝ᵥ y} with hK
  set U : Set ((Fin m → ℝ) × ℝ) := (Set.univ.pi fun i => Set.Iio (x i)) ×ˢ Set.Ioi v with hU
  have hUo : IsOpen U := (isOpen_set_pi Set.finite_univ fun i _ => isOpen_Iio).prod isOpen_Ioi
  have hUc : Convex ℝ U := (convex_pi fun i _ => convex_Iio _).prod (convex_Ioi _)
  have hKc : Convex ℝ K := by
    rintro ⟨z, w⟩ ⟨y, hy0, hyy, hAy, hw⟩ ⟨z', w'⟩ ⟨y', hy0', hyy', hAy', hw'⟩ a b ha hb hab
    refine ⟨a • y + b • y', ?_, ?_, ?_, ?_⟩
    · exact add_nonneg (smul_nonneg ha hy0) (smul_nonneg hb hy0')
    · calc a • y + b • y' ≤ a • y₀ + b • y₀ :=
            add_le_add (smul_le_smul_of_nonneg_left hyy ha) (smul_le_smul_of_nonneg_left hyy' hb)
        _ = y₀ := by rw [← add_smul, hab, one_smul]
    · simp only [Prod.fst_add, Prod.smul_fst, mulVec_add, mulVec_smul]
      exact add_le_add (smul_le_smul_of_nonneg_left hAy ha) (smul_le_smul_of_nonneg_left hAy' hb)
    · simp only [Prod.snd_add, Prod.smul_snd, dotProduct_add, dotProduct_smul, smul_eq_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hw ha) (mul_le_mul_of_nonneg_left hw' hb)
  have hdisj : Disjoint U K := by
    rw [Set.disjoint_left]
    rintro ⟨z, w⟩ ⟨hz, hw⟩ ⟨y, hy0, hyy, hAy, hwy⟩
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Iio, forall_const] at hz
    simp only [Set.mem_Ioi] at hw
    have hfe : A *ᵥ y ≤ x := fun i => (hAy i).trans (hz i).le
    have := le_pv hr hfe hy0 hyy
    simp only at hwy
    linarith
  obtain ⟨f, u, hfU, hfK⟩ := geometric_hahn_banach_open hUc hUo hKc hdisj
  set a : Fin m → ℝ := fun i => f ((Pi.single i 1 : Fin m → ℝ), (0 : ℝ)) with ha
  set c : ℝ := f (0, 1) with hc
  have hf : ∀ z w, f (z, w) = ∑ i, z i * a i + w * c := functional_coords f
  -- (0,0) ∈ K
  have hu0 : u ≤ 0 := by
    have := hfK (0, 0) ⟨0, le_refl _, hy₀, by simp, by simp⟩
    simpa [hf] using this
  -- a ≥ 0
  have ha0 : ∀ i, 0 ≤ a i := by
    intro i
    by_contra hneg
    push Not at hneg
    set t := (1 - u) / (-a i)
    have ht : 0 ≤ t := div_nonneg (by linarith) (by linarith)
    have hmem : ((t • (Pi.single i 1 : Fin m → ℝ)), (0 : ℝ)) ∈ K := by
      refine ⟨0, le_refl _, hy₀, ?_, by simp⟩
      intro k; simp only [mulVec_zero, Pi.zero_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      split_ifs <;> simp [ht]
    have h1 := hfK _ hmem
    rw [hf] at h1
    have : ∑ k, (t • (Pi.single i 1 : Fin m → ℝ)) k * a k = t * a i := by
      simp [Pi.single_apply]
    rw [this] at h1
    have hai : a i ≠ 0 := hneg.ne
    have : t * a i = u - 1 := by
      simp only [t]; field_simp; ring
    linarith
  -- c ≤ 0
  have hc0 : c ≤ 0 := by
    by_contra hpos
    push Not at hpos
    set t := (1 - u) / c
    have ht : 0 ≤ t := div_nonneg (by linarith) hpos.le
    have hmem : ((0 : Fin m → ℝ), -t) ∈ K := ⟨0, le_refl _, hy₀, by simp, by simp [ht]⟩
    have h1 := hfK _ hmem
    rw [hf] at h1
    have : -t * c = u - 1 := by simp only [t]; field_simp; ring
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add] at h1
    linarith
  -- the point (x, v) is in the closure of U
  set S := ∑ i, x i * a i
  have hSu : S + v * c ≤ u := by
    by_contra hgt
    push Not at hgt
    set g := S + v * c - u
    set M := |c| + ∑ i, |a i| + 1
    have hM : 0 < M := by positivity
    set δ := g / (2 * M)
    have hδ : 0 < δ := by positivity
    have hmem : ((fun i => x i - δ), v + δ) ∈ U := by
      refine ⟨?_, ?_⟩
      · simp only [Set.mem_pi, Set.mem_univ, Set.mem_Iio, forall_const]; intro i; linarith
      · simp only [Set.mem_Ioi]; linarith
    have h1 := hfU _ hmem
    rw [hf] at h1
    have hexp : ∑ i, (x i - δ) * a i + (v + δ) * c = S + v * c + δ * (c - ∑ i, a i) := by
      simp only [S, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]; ring
    rw [hexp] at h1
    have hb : |c - ∑ i, a i| ≤ M := by
      calc |c - ∑ i, a i| ≤ |c| + |∑ i, a i| := abs_sub _ _
        _ ≤ |c| + ∑ i, |a i| := by gcongr; exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ M := by simp only [M]; linarith
    have : -(δ * M) ≤ δ * (c - ∑ i, a i) := by
      have := neg_abs_le (c - ∑ i, a i)
      nlinarith
    have : δ * M = g / 2 := by simp only [δ]; field_simp
    linarith
  -- c ≠ 0 (Slater)
  have hcneg : c < 0 := by
    rcases hc0.lt_or_eq with h | h
    · exact h
    exfalso
    have hS : S ≤ 0 := by rw [h] at hSu; linarith
    have hS0 : ∀ i, x i * a i = 0 := by
      have hnn : ∀ i ∈ Finset.univ, 0 ≤ x i * a i := fun i _ => mul_nonneg (hx0 i) (ha0 i)
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (le_antisymm hS (Finset.sum_nonneg hnn))
      exact fun i => this i (Finset.mem_univ i)
    have ha' : ∀ i, a i = 0 := fun i => by
      rcases mul_eq_zero.1 (hS0 i) with h' | h'
      · exact absurd h' (hx i).ne'
      · exact h'
    have hmem : ((fun i => x i - 1), v + 1) ∈ U := by
      refine ⟨?_, ?_⟩
      · simp only [Set.mem_pi, Set.mem_univ, Set.mem_Iio, forall_const]; intro i; linarith
      · simp only [Set.mem_Ioi]; linarith
    have h1 := hfU _ hmem
    rw [hf] at h1
    simp only [ha', h, mul_zero, Finset.sum_const_zero, add_zero] at h1
    linarith
  -- dual prices
  set μ : Fin m → ℝ := fun i => a i / (-c) with hμ
  have hμ0 : 0 ≤ μ := fun i => div_nonneg (ha0 i) (by linarith)
  refine ⟨μ, hμ0, ?_⟩
  -- choose the primal vector that takes the full demand on positive reduced cost
  set rc : Fin n → ℝ := fun j => r j - ∑ i, μ i * A i j
  set y : Fin n → ℝ := fun j => if 0 < rc j then y₀ j else 0
  have hy0 : 0 ≤ y := fun j => by
    simp only [y]; split_ifs
    exacts [hy₀ j, le_refl 0]
  have hyy : y ≤ y₀ := fun j => by
    simp only [y]; split_ifs
    exacts [le_refl _, hy₀ j]
  have hmem : (A *ᵥ y, r ⬝ᵥ y) ∈ K := ⟨y, hy0, hyy, le_refl _, le_refl _⟩
  have h1 := hfK _ hmem
  rw [hf] at h1
  have hcne : c ≠ 0 := hcneg.ne
  have haμ : ∀ i, a i = -c * μ i := fun i => by simp only [μ]; field_simp
  have e1 : S = -c * (μ ⬝ᵥ x) := by
    simp only [S, dotProduct, Finset.mul_sum, haμ]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, (A *ᵥ y) i * a i = -c * (μ ⬝ᵥ (A *ᵥ y)) := by
    simp only [dotProduct, Finset.mul_sum, haμ]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsplit := obj_split A r μ y
  have hyrc : ∑ j, y j * (r j - ∑ i, μ i * A i j) = ∑ j, y₀ j * max 0 (r j - ∑ i, μ i * A i j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [y, rc]
    split_ifs with hpos
    · rw [max_eq_right hpos.le]
    · rw [max_eq_left (not_lt.1 hpos)]; simp
  rw [e1] at hSu
  rw [e2] at h1
  have hP : (-c) * (μ ⬝ᵥ x - v) ≤ (-c) * (μ ⬝ᵥ (A *ᵥ y) - r ⬝ᵥ y) := by nlinarith
  have hP' := le_of_mul_le_mul_left hP (by linarith)
  show ∑ j, y₀ j * max 0 (r j - ∑ i, μ i * A i j) + μ ⬝ᵥ x ≤ v
  linarith


theorem pv_shift_finset {A : Matrix (Fin m) (Fin n) ℝ} {r : Fin n → ℝ}
    (hA : IsIncidence A) (hr : 0 ≤ r) {x : Fin m → ℝ} (hx : 0 ≤ x)
    {y₀ : Fin n → ℝ} (hy₀ : 0 ≤ y₀) {ε : ℝ} (hε : 0 ≤ ε) (S : Finset (Fin m)) :
    piValue A r (x + ε • ∑ i ∈ S, (Pi.single i 1 : Fin m → ℝ)) y₀ ≤
      piValue A r x y₀ + S.card * ε * ⨆ j, r j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    have hnn : 0 ≤ x + ε • ∑ i ∈ S, (Pi.single i 1 : Fin m → ℝ) := by
      intro k
      simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, Pi.single_apply, smul_eq_mul,
        Pi.zero_apply]
      have : 0 ≤ x k := hx k
      have : (0:ℝ) ≤ ∑ c ∈ S, if k = c then 1 else 0 :=
        Finset.sum_nonneg fun c _ => by split_ifs <;> norm_num
      positivity
    have h := lemma2_upper hA hr hnn hy₀ a hε
    have heq : x + ε • ∑ i ∈ insert a S, (Pi.single i 1 : Fin m → ℝ) =
        x + ε • ∑ i ∈ S, (Pi.single i 1 : Fin m → ℝ) + ε • Pi.single a 1 := by
      rw [Finset.sum_insert ha, smul_add]; abel
    rw [heq, Finset.card_insert_of_notMem ha]
    push_cast
    linarith

theorem pv_shift_univ {A : Matrix (Fin m) (Fin n) ℝ} {r : Fin n → ℝ}
    (hA : IsIncidence A) (hr : 0 ≤ r) {x : Fin m → ℝ} (hx : 0 ≤ x)
    {y₀ : Fin n → ℝ} (hy₀ : 0 ≤ y₀) {ε : ℝ} (hε : 0 ≤ ε) :
    piValue A r (fun i => x i + ε) y₀ ≤ piValue A r x y₀ + m * ε * ⨆ j, r j := by
  have h := pv_shift_finset hA hr hx hy₀ hε Finset.univ
  have : (fun i => x i + ε) = x + ε • ∑ i, (Pi.single i 1 : Fin m → ℝ) := by
    ext k; simp [Finset.sum_apply, Pi.single_apply]
  rw [this]; simpa using h

/-- strong duality: the LP value equals the Lagrangian at any optimal dual price vector -/
theorem pv_eq_lagr {A : Matrix (Fin m) (Fin n) ℝ} {r : Fin n → ℝ}
    (hA : IsIncidence A) (hr : 0 ≤ r) {x : Fin m → ℝ} (hx : 0 ≤ x)
    {y₀ : Fin n → ℝ} (hy₀ : 0 ≤ y₀) {μ : Fin m → ℝ} (hμ : IsDualOpt A r x y₀ μ) :
    piValue A r x y₀ = lagr A r x y₀ μ := by
  refine le_antisymm (pv_le_lagr hx hy₀ hμ.1) ?_
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set R := ⨆ j, r j
  have hR : 0 ≤ R := rbar_nonneg r hr
  set ε := δ / (m * R + 1)
  have hε : 0 < ε := by positivity
  have hxε : ∀ i, 0 < x i + ε := fun i => by have := hx i; simp at this; linarith
  obtain ⟨ν, hν0, hν⟩ := strong_duality_pos (A := A) hr hxε hy₀
  have h1 : lagr A r x y₀ μ ≤ lagr A r x y₀ ν := hμ.2 ν hν0
  have h2 : lagr A r x y₀ ν ≤ lagr A r (fun i => x i + ε) y₀ ν := by
    rw [lagr_sub A r x (fun i => x i + ε) y₀ ν]
    have : 0 ≤ ν ⬝ᵥ ((fun i => x i + ε) - x) :=
      dotProduct_nonneg_of_nonneg hν0 (fun i => by simp [hε.le])
    linarith
  have h3 := pv_shift_univ hA hr hx hy₀ hε.le
  have h4 : m * ε * R ≤ δ := by
    have : m * ε * R = δ * (m * R) / (m * R + 1) := by simp only [ε]; field_simp
    rw [this, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-- every optimal dual price vector is a supergradient of `v(·, y₀)` on the orthant -/
theorem supergrad {A : Matrix (Fin m) (Fin n) ℝ} {r : Fin n → ℝ}
    (hA : IsIncidence A) (hr : 0 ≤ r) {x : Fin m → ℝ} (hx : 0 ≤ x)
    {y₀ : Fin n → ℝ} (hy₀ : 0 ≤ y₀) {μ : Fin m → ℝ} (hμ : IsDualOpt A r x y₀ μ)
    {z : Fin m → ℝ} (hz : 0 ≤ z) :
    piValue A r z y₀ ≤ piValue A r x y₀ + μ ⬝ᵥ (z - x) := by
  rw [pv_eq_lagr hA hr hx hy₀ hμ, ← lagr_sub]
  exact pv_le_lagr hz hy₀ hμ.1


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

/-- Fermat: at a point of differentiability, the derivative is the gradient of every optimal
dual price vector -/
theorem fderiv_eq_grad {A : Matrix (Fin m) (Fin n) ℝ} {r : Fin n → ℝ}
    (hA : IsIncidence A) (hr : 0 ≤ r) {x : Fin m → ℝ} (hx : ∀ i, 0 < x i)
    {y₀ : Fin n → ℝ} (hy₀ : 0 ≤ y₀) {μ : Fin m → ℝ} (hμ : IsDualOpt A r x y₀ μ)
    {D : (Fin m → ℝ) →L[ℝ] ℝ} (hD : HasFDerivAt (fun x' => piValue A r x' y₀) D x) :
    D = gradCLM μ := by
  have hloc : IsLocalMax (fun x' => piValue A r x' y₀ - gradCLM μ x') x := by
    filter_upwards [eventually_pos hx] with x' hx'
    have := supergrad hA hr (fun i => (hx i).le) hy₀ hμ (fun i => (hx' i).le)
    simp only [gradCLM_apply', dotProduct_sub] at *
    linarith
  have := hloc.hasFDerivAt_eq_zero (hD.sub (gradCLM μ).hasFDerivAt)
  exact sub_eq_zero.1 this

/-- uniqueness of the optimal dual price vector implies differentiability -/
theorem hasFDerivAt_of_unique {A : Matrix (Fin m) (Fin n) ℝ} {r : Fin n → ℝ}
    (hA : IsIncidence A) (hr : 0 ≤ r) {x : Fin m → ℝ} (hx : ∀ i, 0 < x i)
    {y₀ : Fin n → ℝ} (hy₀ : 0 ≤ y₀) {μ : Fin m → ℝ} (hμ : IsDualOpt A r x y₀ μ)
    (huniq : ∀ μ', IsDualOpt A r x y₀ μ' → μ' = μ) :
    HasFDerivAt (fun x' => piValue A r x' y₀) (gradCLM μ) x := by
  classical
  have hx0 : 0 ≤ x := fun i => (hx i).le
  have hR : 0 ≤ ⨆ j, r j := rbar_nonneg r hr
  set R := ⨆ j, r j
  set B := Set.Icc (0 : Fin m → ℝ) (fun _ => R) with hB
  have hsel : ∀ x' : Fin m → ℝ, ∃ ν, ν ∈ B ∧ (0 ≤ x' → IsDualOpt A r x' y₀ ν) := fun x' => by
    by_cases h : 0 ≤ x'
    · obtain ⟨ν, h1, h2⟩ := exists_dualOpt_box hA hr h hy₀; exact ⟨ν, h2, fun _ => h1⟩
    · exact ⟨0, ⟨le_refl _, fun _ => hR⟩, fun h' => absurd h' h⟩
  choose g hgB hg using hsel
  have hμB : μ ∈ B := by rw [← huniq _ (hg x hx0)]; exact hgB x
  set Lx := fun ν => lagr A r x y₀ ν
  -- continuity of the selection at `x`
  have hgt : ∀ ε > 0, ∀ᶠ x' in 𝓝 x, ‖g x' - μ‖ < ε := by
    intro ε hε
    set Kε := B ∩ {ν | ε ≤ ‖ν - μ‖}
    have hKc : IsCompact Kε := isCompact_Icc.inter_right
      (isClosed_le continuous_const ((continuous_id.sub continuous_const).norm))
    rcases Kε.eq_empty_or_nonempty with hemp | hne
    · refine Eventually.of_forall fun x' => ?_
      by_contra hcon
      push Not at hcon
      have : g x' ∈ Kε := ⟨hgB x', hcon⟩
      rw [hemp] at this; exact this
    obtain ⟨ν₀, hν₀K, hν₀min⟩ := hKc.exists_isMinOn hne (lagr_continuous A r x y₀).continuousOn
    have hgap : lagr A r x y₀ μ < lagr A r x y₀ ν₀ := by
      by_contra hcon
      push Not at hcon
      have hopt : IsDualOpt A r x y₀ ν₀ :=
        ⟨hν₀K.1.1, fun ν' hν' => hcon.trans (hμ.2 ν' hν')⟩
      have := huniq _ hopt
      have h2 : ε ≤ ‖ν₀ - μ‖ := hν₀K.2
      rw [this, sub_self, norm_zero] at h2
      linarith
    set γ := lagr A r x y₀ ν₀ - lagr A r x y₀ μ
    have hγ : 0 < γ := by simp only [γ]; linarith
    have hδ : 0 < γ / (2 * (m * R) + 1) := by positivity
    filter_upwards [Metric.ball_mem_nhds x hδ, eventually_pos hx] with x' hx'd hx'
    rw [Metric.mem_ball, dist_eq_norm] at hx'd
    have hx'0 : 0 ≤ x' := fun i => (hx' i).le
    by_contra hcon
    push Not at hcon
    have hK : g x' ∈ Kε := ⟨hgB x', hcon⟩
    have h1 : lagr A r x y₀ ν₀ ≤ lagr A r x y₀ (g x') := hν₀min hK
    have h2 : lagr A r x' y₀ (g x') ≤ lagr A r x' y₀ μ := (hg x' hx'0).2 μ hμ.1
    rw [lagr_sub A r x x' y₀ (g x'), lagr_sub A r x x' y₀ μ] at h2
    have b1 := dot_le (g x') (x' - x)
    have b2 := dot_le μ (x' - x)
    have n1 := norm_le_of_box hR (hgB x')
    have n2 := norm_le_of_box hR hμB
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have c1 : (m : ℝ) * (‖g x'‖ * ‖x' - x‖) ≤ m * (R * ‖x' - x‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right n1 (norm_nonneg _)) hm0
    have c2 : (m : ℝ) * (‖μ‖ * ‖x' - x‖) ≤ m * (R * ‖x' - x‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right n2 (norm_nonneg _)) hm0
    have c3 : (2 * (m * R) + 1) * ‖x' - x‖ < γ := by
      rwa [lt_div_iff₀ (by positivity), mul_comm] at hx'd
    have c4 : 2 * (m * (R * ‖x' - x‖)) ≤ (2 * (m * R) + 1) * ‖x' - x‖ := by
      nlinarith [norm_nonneg (x' - x)]
    have a1 := neg_abs_le (g x' ⬝ᵥ (x' - x))
    have a2 := le_abs_self (μ ⬝ᵥ (x' - x))
    simp only [γ] at c3
    linarith
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have hm1 : (0 : ℝ) < m + 1 := by positivity
  filter_upwards [hgt (c / (m + 1)) (by positivity), eventually_pos hx] with x' hg' hx'
  have hx'0 : 0 ≤ x' := fun i => (hx' i).le
  have s1 := supergrad hA hr hx0 hy₀ hμ hx'0
  have s2 := supergrad hA hr hx'0 hy₀ (hg x' hx'0) hx0
  rw [gradCLM_apply', Real.norm_eq_abs]
  have hb := dot_le (g x' - μ) (x' - x)
  have e1 : (g x' - μ) ⬝ᵥ (x' - x) = g x' ⬝ᵥ (x' - x) - μ ⬝ᵥ (x' - x) := sub_dotProduct _ _ _
  have e2 : g x' ⬝ᵥ (x - x') = -(g x' ⬝ᵥ (x' - x)) := by
    rw [← dotProduct_neg, neg_sub]
  have hc' : (m : ℝ) * (‖g x' - μ‖ * ‖x' - x‖) ≤ c * ‖x' - x‖ := by
    have : (m : ℝ) * ‖g x' - μ‖ ≤ c := by
      have h1 : (m : ℝ) * ‖g x' - μ‖ ≤ (m + 1) * ‖g x' - μ‖ := by nlinarith [norm_nonneg (g x' - μ)]
      have h2 : (m + 1) * ‖g x' - μ‖ < c := by rwa [lt_div_iff₀ hm1, mul_comm] at hg'
      linarith
    nlinarith [norm_nonneg (x' - x)]
  rw [abs_le]
  have a1 := abs_le.1 (hb.trans hc')
  constructor <;> linarith [a1.1, a1.2]

end RLPSol

open MeasureTheory Matrix Filter Topology

namespace RLPSol
open RLPBidPrice.Unbiased

variable {m n : ℕ}

/-- complementary slackness -/
theorem compl_slack {A : Matrix (Fin m) (Fin n) ℝ} {r : Fin n → ℝ}
    (hA : IsIncidence A) (hr : 0 ≤ r) {x : Fin m → ℝ} (hx : 0 ≤ x)
    {y₀ : Fin n → ℝ} (hy₀ : 0 ≤ y₀) {μ : Fin m → ℝ} (hμ : IsDualOpt A r x y₀ μ)
    {y : Fin n → ℝ} (h1 : A *ᵥ y ≤ x) (h2 : 0 ≤ y) (h3 : y ≤ y₀)
    (hopt : r ⬝ᵥ y = piValue A r x y₀) :
    (∀ j, 0 < y j → 0 ≤ r j - ∑ i, μ i * A i j) ∧ (∀ i, (A *ᵥ y) i < x i → μ i = 0) := by
  have hL := pv_eq_lagr hA hr hx hy₀ hμ
  have hsplit := obj_split A r μ y
  set rc : Fin n → ℝ := fun j => r j - ∑ i, μ i * A i j with hrc
  have g1 : ∀ j ∈ Finset.univ, 0 ≤ y j * (max 0 (rc j) - rc j) :=
    fun j _ => mul_nonneg (h2 j) (by linarith [le_max_right 0 (rc j)])
  have g2 : ∀ j ∈ Finset.univ, 0 ≤ (y₀ j - y j) * max 0 (rc j) :=
    fun j _ => mul_nonneg (by linarith [h3 j]) (le_max_left _ _)
  have g3 : ∀ i ∈ Finset.univ, 0 ≤ μ i * (x i - (A *ᵥ y) i) :=
    fun i _ => mul_nonneg (hμ.1 i) (by linarith [h1 i])
  have htot : ∑ j, y j * (max 0 (rc j) - rc j) + ∑ j, (y₀ j - y j) * max 0 (rc j) +
      ∑ i, μ i * (x i - (A *ᵥ y) i) = 0 := by
    have e : ∑ j, y j * (max 0 (rc j) - rc j) + ∑ j, (y₀ j - y j) * max 0 (rc j) +
        ∑ i, μ i * (x i - (A *ᵥ y) i) = lagr A r x y₀ μ - r ⬝ᵥ y := by
      rw [hsplit]
      simp only [lagr, dotProduct, hrc, mul_sub, sub_mul, Finset.sum_sub_distrib]
      ring
    rw [e, ← hL, hopt, sub_self]
  have s1 := Finset.sum_nonneg g1
  have s2 := Finset.sum_nonneg g2
  have s3 := Finset.sum_nonneg g3
  have z1 := (Finset.sum_eq_zero_iff_of_nonneg g1).1 (by linarith)
  have z3 := (Finset.sum_eq_zero_iff_of_nonneg g3).1 (by linarith)
  refine ⟨fun j hj => ?_, fun i hi => ?_⟩
  · have := z1 j (Finset.mem_univ j)
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · have : max 0 (rc j) = rc j := by linarith
      have := le_max_left 0 (rc j)
      simp only [rc] at *
      linarith
  · have := z3 i (Finset.mem_univ i)
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · linarith

/-- the consequence of Condition C1′ used in Lemma 3 -/
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

theorem lemma3 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)
    (hA : IsIncidence A) (hr : 0 ≤ r) (x : Fin m → ℝ) (hx : 0 ≤ x)
    (hC1 : ConditionOnePrime A x) (y₀ : Fin n → ℝ) (hy₀ : 0 ≤ y₀)
    (μs : Fin m → ℝ) (hμs : IsDualOpt A r x y₀ μs)
    (d : Fin m → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hfeas : ∀ h ∈ Set.Icc (0 : ℝ) ε, 0 ≤ μs + h • d)
    (h : ℝ) (hh : h ∈ Set.Ioc (0 : ℝ) ε)
    (E₀ E₁ : Set (Fin n))
    (hE₀ : E₀ = {j | r j - μs ⬝ᵥ (fun i => A i j) > 0})
    (hE₁ : E₁ = {j | r j - μs ⬝ᵥ (fun i => A i j) = 0 ∧
      r j - μs ⬝ᵥ (fun i => A i j) - h * d ⬝ᵥ (fun i => A i j) > 0})
    (hdA : ∀ j ∈ E₀ ∪ E₁, d ⬝ᵥ (fun i => A i j) = 0)
    (hdx : d ⬝ᵥ x = 0) :
    d = 0 := by
  obtain ⟨y, h1, h2, h3, hopt⟩ := pv_attained A r hr hx hy₀
  obtain ⟨cs1, cs2⟩ := compl_slack hA hr hx hy₀ hμs h1 h2 h3 hopt
  have hh0 : 0 < h := hh.1
  have hfh := hfeas h ⟨hh0.le, hh.2⟩
  -- d ⬝ x splits into nonnegative terms
  have hsplit : d ⬝ᵥ x = ∑ j, y j * d ⬝ᵥ (fun i => A i j) +
      ∑ i, (x i - (A *ᵥ y) i) * d i := by
    have := mulVec_sum_swap A d y
    have e : d ⬝ᵥ x = d ⬝ᵥ (A *ᵥ y) + ∑ i, (x i - (A *ᵥ y) i) * d i := by
      simp only [dotProduct, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, this]
    rfl
  have t1 : ∀ j ∈ Finset.univ, 0 ≤ y j * d ⬝ᵥ (fun i => A i j) := by
    intro j _
    have hy0 : (0:ℝ) ≤ y j := h2 j
    rcases hy0.lt_or_eq with hy | hy
    · have hrc := cs1 j hy
      have hrc' : 0 ≤ r j - μs ⬝ᵥ (fun i => A i j) := hrc
      rcases hrc'.lt_or_eq with hpos | hzero
      · rw [hdA j (Or.inl (by rw [hE₀]; exact hpos)), mul_zero]
      · by_cases hE : r j - μs ⬝ᵥ (fun i => A i j) - h * d ⬝ᵥ (fun i => A i j) > 0
        · rw [hdA j (Or.inr (by rw [hE₁]; exact ⟨hzero.symm, hE⟩)), mul_zero]
        · push Not at hE
          have : 0 ≤ d ⬝ᵥ (fun i => A i j) := by
            rw [← hzero] at hE
            by_contra hneg; push Not at hneg
            nlinarith
          exact mul_nonneg hy.le this
    · rw [← hy, zero_mul]
  have t2 : ∀ i ∈ Finset.univ, 0 ≤ (x i - (A *ᵥ y) i) * d i := by
    intro i _
    rcases (h1 i).lt_or_eq with hs | hs
    · have hμi := cs2 i hs
      have := hfh i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hμi, zero_add, Pi.zero_apply] at this
      exact mul_nonneg (by linarith) (nonneg_of_mul_nonneg_right (by linarith) hh0)
    · rw [hs, sub_self, zero_mul]
  have hsum0 : ∑ j, y j * d ⬝ᵥ (fun i => A i j) + ∑ i, (x i - (A *ᵥ y) i) * d i = 0 := by
    rw [← hsplit, hdx]
  have s1 := Finset.sum_nonneg t1
  have s2 := Finset.sum_nonneg t2
  have z1 := (Finset.sum_eq_zero_iff_of_nonneg t1).1 (by linarith)
  have z2 := (Finset.sum_eq_zero_iff_of_nonneg t2).1 (by linarith)
  refine c1_zero hC1 h2 d (fun j hj => ?_) (fun i hi => ?_) h1
  · rcases mul_eq_zero.1 (z1 j (Finset.mem_univ j)) with h' | h'
    · linarith
    · exact h'
  · rcases mul_eq_zero.1 (z2 i (Finset.mem_univ i)) with h' | h'
    · linarith
    · exact h'

end RLPSol

open MeasureTheory Matrix Filter Topology

namespace RLPSol
open RLPBidPrice.Unbiased

variable {m n : ℕ}

/-! ### Probability: hyperplanes are null -/

theorem atom_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → Fin n → ℝ) (hYm : Measurable Y) (hC2 : ConditionTwo P Y) (j : Fin n) (t : ℝ) :
    P {ω | Y ω j = t} = 0 := by
  have hm : Measurable fun ω => Y ω j := (measurable_pi_apply j).comp hYm
  rw [← measureReal_eq_zero_iff]
  refine le_antisymm ?_ measureReal_nonneg
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.1 (hC2 j).continuousAt ε hε
  have hs : MeasurableSet {ω | Y ω j ≤ t - δ / 2} := measurableSet_le hm measurable_const
  have key := measureReal_inter_add_sdiff (μ := P) (s := {ω | Y ω j ≤ t}) hs
  have hsub : {ω | Y ω j ≤ t} ∩ {ω | Y ω j ≤ t - δ / 2} = {ω | Y ω j ≤ t - δ / 2} := by
    ext ω; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨by linarith, h⟩
  rw [hsub] at key
  have hmono : P.real {ω | Y ω j = t} ≤
      P.real ({ω | Y ω j ≤ t} \ {ω | Y ω j ≤ t - δ / 2}) := by
    refine measureReal_mono (fun ω hω => ?_)
    simp only [Set.mem_setOf_eq] at hω
    simp only [Set.mem_diff, Set.mem_setOf_eq]
    exact ⟨hω.le, by intro h'; linarith⟩
  have hd := hcont (x := t - δ / 2) (by rw [Real.dist_eq, abs_of_neg] <;> linarith)
  rw [Real.dist_eq] at hd
  have := (abs_lt.1 hd).1
  linarith

theorem hyperplane_null {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → Fin n → ℝ) (hYm : Measurable Y) (hC2 : ConditionTwo P Y)
    (hind : ProbabilityTheory.iIndepFun (fun j ω => Y ω j) P)
    (c : Fin n → ℝ) (hc : c ≠ 0) (b : ℝ) :
    P {ω | ∑ j, c j * Y ω j = b} = 0 := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, c k ≠ 0 := by
    by_contra h; push Not at h; exact hc (funext h)
  have hm : ∀ j, Measurable fun ω => Y ω j := fun j => (measurable_pi_apply j).comp hYm
  set T : Finset (Fin n) := Finset.univ.erase k with hT
  have hdisj : Disjoint ({k} : Finset (Fin n)) T := by simp [hT]
  have hind2 := hind.indepFun_finset {k} T hdisj hm
  set X : Ω → ℝ := fun ω => Y ω k with hX
  set W : Ω → (T → ℝ) := fun ω i => Y ω i with hW
  have hXW : ProbabilityTheory.IndepFun X W P :=
    hind2.comp (φ := fun u : ({k} : Finset (Fin n)) → ℝ => u ⟨k, Finset.mem_singleton_self k⟩)
      (ψ := id) (measurable_pi_apply _) measurable_id
  have hXm : Measurable X := hm k
  have hWm : Measurable W := measurable_pi_lambda _ fun i => hm i
  set g : (ℝ × (T → ℝ)) → ℝ := fun p => c k * p.1 + ∑ i : T, c i * p.2 i with hg
  have hgm : Measurable g := by
    refine (measurable_const.mul measurable_fst).add ?_
    exact Finset.measurable_sum _ fun i _ =>
      measurable_const.mul ((measurable_pi_apply i).comp measurable_snd)
  set G := g ⁻¹' {b} with hGdef
  have hG : MeasurableSet G := hgm (measurableSet_singleton b)
  have hE : {ω | ∑ j, c j * Y ω j = b} = (fun ω => (X ω, W ω)) ⁻¹' G := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff, G, g, X, W]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    rw [Finset.sum_coe_sort T (fun i => c i * Y ω i)]
  rw [hE, ← Measure.map_apply (hXm.prodMk hWm) hG,
    (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map hXm.aemeasurable
      hWm.aemeasurable).1 hXW, Measure.prod_apply_symm hG]
  have hz : ∀ w : T → ℝ, (P.map X) ((fun a => (a, w)) ⁻¹' G) = 0 := by
    intro w
    have hset : (fun a => (a, w)) ⁻¹' G = {(b - ∑ i : T, c i * w i) / c k} := by
      ext a
      simp only [Set.mem_preimage, Set.mem_singleton_iff, G, g]
      rw [eq_div_iff hk]
      constructor <;> intro h <;> linarith
    rw [hset, Measure.map_apply hXm (measurableSet_singleton _)]
    exact atom_zero P Y hYm hC2 k _
  simp [hz]

/-! ### Geometry of the optimal dual set -/

theorem lagr_convex (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ) (x : Fin m → ℝ)
    {y₀ : Fin n → ℝ} (hy₀ : 0 ≤ y₀) (μ1 μ2 : Fin m → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    lagr A r x y₀ (a • μ1 + b • μ2) ≤ a * lagr A r x y₀ μ1 + b * lagr A r x y₀ μ2 := by
  unfold lagr
  have hterm : ∀ j, y₀ j * max 0 (r j - ∑ i, (a • μ1 + b • μ2) i * A i j) ≤
      a * (y₀ j * max 0 (r j - ∑ i, μ1 i * A i j)) +
        b * (y₀ j * max 0 (r j - ∑ i, μ2 i * A i j)) := by
    intro j
    set u := r j - ∑ i, μ1 i * A i j
    set w := r j - ∑ i, μ2 i * A i j
    have e : r j - ∑ i, (a • μ1 + b • μ2) i * A i j = a * u + b * w := by
      simp only [u, w, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
        mul_assoc, ← Finset.mul_sum]
      linear_combination (-(r j)) * hab
    rw [e]
    have hmax : max 0 (a * u + b * w) ≤ a * max 0 u + b * max 0 w :=
      max_le (by positivity) (add_le_add (mul_le_mul_of_nonneg_left (le_max_right _ _) ha)
        (mul_le_mul_of_nonneg_left (le_max_right _ _) hb))
    have hy : 0 ≤ y₀ j := hy₀ j
    calc y₀ j * max 0 (a * u + b * w) ≤ y₀ j * (a * max 0 u + b * max 0 w) :=
          mul_le_mul_of_nonneg_left hmax hy
      _ = a * (y₀ j * max 0 u) + b * (y₀ j * max 0 w) := by ring
  have hs := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hterm j
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
  have hd : (a • μ1 + b • μ2) ⬝ᵥ x = a * (μ1 ⬝ᵥ x) + b * (μ2 ⬝ᵥ x) := by
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  rw [hd]
  linarith

theorem dualSet_convex (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ) (x : Fin m → ℝ)
    {y₀ : Fin n → ℝ} (hy₀ : 0 ≤ y₀) : Convex ℝ {μ | IsDualOpt A r x y₀ μ} := by
  intro μ1 h1 μ2 h2 a b ha hb hab
  refine ⟨add_nonneg (smul_nonneg ha h1.1) (smul_nonneg hb h2.1), fun μ' hμ' => ?_⟩
  calc lagr A r x y₀ (a • μ1 + b • μ2) ≤ a * lagr A r x y₀ μ1 + b * lagr A r x y₀ μ2 :=
        lagr_convex A r x hy₀ μ1 μ2 ha hb hab
    _ ≤ a * lagr A r x y₀ μ' + b * lagr A r x y₀ μ' :=
        add_le_add (mul_le_mul_of_nonneg_left (h1.2 μ' hμ') ha)
          (mul_le_mul_of_nonneg_left (h2.2 μ' hμ') hb)
    _ = lagr A r x y₀ μ' := by rw [← add_mul, hab, one_mul]

theorem dualSet_compact (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ) {x : Fin m → ℝ}
    (hx : ∀ i, 0 < x i) {y₀ : Fin n → ℝ} (hy₀ : 0 ≤ y₀) :
    IsCompact {μ | IsDualOpt A r x y₀ μ} := by
  have hcl : IsClosed {μ | IsDualOpt A r x y₀ μ} := by
    have : {μ | IsDualOpt A r x y₀ μ} = {μ | 0 ≤ μ} ∩
        ⋂ μ' ∈ {μ' : Fin m → ℝ | 0 ≤ μ'}, {μ | lagr A r x y₀ μ ≤ lagr A r x y₀ μ'} := by
      ext μ; simp [IsDualOpt]
    rw [this]
    exact (isClosed_le continuous_const continuous_id).inter
      (isClosed_biInter fun μ' _ => isClosed_le (lagr_continuous A r x y₀) continuous_const)
  refine (isCompact_Icc (a := (0 : Fin m → ℝ)) (b := fun i => lagr A r x y₀ 0 / x i)).of_isClosed_subset
    hcl ?_
  intro μ hμ
  refine ⟨hμ.1, fun i => ?_⟩
  have h1 : lagr A r x y₀ μ ≤ lagr A r x y₀ 0 := hμ.2 0 (le_refl _)
  have h2 : μ i * x i ≤ lagr A r x y₀ μ := by
    unfold lagr
    have : 0 ≤ ∑ j, y₀ j * max 0 (r j - ∑ i, μ i * A i j) :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hy₀ j) (le_max_left _ _)
    have : μ i * x i ≤ μ ⬝ᵥ x := by
      simp only [dotProduct]
      exact Finset.single_le_sum (f := fun k => μ k * x k)
        (fun k _ => mul_nonneg (hμ.1 k) (hx k).le) (Finset.mem_univ i)
    linarith
  show μ i ≤ lagr A r x y₀ 0 / x i
  rw [le_div_iff₀ (hx i)]; linarith

/-- the (finite) set of vertices of the hyperplane arrangement `μ ⬝ Aʲ = rʲ`, `μᵢ = 0` -/
def vset (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ) : Set (Fin m → ℝ) :=
  ⋃ (J : Finset (Fin n)) (I : Finset (Fin m)),
    {μ | {ν : Fin m → ℝ | (∀ j ∈ J, ∑ i, ν i * A i j = r j) ∧ ∀ i ∈ I, ν i = 0} = {μ}}

theorem vset_finite (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ) : (vset A r).Finite := by
  refine Set.finite_iUnion fun J => Set.finite_iUnion fun I => Set.Subsingleton.finite ?_
  intro μ hμ μ' hμ'
  have := (Set.mem_setOf_eq ▸ hμ).symm.trans (Set.mem_setOf_eq ▸ hμ')
  exact Set.singleton_eq_singleton_iff.1 this

theorem ev_pos {a : ℝ} (b : ℝ) (h : 0 < a) : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < a + t * b := by
  have : Tendsto (fun t : ℝ => a + t * b) (𝓝 0) (𝓝 (a + 0 * b)) :=
    (continuous_const.add (continuous_id.mul continuous_const)).tendsto 0
  rw [zero_mul, add_zero] at this
  exact this.eventually (Ioi_mem_nhds h)

theorem ev_neg {a : ℝ} (b : ℝ) (h : a < 0) : ∀ᶠ t in 𝓝 (0 : ℝ), a + t * b < 0 := by
  have : Tendsto (fun t : ℝ => a + t * b) (𝓝 0) (𝓝 (a + 0 * b)) :=
    (continuous_const.add (continuous_id.mul continuous_const)).tendsto 0
  rw [zero_mul, add_zero] at this
  exact this.eventually (Iio_mem_nhds h)

theorem lagr_line (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ) (x : Fin m → ℝ)
    (y₀ : Fin n → ℝ) (μ d : Fin m → ℝ) (t : ℝ) :
    lagr A r x y₀ (μ + t • d) = ∑ j, y₀ j * max 0 ((r j - ∑ i, μ i * A i j) +
      t * (-(∑ i, d i * A i j))) + (μ ⬝ᵥ x + t * (d ⬝ᵥ x)) := by
  unfold lagr
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    congr 2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
      mul_assoc, ← Finset.mul_sum]
    ring
  · rw [add_dotProduct, smul_dotProduct, smul_eq_mul]

theorem ext_mem_vset {A : Matrix (Fin m) (Fin n) ℝ} {r : Fin n → ℝ} {x : Fin m → ℝ}
    {y₀ : Fin n → ℝ} (hy₀ : 0 ≤ y₀) {μ : Fin m → ℝ}
    (hμ : μ ∈ {μ | IsDualOpt A r x y₀ μ}.extremePoints ℝ) : μ ∈ vset A r := by
  classical
  obtain ⟨hopt, hext⟩ := mem_extremePoints.1 hμ
  have hopt' : IsDualOpt A r x y₀ μ := hopt
  set J := Finset.univ.filter fun j => ∑ i, μ i * A i j = r j
  set I := Finset.univ.filter fun i => μ i = 0
  refine Set.mem_iUnion.2 ⟨J, Set.mem_iUnion.2 ⟨I, ?_⟩⟩
  show {ν : Fin m → ℝ | (∀ j ∈ J, ∑ i, ν i * A i j = r j) ∧ ∀ i ∈ I, ν i = 0} = {μ}
  ext ν
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hJ, hI⟩
    by_contra hne
    set d := ν - μ with hd
    set rc : Fin n → ℝ := fun j => r j - ∑ i, μ i * A i j
    set e : Fin n → ℝ := fun j => ∑ i, d i * A i j
    have hdJ : ∀ j, rc j = 0 → e j = 0 := by
      intro j hj
      have h1 : ∑ i, μ i * A i j = r j := by simp only [rc] at hj; linarith
      have h2 := hJ j (Finset.mem_filter.2 ⟨Finset.mem_univ j, h1⟩)
      simp only [e, d, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      linarith
    have hdI : ∀ i, μ i = 0 → d i = 0 := by
      intro i hi
      have := hI i (Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩)
      simp [d, this, hi]
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ),
        (∀ i, 0 ≤ μ i + t * d i ∧ 0 ≤ μ i + t * (-d i)) ∧
        ∀ j, max 0 (rc j + t * (-e j)) + max 0 (rc j + t * e j) = 2 * max 0 (rc j) := by
      refine (Filter.eventually_all.2 fun i => ?_).and (Filter.eventually_all.2 fun j => ?_)
      · have hμi : 0 ≤ μ i := hopt'.1 i
        rcases hμi.lt_or_eq with hp | hz
        · filter_upwards [ev_pos (d i) hp, ev_pos (-d i) hp] with t h1 h2
          exact ⟨h1.le, h2.le⟩
        · refine Eventually.of_forall fun t => ?_
          rw [hdI i hz.symm, ← hz]; simp
      · rcases lt_trichotomy (rc j) 0 with hn | hz | hp
        · filter_upwards [ev_neg (-e j) hn, ev_neg (e j) hn] with t h1 h2
          rw [max_eq_left h1.le, max_eq_left h2.le, max_eq_left hn.le]; ring
        · refine Eventually.of_forall fun t => ?_
          rw [hdJ j hz, hz]; simp
        · filter_upwards [ev_pos (-e j) hp, ev_pos (e j) hp] with t h1 h2
          rw [max_eq_right h1.le, max_eq_right h2.le, max_eq_right hp.le]; ring
    obtain ⟨ε, hε, hP⟩ := Metric.eventually_nhds_iff.1 hev
    set t := ε / 2
    have ht : 0 < t := by positivity
    obtain ⟨hpos, hlin⟩ := hP (y := t) (by rw [Real.dist_eq, sub_zero, abs_of_pos ht]; simp only [t]; linarith)
    have hp1 : 0 ≤ μ + t • d := fun i => by simpa using (hpos i).1
    have hp2 : 0 ≤ μ + (-t) • d := fun i => by
      have := (hpos i).2; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      linarith
    have hsum : lagr A r x y₀ (μ + t • d) + lagr A r x y₀ (μ + (-t) • d) =
        2 * lagr A r x y₀ μ := by
      rw [lagr_line, lagr_line]
      unfold lagr
      have : ∀ j, y₀ j * max 0 (rc j + t * -e j) + y₀ j * max 0 (rc j + -t * -e j) =
          2 * (y₀ j * max 0 (rc j)) := by
        intro j
        have := hlin j
        have e2 : rc j + -t * -e j = rc j + t * e j := by ring
        rw [e2, ← mul_add, this]; ring
      have hs : ∑ j, y₀ j * max 0 (rc j + t * -e j) + ∑ j, y₀ j * max 0 (rc j + -t * -e j) =
          2 * ∑ j, y₀ j * max 0 (rc j) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => this j
      simp only [rc, e] at hs
      linarith
    have hL1 := hopt'.2 _ hp1
    have hL2 := hopt'.2 _ hp2
    have ho1 : IsDualOpt A r x y₀ (μ + t • d) :=
      ⟨hp1, fun μ' hμ' => by linarith [hopt'.2 μ' hμ']⟩
    have ho2 : IsDualOpt A r x y₀ (μ + (-t) • d) :=
      ⟨hp2, fun μ' hμ' => by linarith [hopt'.2 μ' hμ']⟩
    have hseg : μ ∈ openSegment ℝ (μ + (-t) • d) (μ + t • d) := by
      refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
      ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    have := (hext _ ho2 _ ho1 hseg).2
    have hd0 : t • d = 0 := by
      have h' : μ + t • d - μ = 0 := by rw [this, sub_self]
      simpa using h'
    have : d = 0 := by
      rcases smul_eq_zero.1 hd0 with h | h
      · exact absurd h ht.ne'
      · exact h
    exact hne (sub_eq_zero.1 this)
  · rintro rfl
    refine ⟨fun j hj => (Finset.mem_filter.1 hj).2, fun i hi => (Finset.mem_filter.1 hi).2⟩

theorem two_ext {O : Set (Fin m → ℝ)} (hc : IsCompact O) (hv : Convex ℝ O) {a b : Fin m → ℝ}
    (ha : a ∈ O) (hb : b ∈ O) (hab : a ≠ b) :
    ∃ v1 ∈ O.extremePoints ℝ, ∃ v2 ∈ O.extremePoints ℝ, v1 ≠ v2 := by
  by_contra h
  push Not at h
  have hs : (O.extremePoints ℝ).Subsingleton := fun v1 h1 v2 h2 => h v1 h1 v2 h2
  have hO := closure_convexHull_extremePoints hc hv
  have hsub : (closure (convexHull ℝ (O.extremePoints ℝ))).Subsingleton := by
    rcases hs.eq_empty_or_singleton with he | ⟨v, hv⟩
    · rw [he]; simp
    · rw [hv, convexHull_singleton, closure_singleton]; exact Set.subsingleton_singleton
  rw [hO] at hsub
  exact hab (hsub ha hb)

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

theorem lemma4 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)
    (hA : IsIncidence A) (hr : 0 ≤ r) (x : Fin m → ℝ) (hx : 0 ≤ x)
    (hC1 : ConditionOnePrime A x)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → Fin n → ℝ) (hYm : Measurable Y) (hY0 : ∀ᵐ ω ∂P, 0 ≤ Y ω)
    (hC2 : ConditionTwo P Y) (hind : ProbabilityTheory.iIndepFun (fun j ω => Y ω j) P) :
    ∀ᵐ ω ∂P, DifferentiableAt ℝ (fun x' => piValue A r x' (Y ω)) x := by
  have hxpos : ∀ i, 0 < x i := c1_pos hx hC1
  set c : (Fin m → ℝ) → (Fin m → ℝ) → Fin n → ℝ := fun v1 v2 j =>
    max 0 (r j - ∑ i, v1 i * A i j) - max 0 (r j - ∑ i, v2 i * A i j) with hcdef
  set b : (Fin m → ℝ) → (Fin m → ℝ) → ℝ := fun v1 v2 => (v2 - v1) ⬝ᵥ x with hbdef
  have hgood : ∀ᵐ ω ∂P, ∀ p : (vset A r) × (vset A r), c p.1 p.2 ≠ 0 →
      ∑ j, c p.1 p.2 j * Y ω j ≠ b p.1 p.2 := by
    haveI : Countable (vset A r) := (vset_finite A r).countable.to_subtype
    rw [ae_all_iff]
    intro p
    by_cases hcp : c p.1 p.2 = 0
    · exact Eventually.of_forall fun ω h => absurd hcp h
    · rw [ae_iff]
      refine measure_mono_null (fun ω hω => ?_) (hyperplane_null P Y hYm hC2 hind _ hcp (b p.1 p.2))
      simp only [Set.mem_setOf_eq, not_forall, not_not] at hω ⊢
      obtain ⟨-, h⟩ := hω
      exact h
  filter_upwards [hgood, hY0] with ω hω hY
  obtain ⟨μ, hμ, -⟩ := exists_dualOpt_box hA hr hx hY
  refine (hasFDerivAt_of_unique hA hr hxpos hY hμ fun μ' hμ' => ?_).differentiableAt
  by_contra hne
  obtain ⟨v1, h1, v2, h2, h12⟩ := two_ext (dualSet_compact A r hxpos hY)
    (dualSet_convex A r x hY) hμ' hμ hne
  have hv1 := ext_mem_vset hY h1
  have hv2 := ext_mem_vset hY h2
  have o1 : IsDualOpt A r x (Y ω) v1 := h1.1
  have o2 : IsDualOpt A r x (Y ω) v2 := h2.1
  have heqL : lagr A r x (Y ω) v1 = lagr A r x (Y ω) v2 :=
    le_antisymm (o1.2 v2 o2.1) (o2.2 v1 o1.1)
  have hcY : ∑ j, c v1 v2 j * Y ω j = b v1 v2 := by
    unfold lagr at heqL
    simp only [c, b, sub_dotProduct, sub_mul, Finset.sum_sub_distrib]
    have e1 : ∑ j, max 0 (r j - ∑ i, v1 i * A i j) * Y ω j =
        ∑ j, Y ω j * max 0 (r j - ∑ i, v1 i * A i j) :=
      Finset.sum_congr rfl fun j _ => mul_comm _ _
    have e2 : ∑ j, max 0 (r j - ∑ i, v2 i * A i j) * Y ω j =
        ∑ j, Y ω j * max 0 (r j - ∑ i, v2 i * A i j) :=
      Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [e1, e2]; linarith
  by_cases hc0 : c v1 v2 = 0
  · obtain ⟨y, hy1, hy2, hy3, hopt⟩ := pv_attained A r hr hx hY
    obtain ⟨cs1a, cs2a⟩ := compl_slack hA hr hx hY o1 hy1 hy2 hy3 hopt
    obtain ⟨cs1b, cs2b⟩ := compl_slack hA hr hx hY o2 hy1 hy2 hy3 hopt
    have hd := c1_zero hC1 hy2 (v2 - v1) (fun j hj => ?_) (fun i hi => ?_) hy1
    · exact h12 (sub_eq_zero.1 hd).symm
    · have ha := cs1a j hj
      have hb := cs1b j hj
      have hcj := congrFun hc0 j
      simp only [c, max_eq_right ha, max_eq_right hb, Pi.zero_apply] at hcj
      simp only [dotProduct, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      linarith
    · simp [cs2a i hi, cs2b i hi]
  · exact hω ⟨⟨v1, hv1⟩, ⟨v2, hv2⟩⟩ hc0 hcY

end RLPSol

open MeasureTheory Matrix RLPBidPrice.Unbiased in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)
    (hA : IsIncidence A) (hr : 0 ≤ r) (x : Fin m → ℝ) (hx : 0 ≤ x)
    (hC1 : ConditionOnePrime A x)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → Fin n → ℝ) (hYm : Measurable Y) (hY0 : ∀ᵐ ω ∂P, 0 ≤ Y ω)
    (hC2 : ConditionTwo P Y) (hind : ProbabilityTheory.iIndepFun (fun j ω => Y ω j) P) :
    ∀ᵐ ω ∂P, DifferentiableAt ℝ (fun x' => piValue A r x' (Y ω)) x :=
  RLPSol.lemma4 A r hA hr x hx hC1 P Y hYm hY0 hC2 hind
