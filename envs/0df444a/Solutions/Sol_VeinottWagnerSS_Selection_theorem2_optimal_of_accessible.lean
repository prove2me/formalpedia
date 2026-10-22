-- Prove2me | solution 1 for VeinottWagnerSS.Selection.theorem2_optimal_of_accessible
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T23:21:36.150986+00:00
-- url     : https://prove2.me/submissions/e2323a1a-a852-4315-a2f7-26252317a446

import Mathlib
import Definitions.Def_VeinottWagnerSS_Selection_Model
import Definitions.Def_VeinottWagnerSS_Selection_CandidateSet

open scoped ENNReal

namespace VeinottWagnerSS.Selection

/-! ### Part 1: the chain -/

lemma vw2_stateLaw_succ (M : Model) (s S x : ℤ) (t : ℕ) :
    stateLaw M s S x (t + 1)
      = M.φ.bind (fun k : ℕ => stateLaw M s S (sSOrder s S x - k) t) := by
  induction t with
  | zero =>
    simp only [stateLaw, PMF.pure_bind]
    rw [PMF.map]
    rfl
  | succ t ih =>
    show (stateLaw M s S x (t + 1)).bind _ = _
    rw [ih, PMF.bind_bind]
    rfl

lemma vw2_support_le (M : Model) (s S x : ℤ) (t : ℕ) (y : ℤ)
    (hy : stateLaw M s S x t y ≠ 0) : y ≤ max x S := by
  induction t generalizing y with
  | zero =>
    simp only [stateLaw, PMF.pure_apply, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
      not_not] at hy
    subst hy; exact le_max_left _ _
  | succ t ih =>
    have hmem : y ∈ (stateLaw M s S x (t + 1)).support := (PMF.mem_support_iff _ _).2 hy
    simp only [stateLaw, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hmem
    obtain ⟨y', hy', k, -, rfl⟩ := hmem
    have := ih y' ((PMF.mem_support_iff _ _).1 hy')
    unfold sSOrder
    split_ifs <;> omega

/-- A crude bound for the period cost of states `≤ Mx`. -/
noncomputable def vw2_Cb (M : Model) (s S Mx : ℤ) : ℝ :=
  M.K + |M.G S| + ∑ z ∈ Finset.Icc s Mx, |M.G z|

lemma vw2_Cb_nonneg (M : Model) (s S Mx : ℤ) : 0 ≤ vw2_Cb M s S Mx := by
  unfold vw2_Cb
  have := M.K_nonneg
  have : 0 ≤ ∑ z ∈ Finset.Icc s Mx, |M.G z| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  linarith [abs_nonneg (M.G S)]

lemma vw2_periodCost_le (M : Model) (s S Mx y : ℤ) (hy : y ≤ Mx) :
    |periodCost M s S y| ≤ vw2_Cb M s S Mx := by
  unfold periodCost vw2_Cb delta
  have hK := M.K_nonneg
  have h1 : |M.K * (if 0 < sSOrder s S y - y then (1:ℝ) else 0)| ≤ M.K := by
    split_ifs <;> simp [abs_of_nonneg hK, hK]
  have h2 : |M.G (sSOrder s S y)| ≤ |M.G S| + ∑ z ∈ Finset.Icc s Mx, |M.G z| := by
    unfold sSOrder
    split_ifs with h
    · linarith [Finset.sum_nonneg (fun z (_ : z ∈ Finset.Icc s Mx) => abs_nonneg (M.G z))]
    · have : |M.G y| ≤ ∑ z ∈ Finset.Icc s Mx, |M.G z| :=
        Finset.single_le_sum (fun z _ => abs_nonneg (M.G z)) (by simp; omega)
      linarith [abs_nonneg (M.G S)]
  calc |M.K * (if 0 < sSOrder s S y - y then (1:ℝ) else 0) + M.G (sSOrder s S y)|
      ≤ |M.K * (if 0 < sSOrder s S y - y then (1:ℝ) else 0)| + |M.G (sSOrder s S y)| :=
        abs_add_le _ _
    _ ≤ _ := by linarith

/-! ### Part 2: sums against a PMF -/

lemma vw2_summable_toReal (p : PMF ℤ) : Summable (fun y => (p y).toReal) :=
  ENNReal.summable_toReal (by rw [PMF.tsum_coe]; exact ENNReal.one_ne_top)

lemma vw2_tsum_toReal (p : PMF ℤ) : ∑' y, (p y).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun _ => PMF.apply_ne_top _ _), PMF.tsum_coe]; simp

lemma vw2_summable_phi (M : Model) : Summable (fun k => (M.φ k).toReal) :=
  ENNReal.summable_toReal (by rw [PMF.tsum_coe]; exact ENNReal.one_ne_top)

lemma vw2_tsum_phi (M : Model) : ∑' k, (M.φ k).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun _ => PMF.apply_ne_top _ _), PMF.tsum_coe]; simp

lemma vw2_summable_pmf_mul (p : PMF ℤ) (c : ℤ → ℝ) (C : ℝ)
    (hc : ∀ y, p y ≠ 0 → |c y| ≤ C) :
    Summable (fun y => (p y).toReal * c y) := by
  refine Summable.of_norm_bounded (g := fun y => (p y).toReal * C)
    ((vw2_summable_toReal p).mul_right C) (fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  by_cases h : p y = 0
  · simp [h]
  · exact mul_le_mul_of_nonneg_left (hc y h) ENNReal.toReal_nonneg

lemma vw2_abs_tsum_pmf_mul_le (p : PMF ℤ) (c : ℤ → ℝ) (C : ℝ)
    (hc : ∀ y, p y ≠ 0 → |c y| ≤ C) :
    |∑' y, (p y).toReal * c y| ≤ C := by
  have hs := vw2_summable_pmf_mul p c C hc
  have hb : ∀ y, |(p y).toReal * c y| ≤ (p y).toReal * C := by
    intro y
    rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    by_cases h : p y = 0
    · simp [h]
    · exact mul_le_mul_of_nonneg_left (hc y h) ENNReal.toReal_nonneg
  calc |∑' y, (p y).toReal * c y| ≤ ∑' y, |(p y).toReal * c y| := by
        rw [← Real.norm_eq_abs]
        refine (norm_tsum_le_tsum_norm ?_)
        exact hs.abs
    _ ≤ ∑' y, (p y).toReal * C := Summable.tsum_le_tsum hb hs.abs ((vw2_summable_toReal p).mul_right C)
    _ = C := by rw [tsum_mul_right, vw2_tsum_toReal, one_mul]

lemma vw2_summable_phi_mul (M : Model) (c : ℕ → ℝ) (C : ℝ) (hc : ∀ k, |c k| ≤ C) :
    Summable (fun k => (M.φ k).toReal * c k) := by
  refine Summable.of_norm_bounded (g := fun k => (M.φ k).toReal * C)
    ((vw2_summable_phi M).mul_right C) (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  exact mul_le_mul_of_nonneg_left (hc k) ENNReal.toReal_nonneg

lemma vw2_tsum_phi_mul_le (M : Model) (c : ℕ → ℝ) (C : ℝ) (hc : ∀ k, |c k| ≤ C)
    (hc' : ∀ k, c k ≤ C) : ∑' k, (M.φ k).toReal * c k ≤ C := by
  calc ∑' k, (M.φ k).toReal * c k ≤ ∑' k, (M.φ k).toReal * C :=
        Summable.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_left (hc' k) ENNReal.toReal_nonneg)
          (vw2_summable_phi_mul M c C hc) ((vw2_summable_phi M).mul_right C)
    _ = C := by rw [tsum_mul_right, vw2_tsum_phi, one_mul]

/-! ### Part 3: the expected period cost -/

lemma vw2_abs_expectedPeriodCost_le (M : Model) (s S Mx x : ℤ) (hS : S ≤ Mx) (hx : x ≤ Mx)
    (t : ℕ) : |expectedPeriodCost M s S x t| ≤ vw2_Cb M s S Mx := by
  unfold expectedPeriodCost
  apply vw2_abs_tsum_pmf_mul_le
  intro y hy
  apply vw2_periodCost_le
  have := vw2_support_le M s S x t y hy
  omega

lemma vw2_expectedPeriodCost_zero (M : Model) (s S x : ℤ) :
    expectedPeriodCost M s S x 0 = periodCost M s S x := by
  unfold expectedPeriodCost
  simp only [stateLaw, PMF.pure_apply]
  rw [tsum_eq_single x]
  · simp
  · intro y hy; simp [hy]

lemma vw2_expectedPeriodCost_succ (M : Model) (s S x : ℤ) (t : ℕ) :
    expectedPeriodCost M s S x (t + 1)
      = ∑' k : ℕ, (M.φ k).toReal * expectedPeriodCost M s S (sSOrder s S x - k) t := by
  unfold expectedPeriodCost
  rw [vw2_stateLaw_succ]
  simp only [PMF.bind_apply]
  have h1 : ∀ y, (∑' k : ℕ, M.φ k * stateLaw M s S (sSOrder s S x - k) t y).toReal
      = ∑' k : ℕ, (M.φ k).toReal * (stateLaw M s S (sSOrder s S x - k) t y).toReal := by
    intro y
    rw [ENNReal.tsum_toReal_eq (fun k => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
      (PMF.apply_ne_top _ _))]
    simp only [ENNReal.toReal_mul]
  simp only [h1]
  set Mx := max x S with hMx
  set C := vw2_Cb M s S Mx
  -- the double family
  let f : ℤ → ℕ → ℝ := fun y k =>
    (M.φ k).toReal * (stateLaw M s S (sSOrder s S x - k) t y).toReal * periodCost M s S y
  have hbound : ∀ y k, |f y k| ≤ (M.φ k).toReal * (stateLaw M s S (sSOrder s S x - k) t y).toReal * C := by
    intro y k
    simp only [f]
    rw [abs_mul, abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)]
    by_cases h : stateLaw M s S (sSOrder s S x - k) t y = 0
    · simp [h]
    · apply mul_le_mul_of_nonneg_left _ (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      apply vw2_periodCost_le
      have := vw2_support_le M s S _ t y h
      have : sSOrder s S x - (k : ℤ) ≤ Mx := by
        unfold sSOrder; split_ifs <;> omega
      omega
  have hsum_g : Summable (fun yk : ℤ × ℕ =>
      (M.φ yk.2).toReal * (stateLaw M s S (sSOrder s S x - yk.2) t yk.1).toReal) := by
    have : Summable (fun yk : ℤ × ℕ =>
        (M.φ yk.2 * stateLaw M s S (sSOrder s S x - yk.2) t yk.1).toReal) := by
      apply ENNReal.summable_toReal
      rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
      simp only [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
      exact ENNReal.one_ne_top
    simpa only [ENNReal.toReal_mul] using this
  have hsum_f : Summable (Function.uncurry f) := by
    refine Summable.of_norm_bounded (g := fun yk : ℤ × ℕ =>
      (M.φ yk.2).toReal * (stateLaw M s S (sSOrder s S x - yk.2) t yk.1).toReal * C)
      (hsum_g.mul_right C) (fun yk => ?_)
    rw [Real.norm_eq_abs]
    exact hbound yk.1 yk.2
  have hsum_f1 : ∀ y, Summable (fun k => f y k) := fun y =>
    (hsum_f.prod_factor y)
  have hsum_f2 : ∀ k, Summable (fun y => f y k) := fun k =>
    ((hsum_f.prod_symm).prod_factor k)
  calc ∑' y, (∑' k : ℕ, (M.φ k).toReal * (stateLaw M s S (sSOrder s S x - k) t y).toReal)
        * periodCost M s S y
      = ∑' y, ∑' k, f y k := by
        congr 1; ext y
        rw [← tsum_mul_right]
    _ = ∑' k, ∑' y, f y k := (Summable.tsum_comm' hsum_f hsum_f1 hsum_f2).symm
    _ = ∑' k : ℕ, (M.φ k).toReal
          * ∑' y, (stateLaw M s S (sSOrder s S x - k) t y).toReal * periodCost M s S y := by
        congr 1; ext k
        rw [← tsum_mul_left]
        congr 1; ext y
        simp only [f]; ring

/-! ### Part 4: the recursion for `fCost` -/

lemma vw2_summable_fCost_terms (M : Model) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) (s S x : ℤ) :
    Summable (fun t : ℕ => α ^ t * expectedPeriodCost M s S x t) := by
  refine Summable.of_norm_bounded (g := fun t => α ^ t * vw2_Cb M s S (max x S))
    ((summable_geometric_of_lt_one hα0 hα1).mul_right _) (fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hα0 t)]
  exact mul_le_mul_of_nonneg_left (vw2_abs_expectedPeriodCost_le M s S (max x S) x
    (le_max_right _ _) (le_max_left _ _) t) (pow_nonneg hα0 t)

lemma vw2_abs_fCost_le (M : Model) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) (s S Mx x : ℤ)
    (hS : S ≤ Mx) (hx : x ≤ Mx) :
    |fCost M α s S x| ≤ vw2_Cb M s S Mx / (1 - α) := by
  unfold fCost
  have hs := vw2_summable_fCost_terms M α hα0 hα1 s S x
  have hg : Summable (fun t : ℕ => α ^ t * vw2_Cb M s S Mx) :=
    (summable_geometric_of_lt_one hα0 hα1).mul_right _
  calc |∑' t, α ^ t * expectedPeriodCost M s S x t|
      ≤ ∑' t, |α ^ t * expectedPeriodCost M s S x t| := by
        rw [← Real.norm_eq_abs]
        exact norm_tsum_le_tsum_norm hs.abs
    _ ≤ ∑' t, α ^ t * vw2_Cb M s S Mx := by
        refine Summable.tsum_le_tsum (fun t => ?_) hs.abs hg
        rw [abs_mul, abs_of_nonneg (pow_nonneg hα0 t)]
        exact mul_le_mul_of_nonneg_left (vw2_abs_expectedPeriodCost_le M s S Mx x hS hx t)
          (pow_nonneg hα0 t)
    _ = vw2_Cb M s S Mx / (1 - α) := by
        rw [tsum_mul_right, tsum_geometric_of_lt_one hα0 hα1, div_eq_mul_inv, mul_comm]

lemma vw2_sSOrder_le (s S x : ℤ) (k : ℕ) : sSOrder s S x - k ≤ max x S := by
  unfold sSOrder; split_ifs <;> omega

lemma vw2_fCost_rec (M : Model) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) (s S x : ℤ) :
    fCost M α s S x = periodCost M s S x
      + α * ∑' k : ℕ, (M.φ k).toReal * fCost M α s S (sSOrder s S x - k) := by
  unfold fCost
  rw [(vw2_summable_fCost_terms M α hα0 hα1 s S x).tsum_eq_zero_add]
  simp only [pow_zero, one_mul, vw2_expectedPeriodCost_zero, vw2_expectedPeriodCost_succ, pow_succ]
  congr 1
  set Mx := max x S with hMx
  set C := vw2_Cb M s S Mx with hC
  have hC0 : 0 ≤ C := vw2_Cb_nonneg M s S Mx
  have hE : ∀ (k t : ℕ), |expectedPeriodCost M s S (sSOrder s S x - k) t| ≤ C := fun k t =>
    vw2_abs_expectedPeriodCost_le M s S Mx _ (le_max_right _ _) (vw2_sSOrder_le s S x k) t
  let g : ℕ → ℕ → ℝ := fun t k =>
    α ^ t * ((M.φ k).toReal * expectedPeriodCost M s S (sSOrder s S x - k) t)
  have hg : Summable (Function.uncurry g) := by
    refine Summable.of_norm_bounded (g := fun tk : ℕ × ℕ => α ^ tk.1 * ((M.φ tk.2).toReal * C))
      ?_ ?_
    · exact (summable_geometric_of_lt_one hα0 hα1).mul_of_nonneg ((vw2_summable_phi M).mul_right C)
        (fun t => pow_nonneg hα0 t) (fun k => mul_nonneg ENNReal.toReal_nonneg hC0)
    · intro tk
      simp only [Function.uncurry, g, Real.norm_eq_abs]
      rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hα0 _), abs_of_nonneg ENNReal.toReal_nonneg]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hE _ _) ENNReal.toReal_nonneg) (pow_nonneg hα0 _)
  have hg1 : ∀ t, Summable (fun k => g t k) := fun t => hg.prod_factor t
  have hg2 : ∀ k, Summable (fun t => g t k) := fun k => hg.prod_symm.prod_factor k
  calc ∑' t, α ^ t * α * ∑' k, (M.φ k).toReal * expectedPeriodCost M s S (sSOrder s S x - k) t
      = ∑' t, α * ∑' k, g t k := by
        congr 1; ext t
        rw [← tsum_mul_left, ← tsum_mul_left]
        congr 1; ext k
        simp only [g]; ring
    _ = α * ∑' t, ∑' k, g t k := tsum_mul_left
    _ = α * ∑' k, ∑' t, g t k := by
        rw [Summable.tsum_comm' hg hg1 hg2]
    _ = α * ∑' k, (M.φ k).toReal * ∑' t, α ^ t * expectedPeriodCost M s S (sSOrder s S x - k) t := by
        congr 1
        congr 1; ext k
        rw [← tsum_mul_left]
        congr 1; ext t
        simp only [g]; ring

lemma vw2_summable_phi_fCost (M : Model) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) (s S Mx y : ℤ)
    (hS : S ≤ Mx) (hy : y ≤ Mx) :
    Summable (fun k : ℕ => (M.φ k).toReal * fCost M α s S (y - k)) :=
  vw2_summable_phi_mul M _ _ (fun k => vw2_abs_fCost_le M α hα0 hα1 s S Mx (y - k) hS (by omega))

lemma vw2_fCost_order (M : Model) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) (s S x : ℤ)
    (hs : s ≤ S) (hx : x < s) :
    fCost M α s S x = M.K + M.G S + α * ∑' k : ℕ, (M.φ k).toReal * fCost M α s S (S - k) := by
  rw [vw2_fCost_rec M α hα0 hα1]
  have h1 : sSOrder s S x = S := by unfold sSOrder; simp [hx]
  simp only [periodCost, h1, delta]
  rw [if_pos (by omega)]
  ring

lemma vw2_fCost_sit (M : Model) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) (s S x : ℤ)
    (hx : s ≤ x) :
    fCost M α s S x = M.G x + α * ∑' k : ℕ, (M.φ k).toReal * fCost M α s S (x - k) := by
  rw [vw2_fCost_rec M α hα0 hα1]
  have h1 : sSOrder s S x = x := by unfold sSOrder; simp [not_lt.2 hx]
  simp only [periodCost, h1, delta, sub_self, lt_irrefl, if_false, mul_zero, zero_add]

lemma vw2_fCost_order_eq (M : Model) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) (s S x x' : ℤ)
    (hs : s ≤ S) (hx : x < s) (hx' : x' < s) :
    fCost M α s S x = fCost M α s S x' := by
  rw [vw2_fCost_order M α hα0 hα1 s S x hs hx, vw2_fCost_order M α hα0 hα1 s S x' hs hx']

lemma vw2_tsum_phi_mul_le' (M : Model) (c : ℕ → ℝ) (C : ℝ)
    (hs : Summable (fun k => (M.φ k).toReal * c k)) (hc' : ∀ k, c k ≤ C) :
    ∑' k, (M.φ k).toReal * c k ≤ C := by
  calc ∑' k, (M.φ k).toReal * c k ≤ ∑' k, (M.φ k).toReal * C :=
        Summable.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_left (hc' k) ENNReal.toReal_nonneg)
          hs ((vw2_summable_phi M).mul_right C)
    _ = C := by rw [tsum_mul_right, vw2_tsum_phi, one_mul]

lemma vw2_phi0_lt (M : Model) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    α * (M.φ 0).toReal < 1 := by
  have h1 : (M.φ 0).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one M.φ 0)
    simpa using this
  nlinarith [ENNReal.toReal_nonneg (a := M.φ 0)]

/-- Comparison at a state where both policies do not order. -/
lemma vw2_sit_compare (M : Model) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (s S s' S' x : ℤ) (hx : s ≤ x) (hx' : s' ≤ x)
    (hk : ∀ k : ℕ, 1 ≤ k → fCost M α s' S' (x - k) ≤ fCost M α s S (x - k)) :
    fCost M α s' S' x ≤ fCost M α s S x := by
  have h1 := vw2_fCost_sit M α hα0 hα1 s S x hx
  have h2 := vw2_fCost_sit M α hα0 hα1 s' S' x hx'
  have hs1 := vw2_summable_phi_fCost M α hα0 hα1 s S (max x S) x (le_max_right _ _) (le_max_left _ _)
  have hs2 := vw2_summable_phi_fCost M α hα0 hα1 s' S' (max x S') x (le_max_right _ _) (le_max_left _ _)
  rw [hs1.tsum_eq_zero_add] at h1
  rw [hs2.tsum_eq_zero_add] at h2
  simp only [Nat.cast_zero, sub_zero] at h1 h2
  have hle : ∑' k : ℕ, (M.φ (k + 1)).toReal * fCost M α s' S' (x - ((k + 1 : ℕ) : ℤ))
      ≤ ∑' k : ℕ, (M.φ (k + 1)).toReal * fCost M α s S (x - ((k + 1 : ℕ) : ℤ)) :=
    Summable.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_left (hk (k + 1) (by omega))
      ENNReal.toReal_nonneg) ((summable_nat_add_iff 1).2 hs2) ((summable_nat_add_iff 1).2 hs1)
  have hφ := vw2_phi0_lt M α hα0 hα1
  nlinarith

/-- The maximum principle: a bounded function dominated by `c` on the boundary and harmonic
(discounted) above it is dominated by `c` everywhere. -/
lemma vw2_max_principle (M : Model) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) (D : ℤ → ℝ)
    (Mx σ : ℤ) (c B : ℝ) (hc : 0 ≤ c)
    (hB : ∀ y, y ≤ Mx → |D y| ≤ B)
    (h1 : ∀ y, y ≤ Mx → y < σ → D y ≤ c)
    (h2 : ∀ y, y ≤ Mx → σ ≤ y → D y = α * ∑' k : ℕ, (M.φ k).toReal * D (y - k)) :
    ∀ y, y ≤ Mx → D y ≤ c := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB Mx le_rfl)
  have key : ∀ n : ℕ, ∀ y, y ≤ Mx → D y ≤ c + α ^ n * B := by
    intro n
    induction n with
    | zero => intro y hy; simp only [pow_zero, one_mul]; linarith [le_abs_self (D y), hB y hy]
    | succ n ih =>
      intro y hy
      by_cases hyσ : y < σ
      · linarith [h1 y hy hyσ, mul_nonneg (pow_nonneg hα0 (n + 1)) hB0]
      · push_neg at hyσ
        rw [h2 y hy hyσ]
        have hs : Summable (fun k : ℕ => (M.φ k).toReal * D (y - k)) :=
          vw2_summable_phi_mul M _ B (fun k => hB _ (by omega))
        have hle : ∑' k : ℕ, (M.φ k).toReal * D (y - k) ≤ c + α ^ n * B :=
          vw2_tsum_phi_mul_le' M _ _ hs (fun k => ih _ (by omega))
        calc α * ∑' k : ℕ, (M.φ k).toReal * D (y - k) ≤ α * (c + α ^ n * B) :=
              mul_le_mul_of_nonneg_left hle hα0
          _ ≤ c + α ^ (n + 1) * B := by rw [pow_succ]; nlinarith
  intro y hy
  by_contra h
  push_neg at h
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (x := (D y - c) / (B + 1)) (by positivity) hα1
  rw [lt_div_iff₀ (by linarith)] at hn
  have := key n y hy
  nlinarith [pow_nonneg hα0 n]

/-! ### Part 5: accessibility as a chain of demands -/

/-- `vw2_Chain M s y y'`: `y'` is reached from `y` by a sequence of demands in the support of
`φ`, every intermediate state being `≥ s` (no order placed). -/
inductive vw2_Chain (M : Model) (s : ℤ) : ℤ → ℤ → Prop
  | base {y : ℤ} {k : ℕ} (hk : M.φ k ≠ 0) : vw2_Chain M s y (y - k)
  | step {y y₁ : ℤ} {k : ℕ} (h : vw2_Chain M s y y₁) (hy₁ : s ≤ y₁) (hk : M.φ k ≠ 0) :
      vw2_Chain M s y (y₁ - k)

lemma vw2_Chain_le (M : Model) (s y y' : ℤ) (h : vw2_Chain M s y y') : y' ≤ y := by
  induction h with
  | base hk => omega
  | step h hy₁ hk ih => omega

lemma vw2_accessible_chain (M : Model) (s S : ℤ) (hs : s ≤ S) (t : ℕ) (ht : 1 ≤ t) (y : ℤ)
    (hy : stateLaw M s S S t y ≠ 0) : vw2_Chain M s S y := by
  induction t generalizing y with
  | zero => omega
  | succ t ih =>
    have hmem : y ∈ (stateLaw M s S S (t + 1)).support := (PMF.mem_support_iff _ _).2 hy
    simp only [stateLaw, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hmem
    obtain ⟨y', hy', k, hk, rfl⟩ := hmem
    have hk' : M.φ k ≠ 0 := (PMF.mem_support_iff _ _).1 hk
    rcases Nat.eq_zero_or_pos t with rfl | ht'
    · simp only [stateLaw, PMF.support_pure, Set.mem_singleton_iff] at hy'
      rw [hy']
      have : sSOrder s S S = S := by unfold sSOrder; simp [not_lt.2 hs]
      rw [this]
      exact vw2_Chain.base hk'
    · have hc := ih ht' y' ((PMF.mem_support_iff _ _).1 hy')
      by_cases hys : y' < s
      · have : sSOrder s S y' = S := by unfold sSOrder; simp [hys]
        rw [this]
        exact vw2_Chain.base hk'
      · push_neg at hys
        have : sSOrder s S y' = y' := by unfold sSOrder; simp [not_lt.2 hys]
        rw [this]
        exact vw2_Chain.step hc hys hk'

lemma vw2_Accessible_chain (M : Model) (s S y : ℤ) (hs : s ≤ S) (h : Accessible M s S S y) :
    vw2_Chain M s S y := by
  obtain ⟨t, ht, hy⟩ := h
  exact vw2_accessible_chain M s S hs t ht y hy

/-! ### Part 6: facts about `G`, `SLow`, `sHigh` -/

lemma vw2_incr_mono (M : Model) (a b : ℤ) (hab : a ≤ b) :
    M.G (a + 1) - M.G a ≤ M.G (b + 1) - M.G b := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, b = a + k := ⟨(b - a).toNat, by omega⟩
  induction k with
  | zero => simp
  | succ k ih =>
    have h := M.G_convex (a + k)
    have e1 : a + (k : ℤ) + 2 = a + ((k + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
    have e2 : a + (k : ℤ) + 1 = a + ((k + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e1, e2] at h
    rw [e2] at ih
    linarith [ih (by omega)]

lemma vw2_bdd_below (M : Model) (c : ℝ) : ∃ N : ℤ, ∀ y, M.G y ≤ c → N < y := by
  have := Filter.tendsto_atTop.1 M.G_tendsto_atBot (c + 1)
  obtain ⟨N, hN⟩ := Filter.eventually_atBot.1 this
  refine ⟨N, fun y hy => ?_⟩
  by_contra h
  have := hN y (by omega)
  linarith

lemma vw2_exists_min (M : Model) : ∃ m : ℤ, ∀ z, M.G m ≤ M.G z := by
  obtain ⟨N1, hN1⟩ := Filter.eventually_atBot.1 (Filter.tendsto_atTop.1 M.G_tendsto_atBot (M.G 0 + 1))
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.1 (Filter.tendsto_atTop.1 M.G_tendsto_atTop (M.G 0 + 1))
  obtain ⟨m, hm, hmin⟩ := (Finset.Icc (min N1 0) (max N2 0)).exists_min_image M.G
    ⟨0, by simp⟩
  refine ⟨m, fun z => ?_⟩
  have h0 : M.G m ≤ M.G 0 := hmin 0 (by simp)
  by_cases hz : z ∈ Finset.Icc (min N1 0) (max N2 0)
  · exact hmin z hz
  · simp only [Finset.mem_Icc, not_and_or, not_le] at hz
    rcases hz with hz | hz
    · have := hN1 z (by omega); linarith
    · have := hN2 z (by omega); linarith

lemma vw2_SLow_min (M : Model) : ∀ z, M.G (SLow M) ≤ M.G z := by
  obtain ⟨m, hm⟩ := vw2_exists_min M
  obtain ⟨N, hN⟩ := vw2_bdd_below M (M.G m)
  have hmem : SLow M ∈ {y : ℤ | ∀ z : ℤ, M.G y ≤ M.G z} :=
    Int.csInf_mem ⟨m, hm⟩ ⟨N, fun y hy => (hN y (hy m)).le⟩
  exact hmem

lemma vw2_anti (M : Model) (a b : ℤ) (hab : a ≤ b) (hb : b ≤ SLow M) : M.G b ≤ M.G a := by
  have hmin := vw2_SLow_min M
  have hd : ∀ y, y < SLow M → M.G (y + 1) - M.G y ≤ 0 := by
    intro y hy
    have := vw2_incr_mono M y (SLow M - 1) (by omega)
    have e : SLow M - 1 + 1 = SLow M := by ring
    rw [e] at this
    linarith [hmin (SLow M - 1)]
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, b = a + k := ⟨(b - a).toNat, by omega⟩
  induction k with
  | zero => simp
  | succ k ih =>
    have := hd (a + k) (by push_cast at hb; omega)
    have e : a + ((k + 1 : ℕ) : ℤ) = a + k + 1 := by push_cast; ring
    rw [e]
    linarith [ih (by push_cast at hb ⊢; omega) (by omega)]

lemma vw2_sHigh_le_SLow (M : Model) (α : ℝ) (hα₁ : α ≤ 1) : sHigh M α ≤ SLow M := by
  obtain ⟨N, hN⟩ := vw2_bdd_below M (M.G (SLow M) + (1 - α) * M.K)
  have hK := M.K_nonneg
  exact csInf_le ⟨N, fun y hy => (hN y hy).le⟩
    (show M.G (SLow M) ≤ M.G (SLow M) + (1 - α) * M.K by nlinarith)

/-! ### Part 7: termwise equality from equality of sums -/

lemma vw2_tsum_eq_termwise (M : Model) (a b : ℕ → ℝ)
    (hsa : Summable (fun k => (M.φ k).toReal * a k))
    (hsb : Summable (fun k => (M.φ k).toReal * b k))
    (hab : ∀ k, a k ≤ b k)
    (heq : ∑' k, (M.φ k).toReal * a k = ∑' k, (M.φ k).toReal * b k) :
    ∀ k, M.φ k ≠ 0 → a k = b k := by
  intro k hk
  have hs : Summable (fun k => (M.φ k).toReal * (b k - a k)) :=
    (hsb.sub hsa).congr (fun k => by ring)
  have h0 : ∑' k, (M.φ k).toReal * (b k - a k) = 0 := by
    rw [tsum_congr (fun k => by ring :
      ∀ k, (M.φ k).toReal * (b k - a k) = (M.φ k).toReal * b k - (M.φ k).toReal * a k),
      Summable.tsum_sub hsb hsa, heq, sub_self]
  have hle := hs.le_tsum k (fun j _ => mul_nonneg ENNReal.toReal_nonneg (sub_nonneg.2 (hab j)))
  rw [h0] at hle
  have hpos : 0 < (M.φ k).toReal := ENNReal.toReal_pos hk (PMF.apply_ne_top _ _)
  have := hab k
  nlinarith

lemma vw2_abs_sub_le (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [sub_eq_add_neg]
  exact (abs_add_le _ _).trans (by rw [abs_neg])

lemma vw2_tsum_le_term (M : Model) (c : ℕ → ℝ) (hs : Summable (fun k => (M.φ k).toReal * c k))
    (hneg : ∀ k, c k ≤ 0) (k : ℕ) :
    ∑' k', (M.φ k').toReal * c k' ≤ (M.φ k).toReal * c k := by
  have h := hs.neg.le_tsum k (fun j _ => by
    simp only [Pi.neg_apply, neg_nonneg]
    exact mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg (hneg j))
  rw [tsum_neg] at h
  simpa using h

/-! ### Part 8: Case A -- ordering at `σ` is at least as good as sitting -/

lemma vw2_order_better (M : Model) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (σ S : ℤ)
    (hσS : σ + 1 ≤ S)
    (hF : fCost M α σ S (σ - 1) ≤ fCost M α (σ + 1) S σ)
    (hchain : vw2_Chain M σ S σ) :
    fCost M α σ S σ ≤ fCost M α σ S (σ - 1) := by
  by_contra hcon
  push_neg at hcon
  have hα0' : 0 ≤ α := hα0.le
  have hσS' : σ ≤ S := by omega
  set F := fCost M α σ S (σ - 1) with hFdef
  set F' := fCost M α (σ + 1) S σ with hF'def
  let D : ℤ → ℝ := fun y => fCost M α (σ + 1) S y - fCost M α σ S y
  have hD1 : ∀ y, y < σ → D y = F' - F := by
    intro y hy
    simp only [D, hFdef, hF'def]
    rw [vw2_fCost_order_eq M α hα0' hα1 (σ + 1) S y σ hσS (by omega) (by omega),
      vw2_fCost_order_eq M α hα0' hα1 σ S y (σ - 1) hσS' hy (by omega)]
  have hD2 : D σ = F' - fCost M α σ S σ := rfl
  have htsub : ∀ y, ∑' k : ℕ, (M.φ k).toReal * D (y - k)
      = ∑' k : ℕ, (M.φ k).toReal * fCost M α (σ + 1) S (y - k)
        - ∑' k : ℕ, (M.φ k).toReal * fCost M α σ S (y - k) := by
    intro y
    have hs1 := vw2_summable_phi_fCost M α hα0' hα1 (σ + 1) S (max y S) y
      (le_max_right _ _) (le_max_left _ _)
    have hs2 := vw2_summable_phi_fCost M α hα0' hα1 σ S (max y S) y
      (le_max_right _ _) (le_max_left _ _)
    rw [← Summable.tsum_sub hs1 hs2]
    congr 1; ext k; simp only [D]; ring
  have hD3 : ∀ y, σ < y → D y = α * ∑' k : ℕ, (M.φ k).toReal * D (y - k) := by
    intro y hy
    simp only [D]
    rw [vw2_fCost_sit M α hα0' hα1 (σ + 1) S y (by omega),
      vw2_fCost_sit M α hα0' hα1 σ S y (by omega), htsub y]
    ring
  have hD4 : F' - F = α * ∑' k : ℕ, (M.φ k).toReal * D (S - k) := by
    have e1 := vw2_fCost_order M α hα0' hα1 (σ + 1) S σ hσS (by omega)
    have e2 := vw2_fCost_order M α hα0' hα1 σ S (σ - 1) hσS' (by omega)
    rw [htsub S, hF'def, hFdef, e1, e2]
    ring
  have hD5 : ∀ y, y ≤ S → |D y| ≤ vw2_Cb M (σ + 1) S S / (1 - α) + vw2_Cb M σ S S / (1 - α) := by
    intro y hy
    simp only [D]
    exact (vw2_abs_sub_le _ _).trans (add_le_add
      (vw2_abs_fCost_le M α hα0' hα1 (σ + 1) S S y le_rfl hy)
      (vw2_abs_fCost_le M α hα0' hα1 σ S S y le_rfl hy))
  set B := vw2_Cb M (σ + 1) S S / (1 - α) + vw2_Cb M σ S S / (1 - α)
  have ha : 0 ≤ F' - F := by linarith
  have hDle : ∀ y, y ≤ S → D y ≤ F' - F := by
    refine vw2_max_principle M α hα0' hα1 D S (σ + 1) (F' - F) B ha hD5 ?_ ?_
    · intro y hy hyσ
      rcases lt_or_eq_of_le (show y ≤ σ by omega) with h | h
      · rw [hD1 y h]
      · rw [h, hD2]; linarith
    · intro y hy hyσ; exact hD3 y (by omega)
  have hsD : Summable (fun k : ℕ => (M.φ k).toReal * D (S - k)) :=
    vw2_summable_phi_mul M _ B (fun k => hD5 _ (by omega))
  have ha0 : F' - F = 0 := by
    have : ∑' k : ℕ, (M.φ k).toReal * D (S - k) ≤ F' - F :=
      vw2_tsum_phi_mul_le' M _ _ hsD (fun k => hDle _ (by omega))
    nlinarith
  have hD0 : ∀ y, y ≤ S → D y ≤ 0 := fun y hy => by linarith [hDle y hy]
  have hb : D σ < 0 := by rw [hD2]; linarith
  have hchainneg : ∀ y₀ y₁, vw2_Chain M σ y₀ y₁ → y₀ = S → D y₁ < 0 →
      ∑' k : ℕ, (M.φ k).toReal * D (S - k) < 0 := by
    intro y₀ y₁ hc
    induction hc with
    | @base k hk =>
      intro hy0 hneg
      rw [hy0] at hneg
      have hterm : (M.φ k).toReal * D (S - k) < 0 :=
        mul_neg_of_pos_of_neg (ENNReal.toReal_pos hk (PMF.apply_ne_top _ _)) hneg
      have := vw2_tsum_le_term M (fun k : ℕ => D (S - k)) hsD (fun k => hD0 _ (by omega)) k
      linarith
    | @step y₁ k h hy₁ hk ih =>
      intro hy0 hneg
      apply ih hy0
      rcases eq_or_lt_of_le hy₁ with h' | h'
      · rw [← h']; exact hb
      · rw [hD3 _ h']
        have hy₁S : y₁ ≤ S := hy0 ▸ vw2_Chain_le M σ y₀ y₁ h
        have hs' : Summable (fun k' : ℕ => (M.φ k').toReal * D (y₁ - k')) :=
          vw2_summable_phi_mul M _ B (fun k' => hD5 _ (by omega))
        have hterm : (M.φ k).toReal * D (y₁ - k) < 0 :=
          mul_neg_of_pos_of_neg (ENNReal.toReal_pos hk (PMF.apply_ne_top _ _)) hneg
        have := vw2_tsum_le_term M (fun k' : ℕ => D (y₁ - k')) hs' (fun k' => hD0 _ (by omega)) k
        exact mul_neg_of_pos_of_neg hα0 (by linarith)
  have hneg := hchainneg S σ hchain rfl hb
  have := mul_neg_of_pos_of_neg hα0 hneg
  linarith

/-! ### Part 9: Case B -- propagation of equality along the chain of `j` -/

lemma vw2_caseB (M : Model) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (si Si sj Sj : ℤ)
    (hij : si < sj) (hjS : sj ≤ Sj) (hiS : si ≤ Si)
    (hF : fCost M α sj Sj (sj - 1) = fCost M α si Si (si - 1))
    (hopt : ∀ y, fCost M α si Si y ≤ fCost M α sj Sj y)
    (hFR : fCost M α sj Sj (sj - 1) ≤ fCost M α si Sj (si - 1)) :
    ∀ y₀ y, vw2_Chain M sj y₀ y → y₀ = Sj → fCost M α si Si y = fCost M α sj Sj y := by
  have hα0' : 0 ≤ α := hα0.le
  have hsiSj : si ≤ Sj := by omega
  set F := fCost M α sj Sj (sj - 1) with hFdef
  set FR := fCost M α si Sj (si - 1) with hFRdef
  set Mx := max Si Sj with hMx
  have hSi : Si ≤ Mx := le_max_left _ _
  have hSj : Sj ≤ Mx := le_max_right _ _
  have hsj : Summable (fun k : ℕ => (M.φ k).toReal * fCost M α sj Sj (Sj - k)) :=
    vw2_summable_phi_fCost M α hα0' hα1 sj Sj Mx Sj hSj hSj
  have hsi : Summable (fun k : ℕ => (M.φ k).toReal * fCost M α si Si (Sj - k)) :=
    vw2_summable_phi_fCost M α hα0' hα1 si Si Mx Sj hSi hSj
  have hsR : Summable (fun k : ℕ => (M.φ k).toReal * fCost M α si Sj (Sj - k)) :=
    vw2_summable_phi_fCost M α hα0' hα1 si Sj Mx Sj hSj hSj
  have eF : F = M.K + M.G Sj + α * ∑' k : ℕ, (M.φ k).toReal * fCost M α sj Sj (Sj - k) :=
    vw2_fCost_order M α hα0' hα1 sj Sj (sj - 1) hjS (by omega)
  have eFR : FR = M.K + M.G Sj + α * ∑' k : ℕ, (M.φ k).toReal * fCost M α si Sj (Sj - k) :=
    vw2_fCost_order M α hα0' hα1 si Sj (si - 1) hsiSj (by omega)
  set H := M.K + M.G Sj + α * ∑' k : ℕ, (M.φ k).toReal * fCost M α si Si (Sj - k) with hHdef
  have hHF : H ≤ F := by
    rw [eF]
    have := Summable.tsum_le_tsum (fun k : ℕ => mul_le_mul_of_nonneg_left (hopt (Sj - k))
      ENNReal.toReal_nonneg) hsi hsj
    nlinarith
  -- the difference between `R = (si, Sj)` and `i = (si, Si)`
  let D : ℤ → ℝ := fun y => fCost M α si Sj y - fCost M α si Si y
  have hD1 : ∀ y, y < si → D y = FR - F := by
    intro y hy
    simp only [D, hFRdef]
    rw [vw2_fCost_order_eq M α hα0' hα1 si Sj y (si - 1) hsiSj hy (by omega),
      vw2_fCost_order_eq M α hα0' hα1 si Si y (si - 1) hiS hy (by omega), hF]
  have htsub : ∀ y, ∑' k : ℕ, (M.φ k).toReal * D (y - k)
      = ∑' k : ℕ, (M.φ k).toReal * fCost M α si Sj (y - k)
        - ∑' k : ℕ, (M.φ k).toReal * fCost M α si Si (y - k) := by
    intro y
    have hs1 := vw2_summable_phi_fCost M α hα0' hα1 si Sj (max y Mx) y
      (le_trans hSj (le_max_right _ _)) (le_max_left _ _)
    have hs2 := vw2_summable_phi_fCost M α hα0' hα1 si Si (max y Mx) y
      (le_trans hSi (le_max_right _ _)) (le_max_left _ _)
    rw [← Summable.tsum_sub hs1 hs2]
    congr 1; ext k; simp only [D]; ring
  have hD3 : ∀ y, si ≤ y → D y = α * ∑' k : ℕ, (M.φ k).toReal * D (y - k) := by
    intro y hy
    simp only [D]
    rw [vw2_fCost_sit M α hα0' hα1 si Sj y hy, vw2_fCost_sit M α hα0' hα1 si Si y hy, htsub y]
    ring
  have hD5 : ∀ y, y ≤ Mx → |D y| ≤ vw2_Cb M si Sj Mx / (1 - α) + vw2_Cb M si Si Mx / (1 - α) := by
    intro y hy
    simp only [D]
    exact (vw2_abs_sub_le _ _).trans (add_le_add
      (vw2_abs_fCost_le M α hα0' hα1 si Sj Mx y hSj hy)
      (vw2_abs_fCost_le M α hα0' hα1 si Si Mx y hSi hy))
  set B := vw2_Cb M si Sj Mx / (1 - α) + vw2_Cb M si Si Mx / (1 - α)
  have hc : 0 ≤ FR - F := by linarith
  have hDle : ∀ y, y ≤ Mx → D y ≤ FR - F :=
    vw2_max_principle M α hα0' hα1 D Mx si (FR - F) B hc hD5
      (fun y _ hys => by rw [hD1 y hys]) (fun y _ hys => hD3 y hys)
  have hsD : Summable (fun k : ℕ => (M.φ k).toReal * D (Sj - k)) :=
    vw2_summable_phi_mul M _ B (fun k => hD5 _ (by omega))
  have hsum_le : ∑' k : ℕ, (M.φ k).toReal * D (Sj - k) ≤ FR - F :=
    vw2_tsum_phi_mul_le' M _ _ hsD (fun k => hDle _ (by omega))
  have eFR' : FR = H + α * ∑' k : ℕ, (M.φ k).toReal * D (Sj - k) := by
    rw [htsub Sj, eFR, hHdef]; ring
  have hFH : F ≤ H := by nlinarith
  have hHF' : H = F := le_antisymm hHF hFH
  -- termwise equality at the states `Sj - k`
  have hbase : ∀ k, M.φ k ≠ 0 → fCost M α si Si (Sj - k) = fCost M α sj Sj (Sj - k) := by
    apply vw2_tsum_eq_termwise M _ _ hsi hsj (fun k => hopt _)
    have h1 : α * ∑' k : ℕ, (M.φ k).toReal * fCost M α si Si (Sj - k)
        = α * ∑' k : ℕ, (M.φ k).toReal * fCost M α sj Sj (Sj - k) := by
      have := hHF'
      rw [hHdef, eF] at this
      linarith
    exact mul_left_cancel₀ hα0.ne' h1
  -- propagation
  intro y₀ y hc
  induction hc with
  | @base k hk =>
    intro hy0; rw [hy0]; exact hbase k hk
  | @step y₁ k h hy₁ hk ih =>
    intro hy0
    have heq := ih hy0
    have e1 := vw2_fCost_sit M α hα0' hα1 si Si y₁ (by omega)
    have e2 := vw2_fCost_sit M α hα0' hα1 sj Sj y₁ hy₁
    have hs1 := vw2_summable_phi_fCost M α hα0' hα1 si Si (max y₁ Si) y₁
      (le_max_right _ _) (le_max_left _ _)
    have hs2 := vw2_summable_phi_fCost M α hα0' hα1 sj Sj (max y₁ Sj) y₁
      (le_max_right _ _) (le_max_left _ _)
    refine vw2_tsum_eq_termwise M _ _ hs1 hs2 (fun k => hopt _) ?_ k hk
    have h1 : α * ∑' k : ℕ, (M.φ k).toReal * fCost M α si Si (y₁ - k)
        = α * ∑' k : ℕ, (M.φ k).toReal * fCost M α sj Sj (y₁ - k) := by linarith
    exact mul_left_cancel₀ hα0.ne' h1

/-! ### Part 10: the sum of `φ (k+1)` and the main theorem -/

lemma vw2_tsum_phi_shift (M : Model) : ∑' k : ℕ, (M.φ (k + 1)).toReal = 1 - (M.φ 0).toReal := by
  have h := (vw2_summable_phi M).tsum_eq_zero_add
  rw [vw2_tsum_phi] at h
  linarith

/-- The tail sum `∑_{k ≥ 1} φ_k f(x - k)` when all `f (x - k) ≤ F` for `k ≥ 1`. -/
lemma vw2_tail_le (M : Model) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) (s S x : ℤ) (F : ℝ)
    (hs : Summable (fun k : ℕ => (M.φ k).toReal * fCost M α s S (x - k)))
    (hb : ∀ k : ℕ, fCost M α s S (x - ((k + 1 : ℕ) : ℤ)) ≤ F) :
    ∑' k : ℕ, (M.φ (k + 1)).toReal * fCost M α s S (x - ((k + 1 : ℕ) : ℤ))
      ≤ (1 - (M.φ 0).toReal) * F := by
  calc ∑' k : ℕ, (M.φ (k + 1)).toReal * fCost M α s S (x - ((k + 1 : ℕ) : ℤ))
      ≤ ∑' k : ℕ, (M.φ (k + 1)).toReal * F :=
        Summable.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_left (hb k) ENNReal.toReal_nonneg)
          ((summable_nat_add_iff 1).2 hs)
          (((summable_nat_add_iff 1).2 (vw2_summable_phi M)).mul_right F)
    _ = (1 - (M.φ 0).toReal) * F := by rw [tsum_mul_right, vw2_tsum_phi_shift]

theorem vw2_theorem2_core (M : Model) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (pi pj : ℤ × ℤ) (hpi : pi ∈ candSet M α) (hpj : pj ∈ candSet M α)
    (hopt : Optimal M α pi.1 pi.2)
    (hacc : ∀ x' : ℤ, min pi.1 pj.1 ≤ x' → x' < max pi.1 pj.1 →
      Accessible M pj.1 pj.2 pj.2 x') :
    Optimal M α pj.1 pj.2 := by
  obtain ⟨si, Si⟩ := pi
  obtain ⟨sj, Sj⟩ := pj
  simp only at hopt hacc ⊢
  have hα0' : 0 ≤ α := hα0.le
  have h1α : 0 < 1 - α := by linarith
  obtain ⟨hbi, hci⟩ := hpi
  obtain ⟨hbj, hcj⟩ := hpj
  simp only [Box, Set.mem_ofPred_eq] at hbi hbj
  obtain ⟨hsi1, hsi2, hSi1, hSi2, hsiSi⟩ := hbi
  obtain ⟨hsj1, hsj2, hSj1, hSj2, hsjSj⟩ := hbj
  have hsHigh : sHigh M α ≤ SLow M := vw2_sHigh_le_SLow M α hα1.le
  have hcalL : ∀ s S : ℤ, calL M α S (S - s) = (1 - α) * fCost M α s S (s - 1) := by
    intro s S
    unfold calL aCost
    have e1 : S - (S - s) = s := by ring
    rw [e1]
  have hFji : fCost M α sj Sj (sj - 1) = fCost M α si Si (si - 1) := by
    have h1 := hcj (si, Si) (by simp only [Box, Set.mem_ofPred_eq]; exact ⟨hsi1, hsi2, hSi1, hSi2, hsiSi⟩)
    have h2 := hci (sj, Sj) (by simp only [Box, Set.mem_ofPred_eq]; exact ⟨hsj1, hsj2, hSj1, hSj2, hsjSj⟩)
    simp only at h1 h2
    rw [hcalL, hcalL] at h1 h2
    exact le_antisymm (le_of_mul_le_mul_left h1 h1α) (le_of_mul_le_mul_left h2 h1α)
  have hoptf : ∀ y, fCost M α si Si y ≤ fCost M α sj Sj y := by
    intro y
    have := hopt.2 y (Set.mem_univ _) sj Sj hsjSj
    unfold aCost at this
    exact le_of_mul_le_mul_left this h1α
  -- the middle range
  have hmid : ∀ x, min si sj ≤ x → x < max si sj → fCost M α sj Sj x ≤ fCost M α si Si x := by
    intro x hx1 hx2
    rcases lt_trichotomy sj si with h | h | h
    · -- case A : sj < si
      have hx1' : sj ≤ x := by omega
      have hx2' : x < si := by omega
      have hsiSj : si ≤ Sj := le_trans hsi2 (le_trans hsHigh hSj1)
      have hFle : fCost M α sj Sj (sj - 1) ≤ fCost M α (sj + 1) Sj sj := by
        have h1 := hcj (sj + 1, Sj) (by
          simp only [Box, Set.mem_ofPred_eq]
          exact ⟨by omega, by omega, hSj1, hSj2, by omega⟩)
        simp only at h1
        rw [hcalL, hcalL] at h1
        have e : sj + 1 - 1 = sj := by ring
        rw [e] at h1
        exact le_of_mul_le_mul_left h1 h1α
      have hchain := vw2_Accessible_chain M sj Sj sj hsjSj (hacc sj (by omega) (by omega))
      have hob := vw2_order_better M α hα0 hα1 sj Sj (by omega) hFle hchain
      have hφ := vw2_phi0_lt M α hα0' hα1
      have hφ0 : 0 ≤ (M.φ 0).toReal := ENNReal.toReal_nonneg
      have hGsj : M.G sj ≤ (1 - α) * fCost M α sj Sj (sj - 1) := by
        have e1 := vw2_fCost_sit M α hα0' hα1 sj Sj sj le_rfl
        have hs := vw2_summable_phi_fCost M α hα0' hα1 sj Sj Sj sj le_rfl hsjSj
        rw [hs.tsum_eq_zero_add] at e1
        simp only [Nat.cast_zero, sub_zero] at e1
        have e2 : ∑' k : ℕ, (M.φ (k + 1)).toReal * fCost M α sj Sj (sj - ((k + 1 : ℕ) : ℤ))
            = (1 - (M.φ 0).toReal) * fCost M α sj Sj (sj - 1) := by
          have : ∀ k : ℕ, fCost M α sj Sj (sj - ((k + 1 : ℕ) : ℤ)) = fCost M α sj Sj (sj - 1) :=
            fun k => vw2_fCost_order_eq M α hα0' hα1 sj Sj _ _ hsjSj (by push_cast; omega) (by omega)
          simp only [this]
          rw [tsum_mul_right, vw2_tsum_phi_shift]
        rw [e2] at e1
        nlinarith [mul_le_mul_of_nonneg_left hob (by nlinarith : (0:ℝ) ≤ 1 - α * (M.φ 0).toReal)]
      have hind : ∀ n : ℕ, ∀ x, sj ≤ x → x < si → x < sj + n →
          fCost M α sj Sj x ≤ fCost M α sj Sj (sj - 1) := by
        intro n
        induction n with
        | zero => intro x _ _ h; omega
        | succ n ih =>
          intro x hx1 hx2 hx3
          have e1 := vw2_fCost_sit M α hα0' hα1 sj Sj x hx1
          have hs := vw2_summable_phi_fCost M α hα0' hα1 sj Sj (max x Sj) x
            (le_max_right _ _) (le_max_left _ _)
          rw [hs.tsum_eq_zero_add] at e1
          simp only [Nat.cast_zero, sub_zero] at e1
          have hle := vw2_tail_le M α hα0' hα1 sj Sj x (fCost M α sj Sj (sj - 1)) hs (by
            intro k
            by_cases hxk : x - ((k + 1 : ℕ) : ℤ) < sj
            · rw [vw2_fCost_order_eq M α hα0' hα1 sj Sj (x - ((k + 1 : ℕ) : ℤ)) (sj - 1) hsjSj hxk
                (by omega)]
            · push_neg at hxk
              exact ih _ hxk (by push_cast at hxk ⊢; omega) (by push_cast at hxk ⊢; omega))
          have hG : M.G x ≤ M.G sj := vw2_anti M sj x hx1 (by omega)
          nlinarith
      have := hind (si - sj).toNat x hx1' hx2' (by omega)
      rw [vw2_fCost_order_eq M α hα0' hα1 si Si x (si - 1) hsiSi hx2' (by omega), ← hFji]
      exact this
    · omega
    · -- case B : si < sj
      have hFR : fCost M α sj Sj (sj - 1) ≤ fCost M α si Sj (si - 1) := by
        have h1 := hcj (si, Sj) (by
          simp only [Box, Set.mem_ofPred_eq]
          exact ⟨hsi1, hsi2, hSj1, hSj2, by omega⟩)
        simp only at h1
        rw [hcalL, hcalL] at h1
        exact le_of_mul_le_mul_left h1 h1α
      have hB := vw2_caseB M α hα0 hα1 si Si sj Sj h hsjSj hsiSi hFji hoptf hFR
      have hchain := vw2_Accessible_chain M sj Sj x hsjSj (hacc x (by omega) (by omega))
      exact (hB Sj x hchain rfl).ge
  -- below the minimum
  have hlow : ∀ x, x < min si sj → fCost M α sj Sj x ≤ fCost M α si Si x := by
    intro x hx
    rw [vw2_fCost_order_eq M α hα0' hα1 sj Sj x (sj - 1) hsjSj (by omega) (by omega),
      vw2_fCost_order_eq M α hα0' hα1 si Si x (si - 1) hsiSi (by omega) (by omega), hFji]
  -- above the maximum
  have hup : ∀ n : ℕ, ∀ x, x < max si sj + n → fCost M α sj Sj x ≤ fCost M α si Si x := by
    intro n
    induction n with
    | zero =>
      intro x hx
      simp only [Nat.cast_zero, add_zero] at hx
      rcases lt_or_ge x (min si sj) with h | h
      · exact hlow x h
      · exact hmid x h hx
    | succ n ih =>
      intro x hx
      by_cases hx' : x < max si sj + n
      · exact ih x hx'
      · push_neg at hx'
        apply vw2_sit_compare M α hα0' hα1 si Si sj Sj x (by omega) (by omega)
        intro k hk
        apply ih
        push_cast at hx ⊢
        omega
  have key : ∀ x, fCost M α sj Sj x ≤ fCost M α si Si x := fun x =>
    hup (x - max si sj + 1).toNat x (by omega)
  refine ⟨hsjSj, fun x _ s S hsS => ?_⟩
  have h1 := hopt.2 x (Set.mem_univ _) s S hsS
  unfold aCost at h1 ⊢
  have := mul_le_mul_of_nonneg_left (key x) h1α.le
  linarith

end VeinottWagnerSS.Selection

open VeinottWagnerSS.Selection


theorem solution (M : Model) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (pi pj : ℤ × ℤ) (hpi : pi ∈ candSet M α) (hpj : pj ∈ candSet M α)
    (hopt : Optimal M α pi.1 pi.2)
    (hacc : ∀ x' : ℤ, min pi.1 pj.1 ≤ x' → x' < max pi.1 pj.1 →
      Accessible M pj.1 pj.2 pj.2 x') :
    Optimal M α pj.1 pj.2 := by
  exact vw2_theorem2_core M α hα0 hα1 pi pj hpi hpj hopt hacc
