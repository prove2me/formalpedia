-- Prove2me | solution 1 for SubsetShrink.Events.prob_F_weak
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T01:17:21.692667+00:00
-- url     : https://prove2.me/submissions/1b124981-35d3-4093-9d5f-7753eed48bca

import Mathlib
import Definitions.Def_SubsetShrink_Events_Model
import Theorems.Thm_GaussianMatrix_gaussian_concentration_vector

open MeasureTheory ProbabilityTheory

namespace BICFweak

open SubsetShrink.Events

/-- The standard Gaussian product measure on `ℝⁿ`. -/
noncomputable abbrev γ (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => gaussianReal 0 1)

lemma γ_prob (n : ℕ) : IsProbabilityMeasure (γ n) := inferInstance

lemma noiseLaw_prob (n : ℕ) (σ : ℝ) : IsProbabilityMeasure (noiseLaw n σ) := by
  unfold noiseLaw
  have hv : ∀ v : NNReal, IsProbabilityMeasure (Measure.pi (fun _ : Fin n => gaussianReal 0 v)) :=
    fun v => inferInstance
  exact hv ⟨σ ^ 2, sq_nonneg σ⟩

/-- `noiseLaw n σ` is the image of the standard Gaussian under `z ↦ σ z`. -/
lemma noiseLaw_eq_map (n : ℕ) (σ : ℝ) :
    noiseLaw n σ = (γ n).map (fun z i => σ * z i) := by
  unfold noiseLaw γ
  rw [Measure.pi_map_pi (fun i => (measurable_const_mul σ).aemeasurable)]
  congr 1
  funext i
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · ext; simp; rfl

lemma dot_le_l2 {n : ℕ} (a b : Fin n → ℝ) : dot a b ≤ l2 a * l2 b := by
  unfold dot l2
  rw [← Real.sqrt_mul (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  calc ∑ i, a i * b i ≤ |∑ i, a i * b i| := le_abs_self _
    _ = Real.sqrt ((∑ i, a i * b i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ _ := Real.sqrt_le_sqrt cs

lemma dot_sub_left {n : ℕ} (a b c : Fin n → ℝ) : dot (a - b) c = dot a c - dot b c := by
  unfold dot; rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _
  simp only [Pi.sub_apply]; ring

lemma dot_smul_right {n : ℕ} (a b : Fin n → ℝ) (c : ℝ) : dot a (c • b) = c * dot a b := by
  unfold dot; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
  simp only [Pi.smul_apply, smul_eq_mul]; ring

lemma dot_smul_left {n : ℕ} (a b : Fin n → ℝ) (c : ℝ) : dot (fun i => c * a i) b = c * dot a b := by
  unfold dot; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring

lemma l2_smul {n : ℕ} (a : Fin n → ℝ) (c : ℝ) : l2 (c • a) = |c| * l2 a := by
  unfold l2
  have : ∑ i, (c • a) i ^ 2 = c ^ 2 * ∑ i, a i ^ 2 := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [this, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

lemma l2_eq_zero {n : ℕ} (a : Fin n → ℝ) (h : l2 a = 0) : a = 0 := by
  unfold l2 at h
  rw [Real.sqrt_eq_zero (Finset.sum_nonneg (fun i _ => sq_nonneg _))] at h
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)] at h
  funext i
  have := h i (Finset.mem_univ i)
  simpa using this

lemma sortedSum_nonneg {p : ℕ} (u : Fin p → ℝ) : 0 ≤ sortedSum u := by
  unfold sortedSum
  refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ (1 : Equiv.Perm (Fin p))))
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))

lemma sortedSum_smul_le {p : ℕ} (u : Fin p → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    sortedSum (c • u) ≤ c * sortedSum u := by
  unfold sortedSum
  apply Finset.sup'_le
  intro π _
  have := Finset.le_sup' (fun π : Equiv.Perm (Fin p) =>
    ∑ j : Fin p, |u (π j)| * Real.sqrt (Real.log (2 * (p : ℝ) / ((j.val : ℝ) + 1))))
    (Finset.mem_univ π)
  calc ∑ j : Fin p, |(c • u) (π j)| * Real.sqrt (Real.log (2 * (p : ℝ) / ((j.val : ℝ) + 1)))
      = c * ∑ j : Fin p, |u (π j)| * Real.sqrt (Real.log (2 * (p : ℝ) / ((j.val : ℝ) + 1))) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
        simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hc]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left this hc

lemma abs_dot_le_l2 {n : ℕ} (a b : Fin n → ℝ) : |dot a b| ≤ l2 a * l2 b := by
  unfold dot l2
  rw [← Real.sqrt_mul (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt cs

lemma integrable_id_g : Integrable id (gaussianReal 0 1) :=
  memLp_one_iff_integrable.mp (by simpa using memLp_id_gaussianReal (μ := 0) (v := 1) 1)

lemma integral_coord (n : ℕ) (i : Fin n) : ∫ z, z i ∂(γ n) = 0 := by
  unfold γ
  rw [integral_eval]
  simp [integral_id_gaussianReal]

lemma integral_lin (n : ℕ) (a : Fin n → ℝ) : ∫ z, ∑ i, a i * z i ∂(γ n) = 0 := by
  rw [integral_finset_sum]
  · apply Finset.sum_eq_zero; intro i _
    rw [integral_const_mul, integral_coord, mul_zero]
  · intro i _
    exact (integrable_eval integrable_id_g).const_mul _

/-- Gaussian tail for a unit linear functional of a standard Gaussian vector. -/
lemma lin_tail {n : ℕ} (a : Fin n → ℝ) (ha : ∑ i, a i ^ 2 = 1) (t : ℝ) (ht : 0 ≤ t) :
    γ n {z | t ≤ |∑ i, a i * z i|} ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / 2)) := by
  have hl2a : l2 a = 1 := by unfold l2; rw [ha, Real.sqrt_one]
  have hlip : ∀ x y : Fin n → ℝ, |(∑ i, a i * x i) - (∑ i, a i * y i)| ≤
      1 * Real.sqrt (∑ i, (x i - y i) ^ 2) := by
    intro x y
    have := abs_dot_le_l2 a (x - y)
    rw [hl2a] at this
    unfold dot l2 at this
    convert this using 2
    · rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _
      simp only [Pi.sub_apply]; ring
    · rfl
  have hlip' : ∀ x y : Fin n → ℝ, |(-∑ i, a i * x i) - (-∑ i, a i * y i)| ≤
      1 * Real.sqrt (∑ i, (x i - y i) ^ 2) := by
    intro x y
    have := hlip x y
    rw [show (-∑ i, a i * x i) - (-∑ i, a i * y i) = -((∑ i, a i * x i) - (∑ i, a i * y i)) by ring,
      abs_neg]
    exact this
  have c1 := (GaussianMatrix.gaussian_concentration_vector (fun z : Fin n → ℝ => ∑ i, a i * z i)
    1 one_pos hlip t ht).2
  have c2 := (GaussianMatrix.gaussian_concentration_vector (fun z : Fin n → ℝ => -∑ i, a i * z i)
    1 one_pos hlip' t ht).2
  have m1 : ∫ y, ∑ i, a i * y i ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) = 0 :=
    integral_lin n a
  have m2 : ∫ y, -∑ i, a i * y i ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) = 0 := by
    rw [integral_neg, m1, neg_zero]
  rw [m1] at c1
  rw [m2] at c2
  simp only [zero_add, one_mul] at c1 c2
  calc γ n {z | t ≤ |∑ i, a i * z i|}
      ≤ γ n ({z | t ≤ ∑ i, a i * z i} ∪ {z | t ≤ -∑ i, a i * z i}) := by
        apply measure_mono
        intro z hz
        simp only [Set.mem_ofPred_eq] at hz
        simp only [Set.mem_union, Set.mem_ofPred_eq]
        rcases le_or_gt 0 (∑ i, a i * z i) with h | h
        · left; rwa [abs_of_nonneg h] at hz
        · right; rwa [abs_of_neg h] at hz
    _ ≤ γ n {z | t ≤ ∑ i, a i * z i} + γ n {z | t ≤ -∑ i, a i * z i} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / 2)) + ENNReal.ofReal (Real.exp (-t ^ 2 / 2)) :=
        add_le_add c1 c2
    _ = ENNReal.ofReal (2 * Real.exp (-t ^ 2 / 2)) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]; ring_nf

/-- The `j`-th column functional `z ↦ (Xᵀz)_j`. -/
def col {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (j : Fin p) (z : Fin n → ℝ) : ℝ :=
  ∑ i, X i j * z i

lemma dot_mulVec_eq {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (z : Fin n → ℝ) (u : Fin p → ℝ) :
    dot z (X.mulVec u) = ∑ j, u j * col X j z := by
  unfold dot col Matrix.mulVec dotProduct
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro i _
  ring

/-- Number of columns whose functional exceeds `τ` in absolute value. -/
noncomputable def cnt {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (τ : ℝ) (z : Fin n → ℝ) : ℕ :=
  (Finset.univ.filter (fun j => τ < |col X j z|)).card

/-- Dyadic thresholds `τ_l = √(6 log(2p/2^l))`. -/
noncomputable def tau (p l : ℕ) : ℝ := Real.sqrt (6 * Real.log (2 * p / 2 ^ l))

/-- Deterministic step: if the dyadic counts are small, the sorted-sum bound holds. -/
lemma sorted_bound_of_counts {n p : ℕ} (hp : 1 ≤ p) (X : Matrix (Fin n) (Fin p) ℝ)
    (z : Fin n → ℝ) (hc : ∀ l ∈ Finset.range (Nat.log 2 p + 1), cnt X (tau p l) z < 2 ^ l)
    (u : Fin p → ℝ) :
    dot z (X.mulVec u) ≤ Real.sqrt 12 * sortedSum u := by
  set g : Fin p → ℝ := fun j => col X j z with hg
  set π := Tuple.sort (fun j => -|g j|) with hπ
  have hmono : Monotone ((fun j => -|g j|) ∘ π) := Tuple.monotone_sort _
  have hanti : ∀ k k' : Fin p, k ≤ k' → |g (π k')| ≤ |g (π k)| := by
    intro k k' hkk
    have := hmono hkk
    simp only [Function.comp] at this
    linarith
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have key : ∀ k : Fin p, |g (π k)| ≤
      Real.sqrt 12 * Real.sqrt (Real.log (2 * (p : ℝ) / ((k.val : ℝ) + 1))) := by
    intro k
    set m := k.val + 1 with hm
    have hm0 : m ≠ 0 := by omega
    have hmp : m ≤ p := by have := k.isLt; omega
    set l := Nat.log 2 m with hl
    have h2l : 2 ^ l ≤ m := Nat.pow_log_le_self 2 hm0
    have h2l' : m < 2 ^ (l + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
    have hlp : l ≤ Nat.log 2 p := Nat.log_mono_right hmp
    have hpos : 1 ≤ 2 ^ l := Nat.one_le_two_pow
    let k0 : Fin p := ⟨2 ^ l - 1, by omega⟩
    have hk0 : k0 ≤ k := by
      show 2 ^ l - 1 ≤ k.val; omega
    have hk0τ : |g (π k0)| ≤ tau p l := by
      by_contra hcon
      push Not at hcon
      have hsub : (Finset.Iic k0).image π ⊆
          Finset.univ.filter (fun j => tau p l < |col X j z|) := by
        intro j hj
        rw [Finset.mem_image] at hj
        obtain ⟨k', hk', rfl⟩ := hj
        rw [Finset.mem_Iic] at hk'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact lt_of_lt_of_le hcon (hanti k' k0 hk')
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ π.injective] at hcard
      have : (Finset.Iic k0).card = 2 ^ l := by
        rw [Fin.card_Iic]; show 2 ^ l - 1 + 1 = 2 ^ l; omega
      rw [this] at hcard
      have := hc l (Finset.mem_range.mpr (by omega))
      unfold cnt at this
      omega
    have hm' : ((k.val : ℝ) + 1) = (m : ℝ) := by rw [hm]; push_cast; ring
    rw [hm']
    have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
    have h2lR : (0 : ℝ) < 2 ^ l := by positivity
    have hlog : Real.log (2 * p / 2 ^ l) ≤ 2 * Real.log (2 * p / m) := by
      rw [← Real.log_rpow (by positivity)]
      apply Real.log_le_log (by positivity)
      rw [show ((2 * (p : ℝ) / m) ^ (2 : ℝ)) = (2 * p / m) ^ 2 by norm_cast]
      rw [div_pow, div_le_div_iff₀ h2lR (by positivity)]
      have a1 : (m : ℝ) < 2 * 2 ^ l := by
        have : (m : ℝ) < ((2 ^ (l + 1) : ℕ) : ℝ) := by exact_mod_cast h2l'
        rw [pow_succ] at this; push_cast at this; linarith
      have a2 : (m : ℝ) ≤ p := by exact_mod_cast hmp
      have a3 : (m : ℝ) * m ≤ (2 * 2 ^ l) * p := mul_le_mul a1.le a2 hmR.le (by positivity)
      have a4 : 2 * (p : ℝ) * ((m : ℝ) * m) ≤ 2 * p * ((2 * 2 ^ l) * p) :=
        mul_le_mul_of_nonneg_left a3 (by positivity)
      nlinarith
    calc |g (π k)| ≤ |g (π k0)| := hanti k0 k hk0
      _ ≤ tau p l := hk0τ
      _ = Real.sqrt (6 * Real.log (2 * p / 2 ^ l)) := rfl
      _ ≤ Real.sqrt (12 * Real.log (2 * p / m)) := Real.sqrt_le_sqrt (by linarith)
      _ = Real.sqrt 12 * Real.sqrt (Real.log (2 * p / m)) := Real.sqrt_mul (by norm_num) _
  rw [dot_mulVec_eq]
  have hss := Finset.le_sup' (fun π : Equiv.Perm (Fin p) =>
    ∑ j : Fin p, |u (π j)| * Real.sqrt (Real.log (2 * (p : ℝ) / ((j.val : ℝ) + 1))))
    (Finset.mem_univ π)
  calc ∑ j, u j * col X j z ≤ ∑ j, |u j| * |g j| := by
        apply Finset.sum_le_sum; intro j _
        rw [← abs_mul]; exact le_abs_self _
    _ = ∑ k, |u (π k)| * |g (π k)| := (Equiv.sum_comp π (fun j => |u j| * |g j|)).symm
    _ ≤ ∑ k, |u (π k)| * (Real.sqrt 12 *
          Real.sqrt (Real.log (2 * (p : ℝ) / ((k.val : ℝ) + 1)))) := by
        apply Finset.sum_le_sum; intro k _
        exact mul_le_mul_of_nonneg_left (key k) (abs_nonneg _)
    _ = Real.sqrt 12 * ∑ k, |u (π k)| *
          Real.sqrt (Real.log (2 * (p : ℝ) / ((k.val : ℝ) + 1))) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
    _ ≤ Real.sqrt 12 * sortedSum u := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        exact hss

lemma measurable_col {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (j : Fin p) :
    Measurable (col X j) := by
  unfold col; fun_prop

lemma continuous_dot_left {n : ℕ} (v : Fin n → ℝ) : Continuous (fun z : Fin n → ℝ => dot z v) := by
  unfold dot; fun_prop

lemma tail_count {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (hX : UnitCols X) (l : ℕ)
    (hl : 2 ^ l ≤ p) :
    γ n {z | 2 ^ l ≤ cnt X (tau p l) z} ≤ ENNReal.ofReal (((2 : ℝ) ^ l / (2 * p)) ^ 2) := by
  have hp : 1 ≤ p := le_trans Nat.one_le_two_pow hl
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h2l : (0 : ℝ) < 2 ^ l := by positivity
  have hlp : (2 : ℝ) ^ l ≤ p := by exact_mod_cast hl
  set τ := tau p l with hτ
  set r : ℝ := 2 * p / 2 ^ l with hr
  have hr1 : 1 ≤ r := by rw [hr, le_div_iff₀ h2l]; linarith
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr1
  have hτ0 : 0 ≤ τ := Real.sqrt_nonneg _
  have hτ2 : τ ^ 2 = 6 * Real.log r := Real.sq_sqrt (by linarith)
  have hexp : Real.exp (-τ ^ 2 / 2) = (1 / r) ^ 3 := by
    rw [hτ2, show -(6 * Real.log r) / 2 = (3 : ℕ) * (-Real.log r) by push_cast; ring,
      Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by linarith), one_div]
  -- the sets
  let S : Fin p → Set (Fin n → ℝ) := fun j => {z | τ < |col X j z|}
  have hS : ∀ j, MeasurableSet (S j) := fun j =>
    measurableSet_lt measurable_const ((measurable_col X j).abs)
  let N : (Fin n → ℝ) → ENNReal := fun z => ∑ j, (S j).indicator 1 z
  have hN : ∀ z, (cnt X τ z : ENNReal) = N z := by
    intro z
    simp only [N, cnt, S, Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
    rw [Finset.sum_boole]
    try simp
  have hNm : AEMeasurable N (γ n) := by
    apply Measurable.aemeasurable
    exact Finset.measurable_sum _ (fun j _ => (measurable_one.indicator (hS j)))
  have hint : ∫⁻ z, N z ∂(γ n) = ∑ j, γ n (S j) := by
    simp only [N]
    rw [lintegral_finsetSum _ (fun j _ => measurable_one.indicator (hS j))]
    apply Finset.sum_congr rfl; intro j _
    exact lintegral_indicator_one (hS j)
  have hSj : ∀ j, γ n (S j) ≤ ENNReal.ofReal (2 * (1 / r) ^ 3) := by
    intro j
    rw [← hexp]
    refine le_trans (measure_mono ?_) (lin_tail (fun i => X i j) (hX j) τ hτ0)
    intro z hz
    simp only [S, Set.mem_ofPred_eq] at hz
    simp only [Set.mem_ofPred_eq]
    exact hz.le
  have hsum : ∑ j, γ n (S j) ≤ ENNReal.ofReal (p * (2 * (1 / r) ^ 3)) := by
    calc ∑ j, γ n (S j) ≤ ∑ _j : Fin p, ENNReal.ofReal (2 * (1 / r) ^ 3) :=
          Finset.sum_le_sum (fun j _ => hSj j)
      _ = ENNReal.ofReal (p * (2 * (1 / r) ^ 3)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg p), ENNReal.ofReal_natCast]
  have hmk := mul_meas_ge_le_lintegral₀ hNm ((2 : ENNReal) ^ l)
  rw [hint] at hmk
  have hsub : {z | 2 ^ l ≤ cnt X τ z} ⊆ {z | (2 : ENNReal) ^ l ≤ N z} := by
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz ⊢
    rw [← hN]
    exact_mod_cast hz
  have key : (2 : ENNReal) ^ l * γ n {z | 2 ^ l ≤ cnt X τ z} ≤
      ENNReal.ofReal (p * (2 * (1 / r) ^ 3)) :=
    le_trans (by gcongr) (le_trans hmk hsum)
  have hpow : ((2 : ENNReal) ^ l) = ENNReal.ofReal ((2 : ℝ) ^ l) := by
    rw [ENNReal.ofReal_pow (by norm_num)]; simp
  rw [hpow] at key
  have hne : ENNReal.ofReal ((2 : ℝ) ^ l) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]; linarith
  have key2 : γ n {z | 2 ^ l ≤ cnt X τ z} ≤
      ENNReal.ofReal (p * (2 * (1 / r) ^ 3)) / ENNReal.ofReal ((2 : ℝ) ^ l) :=
    (ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl ENNReal.ofReal_ne_top)).mpr
      (by rw [mul_comm]; exact key)
  rw [← ENNReal.ofReal_div_of_pos h2l] at key2
  refine le_trans key2 (le_of_eq ?_)
  congr 1
  rw [hr]
  field_simp
  try ring

lemma sum_ratio_le {p : ℕ} (hp : 1 ≤ p) :
    ∑ l ∈ Finset.range (Nat.log 2 p + 1), ((2 : ℝ) ^ l / (2 * p)) ^ 2 ≤ 1 / 3 := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  set q := Nat.log 2 p
  have hq : (2 : ℝ) ^ q ≤ p := by exact_mod_cast Nat.pow_log_le_self 2 (by omega : p ≠ 0)
  have e : ∀ l, ((2 : ℝ) ^ l / (2 * p)) ^ 2 = (4 : ℝ) ^ l / (4 * p ^ 2) := by
    intro l
    rw [div_pow, ← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
    ring
  simp_rw [e]
  rw [← Finset.sum_div, geom_sum_eq (by norm_num)]
  rw [div_le_iff₀ (by positivity)]
  have h4 : (4 : ℝ) ^ (q + 1) = 4 * ((2 : ℝ) ^ q) ^ 2 := by
    rw [pow_succ, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]; ring
  rw [h4]
  have : ((2 : ℝ) ^ q) ^ 2 ≤ (p : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hq 2
  nlinarith

/-- The good event `G₀ = {z : ∀ u, zᵀXu ≤ √12 · sortedSum u}` has probability at least `2/3`. -/
lemma good_event {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (hX : UnitCols X) (hp : 1 ≤ p) :
    MeasurableSet {z : Fin n → ℝ | ∀ u, dot z (X.mulVec u) ≤ Real.sqrt 12 * sortedSum u} ∧
    2 / 3 ≤ (γ n {z : Fin n → ℝ | ∀ u, dot z (X.mulVec u) ≤ Real.sqrt 12 * sortedSum u}).toReal := by
  set G0 := {z : Fin n → ℝ | ∀ u, dot z (X.mulVec u) ≤ Real.sqrt 12 * sortedSum u}
  have hclosed : IsClosed G0 := by
    have : G0 = ⋂ u : Fin p → ℝ, {z : Fin n → ℝ | dot z (X.mulVec u) ≤ Real.sqrt 12 * sortedSum u} := by
      ext z; simp [G0]
    rw [this]
    exact isClosed_iInter (fun u => isClosed_le (continuous_dot_left _) continuous_const)
  have hm : MeasurableSet G0 := hclosed.measurableSet
  refine ⟨hm, ?_⟩
  have hsub : G0ᶜ ⊆ ⋃ l ∈ Finset.range (Nat.log 2 p + 1), {z | 2 ^ l ≤ cnt X (tau p l) z} := by
    intro z hz
    by_contra hcon
    apply hz
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_le] at hcon
    intro u
    exact sorted_bound_of_counts hp X z (fun l hl => hcon l hl) u
  have hbound : γ n G0ᶜ ≤ ENNReal.ofReal (1 / 3) := by
    calc γ n G0ᶜ ≤ γ n (⋃ l ∈ Finset.range (Nat.log 2 p + 1), {z | 2 ^ l ≤ cnt X (tau p l) z}) :=
          measure_mono hsub
      _ ≤ ∑ l ∈ Finset.range (Nat.log 2 p + 1), γ n {z | 2 ^ l ≤ cnt X (tau p l) z} :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ l ∈ Finset.range (Nat.log 2 p + 1), ENNReal.ofReal (((2 : ℝ) ^ l / (2 * p)) ^ 2) := by
          apply Finset.sum_le_sum; intro l hl
          apply tail_count X hX l
          have hl' : l ≤ Nat.log 2 p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
          exact le_trans (Nat.pow_le_pow_right (by norm_num) hl')
            (Nat.pow_log_le_self 2 (by omega))
      _ = ENNReal.ofReal (∑ l ∈ Finset.range (Nat.log 2 p + 1), ((2 : ℝ) ^ l / (2 * p)) ^ 2) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun l _ => sq_nonneg _)]
      _ ≤ ENNReal.ofReal (1 / 3) := ENNReal.ofReal_le_ofReal (sum_ratio_le hp)
  have hc := prob_compl_eq_one_sub (μ := γ n) hm
  have h1 : (γ n G0ᶜ).toReal ≤ 1 / 3 := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    rwa [ENNReal.toReal_ofReal (by norm_num)] at this
  rw [hc, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top] at h1
  simp only [ENNReal.toReal_one] at h1
  linarith

section Sup

variable {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (Λ : ℝ)

/-- The index set `T = {u : 8 · sortedSum u ≤ 1, 6 √Λ ‖Xu‖ ≤ 1}`. -/
def Tset : Set (Fin p → ℝ) :=
  {u | 8 * sortedSum u ≤ 1 ∧ 6 * Real.sqrt Λ * l2 (X.mulVec u) ≤ 1}

/-- `f(z) = sup_{u ∈ T} zᵀXu`. -/
noncomputable def fsup (z : Fin n → ℝ) : ℝ :=
  sSup ((fun u => dot z (X.mulVec u)) '' Tset X Λ)

lemma sortedSum_zero' : sortedSum (0 : Fin p → ℝ) = 0 := by
  unfold sortedSum; simp

lemma zero_mem_T : (0 : Fin p → ℝ) ∈ Tset X Λ := by
  refine ⟨?_, ?_⟩
  · rw [sortedSum_zero']; norm_num
  · rw [Matrix.mulVec_zero]; simp [l2]

variable {Λ}

lemma dot_le_on_T (hΛ : 0 < Λ) (z : Fin n → ℝ) (u : Fin p → ℝ) (hu : u ∈ Tset X Λ) :
    dot z (X.mulVec u) ≤ l2 z * (1 / (6 * Real.sqrt Λ)) := by
  have hs : 0 < 6 * Real.sqrt Λ := by have := Real.sqrt_pos.mpr hΛ; linarith
  have h1 : l2 (X.mulVec u) ≤ 1 / (6 * Real.sqrt Λ) := by
    rw [le_div_iff₀ hs]; linarith [hu.2]
  calc dot z (X.mulVec u) ≤ l2 z * l2 (X.mulVec u) := dot_le_l2 _ _
    _ ≤ l2 z * (1 / (6 * Real.sqrt Λ)) :=
        mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)

lemma bdd_T (hΛ : 0 < Λ) (z : Fin n → ℝ) :
    BddAbove ((fun u => dot z (X.mulVec u)) '' Tset X Λ) := by
  refine ⟨l2 z * (1 / (6 * Real.sqrt Λ)), ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  exact dot_le_on_T X hΛ z u hu

lemma le_fsup (hΛ : 0 < Λ) (z : Fin n → ℝ) (u : Fin p → ℝ) (hu : u ∈ Tset X Λ) :
    dot z (X.mulVec u) ≤ fsup X Λ z :=
  le_csSup (bdd_T X hΛ z) ⟨u, hu, rfl⟩

lemma fsup_le (z : Fin n → ℝ) (c : ℝ) (h : ∀ u ∈ Tset X Λ, dot z (X.mulVec u) ≤ c) :
    fsup X Λ z ≤ c := by
  refine csSup_le ⟨dot z (X.mulVec 0), ⟨0, zero_mem_T X Λ, rfl⟩⟩ ?_
  rintro _ ⟨u, hu, rfl⟩
  exact h u hu

lemma fsup_lip_aux (hΛ : 0 < Λ) (x y : Fin n → ℝ) :
    fsup X Λ x ≤ fsup X Λ y + 1 / (6 * Real.sqrt Λ) * l2 (x - y) := by
  apply fsup_le
  intro u hu
  have e : dot x (X.mulVec u) = dot y (X.mulVec u) + dot (x - y) (X.mulVec u) := by
    rw [dot_sub_left]; ring
  rw [e]
  have h1 := le_fsup X hΛ y u hu
  have h2 := dot_le_on_T X hΛ (x - y) u hu
  linarith

lemma l2_sub_comm {m : ℕ} (x y : Fin m → ℝ) : l2 (x - y) = l2 (y - x) := by
  unfold l2; congr 1; apply Finset.sum_congr rfl; intro i _; simp only [Pi.sub_apply]; ring

lemma fsup_lip (hΛ : 0 < Λ) (x y : Fin n → ℝ) :
    |fsup X Λ x - fsup X Λ y| ≤ 1 / (6 * Real.sqrt Λ) * Real.sqrt (∑ i, (x i - y i) ^ 2) := by
  have h1 := fsup_lip_aux X hΛ x y
  have h2 := fsup_lip_aux X hΛ y x
  rw [l2_sub_comm y x] at h2
  have e : l2 (x - y) = Real.sqrt (∑ i, (x i - y i) ^ 2) := rfl
  rw [e] at h1 h2
  rw [abs_le]; constructor <;> linarith

/-- Homogeneity: if `f(z) ≤ 1`, then `zᵀXu ≤ max(8 sortedSum u, 6 √Λ ‖Xu‖)` for every `u`. -/
lemma bound_of_fsup_le_one (hΛ : 0 < Λ) (z : Fin n → ℝ) (hz : fsup X Λ z ≤ 1)
    (u : Fin p → ℝ) :
    dot z (X.mulVec u) ≤ max (8 * sortedSum u) (6 * Real.sqrt Λ * l2 (X.mulVec u)) := by
  set M := max (8 * sortedSum u) (6 * Real.sqrt Λ * l2 (X.mulVec u))
  have hsq : 0 < Real.sqrt Λ := Real.sqrt_pos.mpr hΛ
  rcases eq_or_lt_of_le (Real.sqrt_nonneg (∑ i, (X.mulVec u) i ^ 2) : 0 ≤ l2 (X.mulVec u)) with h0 | hpos
  · have := l2_eq_zero _ h0.symm
    rw [this]
    have : dot z (0 : Fin n → ℝ) = 0 := by simp [dot]
    rw [this]
    exact le_trans (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) (le_max_right _ _)
  · have hM : 0 < M := lt_of_lt_of_le (by positivity) (le_max_right _ _)
    set c := M⁻¹ with hc
    have hc0 : 0 < c := inv_pos.mpr hM
    have hmem : c • u ∈ Tset X Λ := by
      refine ⟨?_, ?_⟩
      · have := sortedSum_smul_le u c hc0.le
        have h8 : 8 * sortedSum u ≤ M := le_max_left _ _
        calc 8 * sortedSum (c • u) ≤ c * (8 * sortedSum u) := by nlinarith
          _ ≤ c * M := mul_le_mul_of_nonneg_left h8 hc0.le
          _ = 1 := inv_mul_cancel₀ hM.ne'
      · rw [Matrix.mulVec_smul, l2_smul, abs_of_pos hc0]
        have h6 : 6 * Real.sqrt Λ * l2 (X.mulVec u) ≤ M := le_max_right _ _
        calc 6 * Real.sqrt Λ * (c * l2 (X.mulVec u)) = c * (6 * Real.sqrt Λ * l2 (X.mulVec u)) := by
              ring
          _ ≤ c * M := mul_le_mul_of_nonneg_left h6 hc0.le
          _ = 1 := inv_mul_cancel₀ hM.ne'
    have := le_trans (le_fsup X hΛ z _ hmem) hz
    rw [Matrix.mulVec_smul, dot_smul_right] at this
    have : M * (c * dot z (X.mulVec u)) ≤ M * 1 := mul_le_mul_of_nonneg_left this hM.le
    rw [← mul_assoc, mul_inv_cancel₀ hM.ne'] at this
    linarith

end Sup

lemma sqrt12_le : Real.sqrt 12 ≤ 4 := by
  rw [Real.sqrt_le_left (by norm_num)]; norm_num

lemma closed_event {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (c : (Fin p → ℝ) → ℝ) :
    IsClosed {z : Fin n → ℝ | ∀ u, dot z (X.mulVec u) ≤ c u} := by
  have : {z : Fin n → ℝ | ∀ u, dot z (X.mulVec u) ≤ c u} =
      ⋂ u : Fin p → ℝ, {z : Fin n → ℝ | dot z (X.mulVec u) ≤ c u} := by
    ext z; simp
  rw [this]
  exact isClosed_iInter (fun u => isClosed_le (continuous_dot_left _) continuous_const)

/-- The concentration step in standard-Gaussian coordinates, for `Λ ≥ log 2`. -/
lemma z_tail {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (hX : UnitCols X) (hp : 1 ≤ p)
    (Λ : ℝ) (hΛ : Real.log 2 ≤ Λ) :
    γ n {z | ¬ ∀ u, dot z (X.mulVec u) ≤
        max (8 * sortedSum u) (6 * Real.sqrt Λ * l2 (X.mulVec u))} ≤
      ENNReal.ofReal (Real.exp (-Λ)) := by
  have hlog2 : (4 / 9 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hΛ0 : 0 < Λ := by linarith
  have hsq : (2 / 3 : ℝ) ≤ Real.sqrt Λ := by
    rw [Real.le_sqrt (by norm_num) hΛ0.le]; linarith
  set ℓ := 1 / (6 * Real.sqrt Λ) with hℓ
  have hℓ0 : 0 < ℓ := by rw [hℓ]; positivity
  have hlip := fsup_lip X hΛ0
  set E := ∫ z, fsup X Λ z ∂(γ n) with hE
  -- step 1: the mean is at most `1/2 + ℓ`
  have hG := good_event X hX hp
  have hmean : E ≤ 1 / 2 + ℓ := by
    by_contra hcon
    push Not at hcon
    set t := (E - 1 / 2) / ℓ with ht
    have ht1 : 1 < t := by rw [ht, lt_div_iff₀ hℓ0]; linarith
    have hlip' : ∀ x y : Fin n → ℝ, |(-fsup X Λ x) - (-fsup X Λ y)| ≤
        ℓ * Real.sqrt (∑ i, (x i - y i) ^ 2) := by
      intro x y
      rw [show (-fsup X Λ x) - (-fsup X Λ y) = -(fsup X Λ x - fsup X Λ y) by ring, abs_neg]
      exact hlip x y
    have c2 := (GaussianMatrix.gaussian_concentration_vector (fun z => -fsup X Λ z) ℓ hℓ0
      hlip' t (by linarith)).2
    have hneg : ∫ y, -fsup X Λ y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) = -E := by
      rw [integral_neg]
    rw [hneg] at c2
    have hsub : {z : Fin n → ℝ | ∀ u, dot z (X.mulVec u) ≤ Real.sqrt 12 * sortedSum u} ⊆
        {x | -E + ℓ * t ≤ -fsup X Λ x} := by
      intro z hz
      simp only [Set.mem_setOf_eq] at hz ⊢
      have : fsup X Λ z ≤ 1 / 2 := by
        apply fsup_le
        intro u hu
        have h1 := hz u
        have h2 : sortedSum u ≤ 1 / 8 := by linarith [hu.1]
        have h3 := sqrt12_le
        have h4 := sortedSum_nonneg u
        nlinarith [Real.sqrt_nonneg 12]
      have : ℓ * t = E - 1 / 2 := by rw [ht]; field_simp
      linarith
    have hle := le_trans (measure_mono hsub) c2
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le] at this
    have hexp : Real.exp (-t ^ 2 / 2) ≤ Real.exp (-1 / 2) := by
      apply Real.exp_le_exp.mpr; nlinarith
    have hexp2 : Real.exp (-1 / 2) < 2 / 3 := by
      have h := Real.add_one_lt_exp (show (1 / 2 : ℝ) ≠ 0 by norm_num)
      have e : Real.exp (-1 / 2) = (Real.exp (1 / 2))⁻¹ := by rw [← Real.exp_neg]; ring_nf
      rw [e, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
      linarith
    linarith [hG.2]
  -- step 2: upper tail at level `√(2Λ)`
  set s := Real.sqrt (2 * Λ) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have c1 := (GaussianMatrix.gaussian_concentration_vector (fun z => fsup X Λ z) ℓ hℓ0
    hlip s hs0).2
  have hs2 : -s ^ 2 / 2 = -Λ := by rw [hs, Real.sq_sqrt (by linarith)]; ring
  rw [hs2] at c1
  refine le_trans (measure_mono ?_) c1
  intro z hz
  simp only [Set.mem_setOf_eq] at hz ⊢
  by_contra hlt
  push Not at hlt
  apply hz
  apply bound_of_fsup_le_one X hΛ0 z
  -- `f(z) < E + ℓ s ≤ 1`
  have hsΛ : s = Real.sqrt 2 * Real.sqrt Λ := by
    rw [hs, Real.sqrt_mul (by norm_num)]
  have hnum : ℓ * (1 + s) ≤ 1 / 2 := by
    rw [hℓ, hsΛ]
    have hsqpos : 0 < Real.sqrt Λ := by linarith
    have h2 : Real.sqrt 2 ≤ 3 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    nlinarith
  have : ℓ + ℓ * s = ℓ * (1 + s) := by ring
  linarith

/-- **Weak form of the event `𝓕`.** -/
theorem weakF_part {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (hX : UnitCols X) (hp : 1 ≤ p)
    (σ : ℝ) (hσ : 0 < σ) (δ0 : ℝ) (hδ0 : 0 < δ0) (hδ1 : δ0 < 1) :
    MeasurableSet {ε : Fin n → ℝ | ∀ u : Fin p → ℝ, dot ε (X.mulVec u) ≤
        σ * max (8 * sortedSum u) (6 * Real.sqrt (Real.log (1 / δ0)) * l2 (X.mulVec u))} ∧
    1 - δ0 ≤ (noiseLaw n σ {ε : Fin n → ℝ | ∀ u : Fin p → ℝ, dot ε (X.mulVec u) ≤
        σ * max (8 * sortedSum u) (6 * Real.sqrt (Real.log (1 / δ0)) * l2 (X.mulVec u))}).toReal := by
  set Λ := Real.log (1 / δ0) with hΛ
  set A := {ε : Fin n → ℝ | ∀ u : Fin p → ℝ, dot ε (X.mulVec u) ≤
        σ * max (8 * sortedSum u) (6 * Real.sqrt Λ * l2 (X.mulVec u))} with hA
  set Az := {z : Fin n → ℝ | ∀ u : Fin p → ℝ, dot z (X.mulVec u) ≤
        max (8 * sortedSum u) (6 * Real.sqrt Λ * l2 (X.mulVec u))} with hAz
  have hAm : MeasurableSet A := (closed_event X _).measurableSet
  have hAzm : MeasurableSet Az := (closed_event X _).measurableSet
  refine ⟨hAm, ?_⟩
  have hpre : (fun z : Fin n → ℝ => fun i => σ * z i) ⁻¹' A = Az := by
    ext z
    simp only [Set.mem_preimage, hA, hAz, Set.mem_setOf_eq]
    constructor
    · intro h u
      have := h u
      rw [dot_smul_left] at this
      exact le_of_mul_le_mul_left this hσ
    · intro h u
      rw [dot_smul_left]
      exact mul_le_mul_of_nonneg_left (h u) hσ.le
  have hmeasS : Measurable (fun z : Fin n → ℝ => fun i => σ * z i) := by fun_prop
  have hlaw : noiseLaw n σ A = γ n Az := by
    rw [noiseLaw_eq_map, Measure.map_apply hmeasS hAm, hpre]
  rw [hlaw]
  haveI := γ_prob n
  by_cases hsmall : δ0 ≤ 1 / 2
  · have hΛ2 : Real.log 2 ≤ Λ := by
      rw [hΛ]
      apply Real.log_le_log (by norm_num)
      rw [le_div_iff₀ hδ0]; linarith
    have ht := z_tail X hX hp Λ hΛ2
    have hcompl : Azᶜ = {z | ¬ ∀ u, dot z (X.mulVec u) ≤
        max (8 * sortedSum u) (6 * Real.sqrt Λ * l2 (X.mulVec u))} := by
      ext z; simp [hAz]
    have hexpΛ : Real.exp (-Λ) = δ0 := by
      rw [hΛ, one_div, Real.log_inv, neg_neg, Real.exp_log hδ0]
    rw [← hcompl, hexpΛ] at ht
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top ht
    rw [ENNReal.toReal_ofReal hδ0.le, prob_compl_eq_one_sub hAzm,
      ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top] at h1
    simp only [ENNReal.toReal_one] at h1
    linarith
  · push Not at hsmall
    have hG := good_event X hX hp
    have hsub : {z : Fin n → ℝ | ∀ u, dot z (X.mulVec u) ≤ Real.sqrt 12 * sortedSum u} ⊆ Az := by
      intro z hz u
      have h1 := hz u
      have h2 := sortedSum_nonneg u
      have h3 := sqrt12_le
      have : Real.sqrt 12 * sortedSum u ≤ 8 * sortedSum u := by nlinarith
      exact le_trans h1 (le_trans this (le_max_left _ _))
    have := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub (μ := γ n))
    linarith [hG.2]

lemma sortedEvent_part {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (hX : UnitCols X) (hp : 1 ≤ p)
    (σ : ℝ) (hσ : 0 < σ) :
    MeasurableSet {ε : Fin n → ℝ | ∀ u : Fin p → ℝ,
        dot ε (X.mulVec u) ≤ Real.sqrt 12 * σ * sortedSum u} ∧
    2 / 3 ≤ (noiseLaw n σ {ε : Fin n → ℝ | ∀ u : Fin p → ℝ,
        dot ε (X.mulVec u) ≤ Real.sqrt 12 * σ * sortedSum u}).toReal := by
  set A := {ε : Fin n → ℝ | ∀ u : Fin p → ℝ,
        dot ε (X.mulVec u) ≤ Real.sqrt 12 * σ * sortedSum u} with hA
  have hAm : MeasurableSet A := (closed_event X _).measurableSet
  refine ⟨hAm, ?_⟩
  have hG := good_event X hX hp
  have hpre : (fun z : Fin n → ℝ => fun i => σ * z i) ⁻¹' A =
      {z : Fin n → ℝ | ∀ u, dot z (X.mulVec u) ≤ Real.sqrt 12 * sortedSum u} := by
    ext z
    simp only [Set.mem_preimage, hA, Set.mem_setOf_eq]
    constructor
    · intro h u
      have := h u
      rw [dot_smul_left, show Real.sqrt 12 * σ * sortedSum u = σ * (Real.sqrt 12 * sortedSum u)
        by ring] at this
      exact le_of_mul_le_mul_left this hσ
    · intro h u
      rw [dot_smul_left, show Real.sqrt 12 * σ * sortedSum u = σ * (Real.sqrt 12 * sortedSum u)
        by ring]
      exact mul_le_mul_of_nonneg_left (h u) hσ.le
  have hmeasS : Measurable (fun z : Fin n → ℝ => fun i => σ * z i) := by fun_prop
  rw [noiseLaw_eq_map, Measure.map_apply hmeasS hAm, hpre]
  exact hG.2

end BICFweak

open BICFweak SubsetShrink.Events in
theorem solution {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (hX : UnitCols X) (hp : 1 ≤ p)
    (σ : ℝ) (hσ : 0 < σ) :
    (MeasurableSet {ε : Fin n → ℝ | ∀ u : Fin p → ℝ,
        dot ε (X.mulVec u) ≤ Real.sqrt 12 * σ * sortedSum u} ∧
      2 / 3 ≤ (noiseLaw n σ {ε : Fin n → ℝ | ∀ u : Fin p → ℝ,
        dot ε (X.mulVec u) ≤ Real.sqrt 12 * σ * sortedSum u}).toReal) ∧
    ∀ δ0 : ℝ, 0 < δ0 → δ0 < 1 →
      MeasurableSet {ε : Fin n → ℝ | ∀ u : Fin p → ℝ, dot ε (X.mulVec u) ≤
        σ * max (8 * sortedSum u) (6 * Real.sqrt (Real.log (1 / δ0)) * l2 (X.mulVec u))} ∧
      1 - δ0 ≤ (noiseLaw n σ {ε : Fin n → ℝ | ∀ u : Fin p → ℝ, dot ε (X.mulVec u) ≤
        σ * max (8 * sortedSum u) (6 * Real.sqrt (Real.log (1 / δ0)) * l2 (X.mulVec u))}).toReal :=
  ⟨sortedEvent_part X hX hp σ hσ, fun δ0 h0 h1 => weakF_part X hX hp σ hσ δ0 h0 h1⟩
