-- Prove2me | solution 1 for QueueingFundamentals.MG1.mean_departure_size
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T16:33:03.760665+00:00
-- url     : https://prove2.me/submissions/bb5ff1a6-a350-4097-a7e1-253754470183

import Mathlib
import Definitions.Def_QueueingFundamentals_MG1_embeddedChain



namespace QueueingFundamentals.MG1

open MeasureTheory Finset

lemma mg_ae_nonneg (B : Measure ℝ) (hB : B (Set.Iio 0) = 0) : ∀ᵐ t ∂B, 0 ≤ t := by
  rw [ae_iff]
  have : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext; simp
  rw [this]; exact hB

lemma mg_hasSum_integral {μ : Measure ℝ} (F : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hF : ∀ n, AEStronglyMeasurable (F n) μ) (hpos : ∀ᵐ t ∂μ, ∀ n, 0 ≤ F n t)
    (hsum : ∀ᵐ t ∂μ, HasSum (fun n => F n t) (g t)) (hg : Integrable g μ) :
    HasSum (fun n => ∫ t, F n t ∂μ) (∫ t, g t ∂μ) := by
  refine hasSum_integral_of_dominated_convergence (fun n t => ‖F n t‖) hF ?_ ?_ ?_ hsum
  · intro n; exact Filter.Eventually.of_forall (fun t => le_rfl)
  · filter_upwards [hpos, hsum] with t h1 h2
    simpa [Real.norm_eq_abs, abs_of_nonneg (h1 _)] using h2.summable
  · refine hg.congr ?_
    filter_upwards [hpos, hsum] with t h1 h2
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (h1 _)]; exact h2.tsum_eq.symm

lemma mg_poisson_sum (x : ℝ) :
    HasSum (fun n : ℕ => Real.exp (-x) * x ^ n / (Nat.factorial n : ℝ)) 1 := by
  have h : HasSum (fun n : ℕ => x ^ n / (Nat.factorial n : ℝ)) (Real.exp x) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp x
  have := h.mul_left (Real.exp (-x))
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at this
  refine this.congr_fun ?_
  intro n; ring

lemma mg_poisson_mean (x : ℝ) :
    HasSum (fun n : ℕ => (n : ℝ) * (Real.exp (-x) * x ^ n / (Nat.factorial n : ℝ))) x := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_mul, sub_zero]
  have := (mg_poisson_sum x).mul_left x
  rw [mul_one] at this
  refine this.congr_fun ?_
  intro n
  rw [Nat.factorial_succ]; push_cast
  field_simp
  ring

variable {lam : ℝ} {B : Measure ℝ}

lemma mg_k_nonneg (hlam : 0 < lam) (hB : B (Set.Iio 0) = 0) (i : ℕ) : 0 ≤ arrivalProb lam B i := by
  unfold arrivalProb
  apply integral_nonneg_of_ae
  filter_upwards [mg_ae_nonneg B hB] with t ht
  have : 0 ≤ lam * t := mul_nonneg hlam.le ht
  positivity

lemma mg_meas (lam : ℝ) (i : ℕ) :
    AEStronglyMeasurable (fun t : ℝ => Real.exp (-(lam * t)) * (lam * t) ^ i / (Nat.factorial i : ℝ)) B := by
  apply Continuous.aestronglyMeasurable; fun_prop

lemma mg_k_sum (hlam : 0 < lam) [IsProbabilityMeasure B] (hB : B (Set.Iio 0) = 0) :
    HasSum (arrivalProb lam B) 1 := by
  have := mg_hasSum_integral (μ := B)
    (fun i t => Real.exp (-(lam * t)) * (lam * t) ^ i / (Nat.factorial i : ℝ)) (fun _ => 1)
    (fun i => mg_meas lam i) ?_ ?_ (integrable_const _)
  · have e : (∫ _t, (1:ℝ) ∂B) = 1 := by simp
    rw [e] at this; exact this
  · filter_upwards [mg_ae_nonneg B hB] with t ht n
    have : 0 ≤ lam * t := mul_nonneg hlam.le ht
    positivity
  · exact Filter.Eventually.of_forall (fun t => mg_poisson_sum (lam * t))

lemma mg_k_mean (hlam : 0 < lam) [IsProbabilityMeasure B] (hB : B (Set.Iio 0) = 0)
    (hint : Integrable (fun t : ℝ => t) B) :
    HasSum (fun i : ℕ => (i : ℝ) * arrivalProb lam B i) (utilization lam B) := by
  have := mg_hasSum_integral (μ := B)
    (fun i t => (i : ℝ) * (Real.exp (-(lam * t)) * (lam * t) ^ i / (Nat.factorial i : ℝ)))
    (fun t => lam * t)
    (fun i => (mg_meas lam i).const_mul _) ?_ ?_ (hint.const_mul lam)
  · unfold utilization meanService
    rw [← integral_const_mul]
    refine this.congr_fun ?_
    intro i; unfold arrivalProb; rw [integral_const_mul]
  · filter_upwards [mg_ae_nonneg B hB] with t ht n
    have : 0 ≤ lam * t := mul_nonneg hlam.le ht
    positivity
  · exact Filter.Eventually.of_forall (fun t => mg_poisson_mean (lam * t))

lemma mg_k0_pos (hlam : 0 < lam) [IsProbabilityMeasure B] (hB : B (Set.Iio 0) = 0) :
    0 < arrivalProb lam B 0 := by
  unfold arrivalProb
  simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one]
  apply integral_exp_pos
  refine Integrable.mono' (integrable_const 1) ?_ ?_
  · apply Continuous.aestronglyMeasurable; fun_prop
  · filter_upwards [mg_ae_nonneg B hB] with t ht
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ lam * t := mul_nonneg hlam.le ht
    linarith

/-! Abstract part: a nonnegative sequence `k` with sum one and mean `ρ`. -/

/-- tail `A n = 1 - ∑_{i ≤ n} k i`. -/
noncomputable def mgA (k : ℕ → ℝ) (n : ℕ) : ℝ := 1 - ∑ i ∈ range (n + 1), k i

lemma mgA_hasSum_tail (k : ℕ → ℝ) (hk1 : HasSum k 1) (n : ℕ) :
    HasSum (fun j => if n < j then k j else 0) (mgA k n) := by
  rw [← hasSum_nat_add_iff' (n + 1)]
  have h1 : ∑ i ∈ range (n + 1), (if n < i then k i else 0) = 0 := by
    apply Finset.sum_eq_zero; intro i hi; simp at hi; simp; omega
  rw [h1, sub_zero]
  have := (hasSum_nat_add_iff' (n + 1)).mpr hk1
  refine this.congr_fun ?_
  intro j; simp; omega

lemma mgA_nonneg (k : ℕ → ℝ) (hk0 : ∀ i, 0 ≤ k i) (hk1 : HasSum k 1) (n : ℕ) : 0 ≤ mgA k n := by
  have := mgA_hasSum_tail k hk1 n
  rw [← this.tsum_eq]; exact tsum_nonneg (fun j => by split_ifs <;> simp [hk0])

lemma mgA_hasSum (k : ℕ → ℝ) (ρ : ℝ) (hk0 : ∀ i, 0 ≤ k i) (hk1 : HasSum k 1)
    (hkm : HasSum (fun i : ℕ => (i : ℝ) * k i) ρ) : HasSum (mgA k) ρ := by
  set f : ℕ × ℕ → ℝ := fun p => if p.1 < p.2 then k p.2 else 0 with hf
  have fnn : 0 ≤ f := fun p => by simp only [hf]; split_ifs <;> simp [hk0]
  have hinner : ∀ j : ℕ, HasSum (fun n => f (n, j)) ((j : ℝ) * k j) := by
    intro j
    have : HasSum (fun n => f (n, j)) (∑ n ∈ range j, f (n, j)) :=
      hasSum_sum_of_ne_finset_zero (by intro n hn; simp at hn; simp [hf]; omega)
    convert this using 1
    simp only [hf]
    rw [Finset.sum_congr rfl (g := fun _ => k j) (fun n hn => by simp at hn; simp [hn])]
    simp
  set g : ℕ × ℕ → ℝ := fun p => f (p.2, p.1) with hg
  have gnn : 0 ≤ g := fun p => fnn (p.2, p.1)
  have gsum : Summable g := (summable_prod_of_nonneg gnn).2
    ⟨fun j => (hinner j).summable, by
      simp only [hg]; simp_rw [(hinner _).tsum_eq]; exact hkm.summable⟩
  have gval : HasSum g ρ := by
    have := gsum.tsum_prod' (fun j => (hinner j).summable)
    simp only [hg] at this
    simp_rw [(hinner _).tsum_eq] at this
    rw [hkm.tsum_eq] at this
    rw [← this]; exact gsum.hasSum
  have fval : HasSum f ρ := by
    have := (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr gval
    exact this
  exact fval.prod_fiberwise (fun n => mgA_hasSum_tail k hk1 n)

def mgP (k : ℕ → ℝ) (i j : ℕ) : ℝ := if i = 0 then k j else if i ≤ j + 1 then k (j + 1 - i) else 0

lemma mg_tm_eq (lam : ℝ) (B : Measure ℝ) : transitionMatrix lam B = mgP (arrivalProb lam B) := rfl

lemma mg_row_hasSum (k : ℕ → ℝ) (π : ℕ → ℝ) (j : ℕ) :
    HasSum (fun i => π i * mgP k i j) (π 0 * k j + ∑ i ∈ range (j + 1), π (i + 1) * k (j - i)) := by
  have h2 : HasSum (fun i => π i * mgP k i j) (∑ i ∈ range (j + 2), π i * mgP k i j) :=
    hasSum_sum_of_ne_finset_zero (by
      intro i hi; simp at hi
      simp only [mgP]; rw [if_neg (by omega), if_neg (by omega), mul_zero])
  convert h2 using 1
  rw [sum_range_succ' _ (j + 1)]
  simp only [mgP, if_true]
  rw [add_comm]
  congr 1
  apply sum_congr rfl
  intro i hi; simp at hi
  rw [if_neg (by omega), if_pos (by omega)]
  congr 2; omega

noncomputable def mgc (k π : ℕ → ℝ) (n : ℕ) : ℝ :=
  π 0 * mgA k n + ∑ i ∈ range n, π (i + 1) * mgA k (n - i) - k 0 * π (n + 1)

noncomputable def mgr (k π : ℕ → ℝ) (j : ℕ) : ℝ :=
  π j - (π 0 * k j + ∑ i ∈ range (j + 1), π (i + 1) * k (j - i))

lemma mgA_succ (k : ℕ → ℝ) (m : ℕ) : mgA k (m + 1) = mgA k m - k (m + 1) := by
  simp only [mgA, sum_range_succ _ (m + 1)]; ring

lemma mgc_zero (k π : ℕ → ℝ) : mgc k π 0 = mgr k π 0 := by
  simp [mgc, mgr, mgA]; ring

lemma mgc_succ (k π : ℕ → ℝ) (n : ℕ) : mgc k π (n + 1) = mgc k π n + mgr k π (n + 1) := by
  have hs : ∑ i ∈ range (n + 1), π (i + 1) * mgA k (n + 1 - i) =
      ∑ i ∈ range n, π (i + 1) * mgA k (n - i) - ∑ i ∈ range n, π (i + 1) * k (n + 1 - i)
        + π (n + 1) * mgA k 1 := by
    rw [sum_range_succ, ← sum_sub_distrib]
    congr 1
    · apply sum_congr rfl; intro i hi; simp at hi
      rw [show n + 1 - i = (n - i) + 1 by omega, mgA_succ]; ring
    · simp
  have hA1 : mgA k 1 = 1 - k 0 - k 1 := by simp [mgA, sum_range_succ]; ring
  simp only [mgc, mgr]
  rw [hs, mgA_succ, hA1, sum_range_succ _ (n + 1), sum_range_succ _ n]
  simp
  ring

lemma mgc_eq_sum (k π : ℕ → ℝ) (n : ℕ) : mgc k π n = ∑ j ∈ range (n + 1), mgr k π j := by
  induction n with
  | zero => simp [mgc_zero]
  | succ n ih => rw [mgc_succ, ih, sum_range_succ _ (n + 1)]

lemma mg_stat_cut (k π : ℕ → ℝ) (h : ∀ j, HasSum (fun i => π i * mgP k i j) (π j)) (n : ℕ) :
    k 0 * π (n + 1) = π 0 * mgA k n + ∑ i ∈ range n, π (i + 1) * mgA k (n - i) := by
  have hr : ∀ j, mgr k π j = 0 := by
    intro j; simp only [mgr]; rw [(h j).unique (mg_row_hasSum k π j)]; ring
  have := mgc_eq_sum k π n
  simp only [hr, sum_const_zero, mgc] at this
  linarith

lemma mg_cut_stat (k π : ℕ → ℝ)
    (h : ∀ n, k 0 * π (n + 1) = π 0 * mgA k n + ∑ i ∈ range n, π (i + 1) * mgA k (n - i)) (j : ℕ) :
    HasSum (fun i => π i * mgP k i j) (π j) := by
  have hc : ∀ n, mgc k π n = 0 := by intro n; simp only [mgc]; rw [h n]; ring
  have hr : mgr k π j = 0 := by
    cases j with
    | zero => rw [← mgc_zero]; exact hc 0
    | succ n => have := mgc_succ k π n; rw [hc, hc] at this; linarith
  convert mg_row_hasSum k π j using 1
  simp only [mgr] at hr; linarith

lemma mg_key (k : ℕ → ℝ) (ρ : ℝ) (hk0 : ∀ i, 0 ≤ k i) (hk1 : HasSum k 1)
    (hkm : HasSum (fun i : ℕ => (i : ℝ) * k i) ρ) (u : ℕ → ℝ) (U c : ℝ) (hu : HasSum u U)
    (hu0 : ∀ i, 0 ≤ u i)
    (hcut : ∀ n, k 0 * u n = c * mgA k n + ∑ i ∈ range n, u i * mgA k (n - i)) :
    k 0 * U = c * ρ + U * (ρ - mgA k 0) := by
  have hA := mgA_hasSum k ρ hk0 hk1 hkm
  have hv : HasSum (fun l => mgA k (l + 1)) (ρ - mgA k 0) := by
    have := (hasSum_nat_add_iff' 1).mpr hA; simpa using this
  have hn1 : Summable fun i => ‖u i‖ :=
    hu.summable.congr (fun i => by rw [Real.norm_eq_abs, abs_of_nonneg (hu0 i)])
  have hn2 : Summable fun l => ‖mgA k (l + 1)‖ :=
    hv.summable.congr (fun i => by rw [Real.norm_eq_abs, abs_of_nonneg (mgA_nonneg k hk0 hk1 _)])
  have hconv : HasSum (fun m => ∑ kl ∈ antidiagonal m, u kl.1 * mgA k (kl.2 + 1))
      (U * (ρ - mgA k 0)) := by
    have := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hn1 hn2
    rw [hu.tsum_eq, hv.tsum_eq] at this
    rw [this]
    exact (summable_norm_sum_mul_antidiagonal_of_summable_norm hn1 hn2).of_norm.hasSum
  have hconv' : HasSum (fun n => ∑ i ∈ range n, u i * mgA k (n - i)) (U * (ρ - mgA k 0)) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [range_one, sum_singleton, range_zero, sum_empty, sub_zero]
    refine hconv.congr_fun ?_
    intro m
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply sum_congr rfl; intro i hi; simp at hi
    congr 2; omega
  have htot := (hA.mul_left c).add hconv'
  have hl := hu.mul_left (k 0)
  have : (fun n => k 0 * u n) = fun n => c * mgA k n + ∑ i ∈ range n, u i * mgA k (n - i) :=
    funext hcut
  rw [this] at hl
  exact hl.unique htot

lemma mg_stat_pi0 (k : ℕ → ℝ) (ρ : ℝ) (hk0 : ∀ i, 0 ≤ k i) (hk1 : HasSum k 1)
    (hkm : HasSum (fun i : ℕ => (i : ℝ) * k i) ρ) (π : ℕ → ℝ) (hπ : IsStationaryDist (mgP k) π) :
    π 0 = 1 - ρ := by
  obtain ⟨h0, h1, h2⟩ := hπ
  have hu : HasSum (fun n => π (n + 1)) (1 - π 0) := by
    have := (hasSum_nat_add_iff' 1).mpr h1; simpa using this
  have := mg_key k ρ hk0 hk1 hkm (fun n => π (n + 1)) (1 - π 0) (π 0) hu (fun i => h0 _)
    (mg_stat_cut k π h2)
  have hA0 : mgA k 0 = 1 - k 0 := by simp [mgA]
  rw [hA0] at this
  linarith

noncomputable def mgU (k : ℕ → ℝ) (c : ℝ) : ℕ → ℝ
  | n => (c * mgA k n + ∑ i : Fin n, mgU k c i * mgA k (n - i)) / k 0
decreasing_by exact i.2

lemma mgU_eq (k : ℕ → ℝ) (c : ℝ) (hk : k 0 ≠ 0) (n : ℕ) :
    k 0 * mgU k c n = c * mgA k n + ∑ i ∈ range n, mgU k c i * mgA k (n - i) := by
  rw [mgU, Fin.sum_univ_eq_sum_range (fun i => mgU k c i * mgA k (n - i))]
  field_simp

lemma mgU_nonneg (k : ℕ → ℝ) (c : ℝ) (hk0 : ∀ i, 0 ≤ k i) (hk1 : HasSum k 1) (hkp : 0 < k 0)
    (hc : 0 ≤ c) (n : ℕ) : 0 ≤ mgU k c n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have h := mgU_eq k c hkp.ne' n
    have : 0 ≤ c * mgA k n + ∑ i ∈ range n, mgU k c i * mgA k (n - i) := by
      apply add_nonneg (mul_nonneg hc (mgA_nonneg k hk0 hk1 n))
      apply sum_nonneg; intro i hi; simp at hi
      exact mul_nonneg (ih i hi) (mgA_nonneg k hk0 hk1 _)
    rw [← h] at this
    exact nonneg_of_mul_nonneg_right (by linarith) hkp

lemma mg_double_le (u a : ℕ → ℝ) (T : ℝ) (hu : ∀ i, 0 ≤ u i) (ha : ∀ i, 0 ≤ a i)
    (hT : HasSum (fun l => a (l + 1)) T) (N : ℕ) :
    ∑ n ∈ range N, ∑ i ∈ range n, u i * a (n - i) ≤ (∑ i ∈ range N, u i) * T := by
  have h1 : ∀ n ∈ range N, ∑ i ∈ range n, u i * a (n - i) =
      ∑ i ∈ range N, if i < n then u i * a (n - i) else 0 := by
    intro n hn; rw [← sum_filter]; congr 1; ext i; simp at hn ⊢; omega
  rw [sum_congr rfl h1, sum_comm, sum_mul]
  apply sum_le_sum; intro i hi
  rw [show ∑ n ∈ range N, (if i < n then u i * a (n - i) else 0) =
      u i * ∑ n ∈ range N, (if i < n then a (n - i) else 0) by
    rw [mul_sum]; apply sum_congr rfl; intro n _; split_ifs <;> simp]
  apply mul_le_mul_of_nonneg_left _ (hu i)
  rw [← sum_filter]
  have : (range N).filter (fun n => i < n) = Ico (i + 1) N := by ext n; simp; omega
  rw [this, sum_Ico_eq_sum_range]
  rw [sum_congr rfl (g := fun l => a (l + 1)) (fun l _ => by congr 1; omega)]
  exact sum_le_hasSum _ (fun l _ => ha _) hT

lemma mg_exists (k : ℕ → ℝ) (ρ : ℝ) (hk0 : ∀ i, 0 ≤ k i) (hk1 : HasSum k 1)
    (hkm : HasSum (fun i : ℕ => (i : ℝ) * k i) ρ) (hkp : 0 < k 0) (hρ : ρ < 1) :
    ∃ π, IsStationaryDist (mgP k) π := by
  have hρ0 : 0 ≤ ρ := hkm.nonneg (fun i => mul_nonneg (Nat.cast_nonneg _) (hk0 i))
  set c := 1 - ρ with hcdef
  have hc : 0 ≤ c := by linarith
  set u := mgU k c with hudef
  have hu0 : ∀ i, 0 ≤ u i := mgU_nonneg k c hk0 hk1 hkp hc
  have hA := mgA_hasSum k ρ hk0 hk1 hkm
  have hv : HasSum (fun l => mgA k (l + 1)) (ρ - mgA k 0) := by
    have := (hasSum_nat_add_iff' 1).mpr hA; simpa using this
  have hA0 : mgA k 0 = 1 - k 0 := by simp [mgA]
  have hbound : ∀ N, ∑ i ∈ range N, u i ≤ ρ := by
    intro N
    have e : k 0 * ∑ n ∈ range N, u n = c * ∑ n ∈ range N, mgA k n +
        ∑ n ∈ range N, ∑ i ∈ range n, u i * mgA k (n - i) := by
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      apply sum_congr rfl; intro n _; exact mgU_eq k c hkp.ne' n
    have h1 : ∑ n ∈ range N, mgA k n ≤ ρ :=
      sum_le_hasSum _ (fun l _ => mgA_nonneg k hk0 hk1 _) hA
    have h2 := mg_double_le u (mgA k) _ hu0 (mgA_nonneg k hk0 hk1) hv N
    rw [hA0] at h2
    have h3 : c * ∑ n ∈ range N, mgA k n ≤ c * ρ := mul_le_mul_of_nonneg_left h1 hc
    have h4 : (∑ i ∈ range N, u i) * (1 - ρ) ≤ ρ * (1 - ρ) := by
      rw [hcdef] at h3; nlinarith
    exact le_of_mul_le_mul_right h4 (by linarith)
  have hs : Summable u := summable_of_sum_range_le hu0 hbound
  have hkey := mg_key k ρ hk0 hk1 hkm u (∑' i, u i) c hs.hasSum hu0 (mgU_eq k c hkp.ne')
  rw [hA0] at hkey
  have hU : ∑' i, u i = ρ := by
    have : (∑' i, u i - ρ) * (1 - ρ) = 0 := by rw [hcdef] at hkey; linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exfalso; linarith
  refine ⟨fun n => if n = 0 then c else u (n - 1), ?_, ?_, ?_⟩
  · intro n; show 0 ≤ (if n = 0 then c else u (n - 1)); split_ifs; exact hc; exact hu0 _
  · rw [← hasSum_nat_add_iff' 1]
    simp only [range_one, sum_singleton, if_true, add_eq_zero, one_ne_zero, and_false,
      if_false, add_tsub_cancel_right]
    rw [hcdef, show (1:ℝ) - (1 - ρ) = ρ by ring, ← hU]; exact hs.hasSum
  · apply mg_cut_stat
    intro n
    simp only [add_eq_zero, one_ne_zero, and_false, if_false, add_tsub_cancel_right, if_true]
    exact mgU_eq k c hkp.ne' n

lemma mg_unique (k : ℕ → ℝ) (ρ : ℝ) (hk0 : ∀ i, 0 ≤ k i) (hk1 : HasSum k 1)
    (hkm : HasSum (fun i : ℕ => (i : ℝ) * k i) ρ) (hkp : 0 < k 0) (π σ : ℕ → ℝ)
    (hπ : IsStationaryDist (mgP k) π) (hσ : IsStationaryDist (mgP k) σ) : π = σ := by
  have e0 : π 0 = σ 0 := by
    rw [mg_stat_pi0 k ρ hk0 hk1 hkm π hπ, mg_stat_pi0 k ρ hk0 hk1 hkm σ hσ]
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => exact e0
    | succ m =>
      have h1 := mg_stat_cut k π hπ.2.2 m
      have h2 := mg_stat_cut k σ hσ.2.2 m
      have : ∑ i ∈ range m, π (i + 1) * mgA k (m - i) = ∑ i ∈ range m, σ (i + 1) * mgA k (m - i) := by
        apply sum_congr rfl; intro i hi; simp at hi; rw [ih (i + 1) (by omega)]
      rw [e0, this, ← h2] at h1
      exact mul_left_cancel₀ hkp.ne' h1

lemma mg_no_stat (k : ℕ → ℝ) (ρ : ℝ) (hk0 : ∀ i, 0 ≤ k i) (hk1 : HasSum k 1)
    (hkm : HasSum (fun i : ℕ => (i : ℝ) * k i) ρ) (hkp : 0 < k 0) (hρ : 1 ≤ ρ) (π : ℕ → ℝ)
    (hπ : IsStationaryDist (mgP k) π) : False := by
  have e0 := mg_stat_pi0 k ρ hk0 hk1 hkm π hπ
  have p0 : π 0 = 0 := by have := hπ.1 0; linarith
  have hz : ∀ n, π n = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      cases n with
      | zero => exact p0
      | succ m =>
        have h1 := mg_stat_cut k π hπ.2.2 m
        have : ∑ i ∈ range m, π (i + 1) * mgA k (m - i) = 0 := by
          apply sum_eq_zero; intro i hi; simp at hi; rw [ih (i + 1) (by omega), zero_mul]
        rw [this, p0, zero_mul, add_zero] at h1
        rcases mul_eq_zero.mp h1 with h | h
        · linarith
        · exact h
  have := hπ.2.1
  have h0 : HasSum π 0 := by
    have : π = fun _ => 0 := funext hz
    rw [this]; exact hasSum_zero
  have := this.unique h0
  norm_num at this

lemma mg_poisson_sq (x : ℝ) :
    HasSum (fun n : ℕ => (n : ℝ) ^ 2 * (Real.exp (-x) * x ^ n / (Nat.factorial n : ℝ))) (x ^ 2 + x) := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_mul, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow]
  have := ((mg_poisson_mean x).add (mg_poisson_sum x)).mul_left x
  rw [show x * (x + 1) = x ^ 2 + x by ring] at this
  refine this.congr_fun ?_
  intro n
  rw [Nat.factorial_succ]; push_cast
  field_simp
  ring

lemma mg_k_sq (hlam : 0 < lam) [IsProbabilityMeasure B] (hB : B (Set.Iio 0) = 0)
    (hint : Integrable (fun t : ℝ => t) B) (hint2 : Integrable (fun t : ℝ => t ^ 2) B) :
    HasSum (fun i : ℕ => (i : ℝ) ^ 2 * arrivalProb lam B i)
      (lam ^ 2 * (∫ t, t ^ 2 ∂B) + utilization lam B) := by
  have hg : Integrable (fun t : ℝ => (lam * t) ^ 2 + lam * t) B := by
    have := (hint2.const_mul (lam ^ 2)).add (hint.const_mul lam)
    refine this.congr (Filter.Eventually.of_forall (fun t => ?_))
    simp only [Pi.add_apply]; ring
  have := mg_hasSum_integral (μ := B)
    (fun i t => (i : ℝ) ^ 2 * (Real.exp (-(lam * t)) * (lam * t) ^ i / (Nat.factorial i : ℝ)))
    (fun t => (lam * t) ^ 2 + lam * t)
    (fun i => (mg_meas lam i).const_mul _) ?_ ?_ hg
  · have e : (∫ t, (lam * t) ^ 2 + lam * t ∂B) = lam ^ 2 * (∫ t, t ^ 2 ∂B) + utilization lam B := by
      unfold utilization meanService
      rw [integral_add _ (hint.const_mul lam), ← integral_const_mul, ← integral_const_mul]
      · congr 1; congr 1; funext t; ring
      · exact (hint2.const_mul (lam ^ 2)).congr (Filter.Eventually.of_forall (fun t => by ring))
    rw [e] at this
    refine this.congr_fun ?_
    intro i; unfold arrivalProb; rw [integral_const_mul]
  · filter_upwards [mg_ae_nonneg B hB] with t ht n
    have : 0 ≤ lam * t := mul_nonneg hlam.le ht
    positivity
  · exact Filter.Eventually.of_forall (fun t => mg_poisson_sq (lam * t))

lemma mgA_hasSum_w (k : ℕ → ℝ) (hk0 : ∀ i, 0 ≤ k i) (hk1 : HasSum k 1) (φ : ℕ → ℝ)
    (hφ : ∀ n, 0 ≤ φ n) (R : ℝ) (hR : HasSum (fun i => (∑ n ∈ range i, φ n) * k i) R) :
    HasSum (fun n => φ n * mgA k n) R := by
  set f : ℕ × ℕ → ℝ := fun p => if p.1 < p.2 then φ p.1 * k p.2 else 0 with hf
  have fnn : 0 ≤ f := fun p => by
    simp only [hf]; split_ifs
    · exact mul_nonneg (hφ _) (hk0 _)
    · exact le_rfl
  have hinner : ∀ j : ℕ, HasSum (fun n => f (n, j)) ((∑ n ∈ range j, φ n) * k j) := by
    intro j
    have : HasSum (fun n => f (n, j)) (∑ n ∈ range j, f (n, j)) :=
      hasSum_sum_of_ne_finset_zero (by intro n hn; simp at hn; simp [hf]; omega)
    convert this using 1
    simp only [hf]
    rw [sum_mul]
    apply sum_congr rfl; intro n hn; simp at hn; simp [hn]
  set g : ℕ × ℕ → ℝ := fun p => f (p.2, p.1) with hg
  have gnn : 0 ≤ g := fun p => fnn (p.2, p.1)
  have gsum : Summable g := (summable_prod_of_nonneg gnn).2
    ⟨fun j => (hinner j).summable, by
      simp only [hg]; simp_rw [(hinner _).tsum_eq]; exact hR.summable⟩
  have gval : HasSum g R := by
    have := gsum.tsum_prod' (fun j => (hinner j).summable)
    simp only [hg] at this
    simp_rw [(hinner _).tsum_eq] at this
    rw [hR.tsum_eq] at this
    rw [← this]; exact gsum.hasSum
  have fval : HasSum f R := by
    have := (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr gval
    exact this
  refine fval.prod_fiberwise (fun n => ?_)
  have e : (fun j => f (n, j)) = fun j => φ n * (if n < j then k j else 0) := by
    funext j; simp only [hf]; split_ifs <;> simp
  rw [e]; exact (mgA_hasSum_tail k hk1 n).mul_left (φ n)

lemma mg_conv_hasSum (u a : ℕ → ℝ) (U T : ℝ) (hu : HasSum u U) (hu0 : ∀ i, 0 ≤ u i)
    (ha0 : ∀ i, 0 ≤ a i) (hv : HasSum (fun l => a (l + 1)) T) :
    HasSum (fun n => ∑ i ∈ range n, u i * a (n - i)) (U * T) := by
  have hn1 : Summable fun i => ‖u i‖ :=
    hu.summable.congr (fun i => by rw [Real.norm_eq_abs, abs_of_nonneg (hu0 i)])
  have hn2 : Summable fun l => ‖a (l + 1)‖ :=
    hv.summable.congr (fun i => by rw [Real.norm_eq_abs, abs_of_nonneg (ha0 _)])
  have hconv : HasSum (fun m => ∑ kl ∈ antidiagonal m, u kl.1 * a (kl.2 + 1)) (U * T) := by
    have := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hn1 hn2
    rw [hu.tsum_eq, hv.tsum_eq] at this
    rw [this]
    exact (summable_norm_sum_mul_antidiagonal_of_summable_norm hn1 hn2).of_norm.hasSum
  rw [← hasSum_nat_add_iff' 1]
  simp only [range_one, sum_singleton, range_zero, sum_empty, sub_zero]
  refine hconv.congr_fun ?_
  intro m
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply sum_congr rfl; intro i hi; simp at hi
  congr 2; omega

lemma mg_mean_abstract (k : ℕ → ℝ) (ρ : ℝ) (hk0 : ∀ i, 0 ≤ k i) (hk1 : HasSum k 1)
    (hkm : HasSum (fun i : ℕ => (i : ℝ) * k i) ρ) (hkp : 0 < k 0) (hρ : ρ < 1) (M : ℝ)
    (hM : HasSum (fun n : ℕ => ((n : ℝ) + 1) * mgA k n) M)
    (π : ℕ → ℝ) (hπ : IsStationaryDist (mgP k) π) :
    HasSum (fun n : ℕ => (n : ℝ) * π n) ((M - ρ ^ 2) / (1 - ρ)) := by
  have e0 := mg_stat_pi0 k ρ hk0 hk1 hkm π hπ
  obtain ⟨h0, h1, h2⟩ := hπ
  set u : ℕ → ℝ := fun n => π (n + 1) with hu_def
  have hu : HasSum u ρ := by
    have := (hasSum_nat_add_iff' 1).mpr h1; simp at this; rw [e0] at this
    simpa [hu_def] using this
  have hu0 : ∀ i, 0 ≤ u i := fun i => h0 _
  have hcut : ∀ n, k 0 * u n = (1 - ρ) * mgA k n + ∑ i ∈ range n, u i * mgA k (n - i) := by
    intro n; have := mg_stat_cut k π h2 n; rw [e0] at this; exact this
  have hA := mgA_hasSum k ρ hk0 hk1 hkm
  have hAn := mgA_nonneg k hk0 hk1
  have hA0 : mgA k 0 = 1 - k 0 := by simp [mgA]
  have hT : HasSum (fun l => mgA k (l + 1)) (ρ - (1 - k 0)) := by
    have := (hasSum_nat_add_iff' 1).mpr hA; simp at this; rw [← hA0]; exact this
  set a2 : ℕ → ℝ := fun l => (l : ℝ) * mgA k l with ha2
  have ha20 : ∀ l, 0 ≤ a2 l := fun l => mul_nonneg (Nat.cast_nonneg _) (hAn l)
  have hM2 : HasSum (fun l => a2 (l + 1)) (M - ρ) := by
    have h3 : HasSum a2 (M - ρ) := by
      refine (hM.sub hA).congr_fun ?_
      intro n; simp only [ha2]; ring
    have := (hasSum_nat_add_iff' 1).mpr h3
    simpa [ha2] using this
  have hMρ : 0 ≤ M - ρ := hM2.nonneg (fun l => ha20 _)
  set w : ℕ → ℝ := fun n => ((n : ℝ) + 1) * u n with hw
  have hw0 : ∀ n, 0 ≤ w n := fun n => mul_nonneg (by positivity) (hu0 n)
  have hid : ∀ n, k 0 * w n = (1 - ρ) * (((n : ℝ) + 1) * mgA k n) +
      ∑ i ∈ range n, w i * mgA k (n - i) + ∑ i ∈ range n, u i * a2 (n - i) := by
    intro n
    have e1 : k 0 * w n = ((n : ℝ) + 1) * (k 0 * u n) := by simp only [hw]; ring
    rw [e1, hcut n, mul_add, mul_sum, add_assoc, ← sum_add_distrib]
    congr 1
    · ring
    · apply sum_congr rfl; intro i hi; simp at hi
      simp only [hw, ha2]
      rw [Nat.cast_sub hi.le]; ring
  -- partial sums bounded
  have hbound : ∀ N, ∑ n ∈ range N, w n ≤ ((1 - ρ) * M + ρ * (M - ρ)) / (1 - ρ) := by
    intro N
    have e : k 0 * ∑ n ∈ range N, w n = (1 - ρ) * ∑ n ∈ range N, ((n : ℝ) + 1) * mgA k n +
        ∑ n ∈ range N, ∑ i ∈ range n, w i * mgA k (n - i) +
        ∑ n ∈ range N, ∑ i ∈ range n, u i * a2 (n - i) := by
      rw [mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
      apply sum_congr rfl; intro n _; exact hid n
    have b1 : ∑ n ∈ range N, ((n : ℝ) + 1) * mgA k n ≤ M :=
      sum_le_hasSum _ (fun l _ => mul_nonneg (by positivity) (hAn _)) hM
    have b2 := mg_double_le w (mgA k) _ hw0 hAn hT N
    have b3 := mg_double_le u a2 _ hu0 ha20 hM2 N
    have b4 : ∑ i ∈ range N, u i ≤ ρ := sum_le_hasSum _ (fun l _ => hu0 _) hu
    have b5 : (∑ i ∈ range N, u i) * (M - ρ) ≤ ρ * (M - ρ) := mul_le_mul_of_nonneg_right b4 hMρ
    have b6 : (1 - ρ) * ∑ n ∈ range N, ((n : ℝ) + 1) * mgA k n ≤ (1 - ρ) * M :=
      mul_le_mul_of_nonneg_left b1 (by linarith)
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  have hs : Summable w := summable_of_sum_range_le hw0 hbound
  set L := ∑' n, w n with hL
  have hwL : HasSum w L := hs.hasSum
  have hl := hwL.mul_left (k 0)
  have hr := (((hM.mul_left (1 - ρ)).add (mg_conv_hasSum w (mgA k) L _ hwL hw0 hAn hT)).add
    (mg_conv_hasSum u a2 ρ _ hu hu0 ha20 hM2))
  have : (fun n : ℕ => k 0 * w n) = fun n : ℕ => (1 - ρ) * (((n : ℝ) + 1) * mgA k n) +
      ∑ i ∈ range n, w i * mgA k (n - i) + ∑ i ∈ range n, u i * a2 (n - i) := funext hid
  rw [this] at hl
  have heq := hl.unique hr
  have hLv : L = (M - ρ ^ 2) / (1 - ρ) := by
    rw [eq_div_iff (by linarith)]; linarith
  rw [← hLv, ← hasSum_nat_add_iff' 1]
  simp only [range_one, sum_singleton, Nat.cast_zero, zero_mul, sub_zero]
  refine hwL.congr_fun ?_
  intro n; simp only [hw, hu_def]; push_cast; ring

lemma mg_sum_range_succ_id (i : ℕ) : ∑ n ∈ range i, ((n : ℝ) + 1) = ((i : ℝ) ^ 2 + i) / 2 := by
  induction i with
  | zero => simp
  | succ m ih => rw [sum_range_succ, ih]; push_cast; ring

theorem mean_departure_size_core (lam : ℝ) (hlam : 0 < lam) (B : Measure ℝ) [IsProbabilityMeasure B]
    (hB : B (Set.Iio 0) = 0)
    (hint : Integrable (fun t : ℝ => t) B) (hint2 : Integrable (fun t : ℝ => t ^ 2) B)
    (hρ : utilization lam B < 1)
    (π : ℕ → ℝ) (hπ : IsStationaryDist (transitionMatrix lam B) π) :
    HasSum (fun n : ℕ => (n : ℝ) * π n)
      (utilization lam B + (utilization lam B ^ 2 + lam ^ 2 * serviceVariance B) /
        (2 * (1 - utilization lam B))) := by
  rw [mg_tm_eq] at hπ
  have hk0 := mg_k_nonneg (B := B) hlam hB
  have hk1 := mg_k_sum (B := B) hlam hB
  have hkm := mg_k_mean (B := B) hlam hB hint
  have hkp := mg_k0_pos (B := B) hlam hB
  have hk2 := mg_k_sq (B := B) hlam hB hint hint2
  set ρ := utilization lam B with hρdef
  set m2 := ∫ t, t ^ 2 ∂B with hm2
  have hR : HasSum (fun i => (∑ n ∈ range i, ((n : ℝ) + 1)) * arrivalProb lam B i)
      ((lam ^ 2 * m2 + ρ + ρ) / 2) := by
    have := (hk2.add hkm).div_const 2
    refine this.congr_fun ?_
    intro i; rw [mg_sum_range_succ_id]; ring
  have hM := mgA_hasSum_w _ hk0 hk1 (fun n => (n : ℝ) + 1) (fun n => by positivity) _ hR
  have := mg_mean_abstract _ ρ hk0 hk1 hkm hkp hρ _ hM π hπ
  convert this using 1
  have hv : lam ^ 2 * serviceVariance B = lam ^ 2 * m2 - ρ ^ 2 := by
    simp only [serviceVariance, hρdef, utilization]; ring
  rw [hv]
  have : (1 - ρ) ≠ 0 := by linarith
  field_simp
  ring

end QueueingFundamentals.MG1

open QueueingFundamentals.MG1
open MeasureTheory

theorem solution (lam : ℝ) (hlam : 0 < lam) (B : Measure ℝ) [IsProbabilityMeasure B]
    (hB : B (Set.Iio 0) = 0)
    (hint : Integrable (fun t : ℝ => t) B) (hint2 : Integrable (fun t : ℝ => t ^ 2) B)
    (hρ : utilization lam B < 1)
    (π : ℕ → ℝ) (hπ : IsStationaryDist (transitionMatrix lam B) π) :
    HasSum (fun n : ℕ => (n : ℝ) * π n)
      (utilization lam B + (utilization lam B ^ 2 + lam ^ 2 * serviceVariance B) /
        (2 * (1 - utilization lam B))) := by
  exact mean_departure_size_core lam hlam B hB hint hint2 hρ π hπ
