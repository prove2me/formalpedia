-- Prove2me | solution 1 for QueueingFundamentals.MG1.wait_lst
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T16:24:42.572528+00:00
-- url     : https://prove2.me/submissions/5c7ab9bb-24cd-47f0-923f-ad03545921a3

import Mathlib
import Definitions.Def_QueueingFundamentals_MG1_embeddedChain
import Definitions.Def_QueueingFundamentals_MG1_transforms



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

theorem ergodicity_core (lam : ℝ) (hlam : 0 < lam) (B : Measure ℝ) [IsProbabilityMeasure B]
    (hB : B (Set.Iio 0) = 0)
    (hint : Integrable (fun t : ℝ => t) B) :
    (∃! π : ℕ → ℝ, IsStationaryDist (transitionMatrix lam B) π) ↔ utilization lam B < 1 := by
  rw [mg_tm_eq]
  have hk0 := mg_k_nonneg (B := B) hlam hB
  have hk1 := mg_k_sum (B := B) hlam hB
  have hkm := mg_k_mean (B := B) hlam hB hint
  have hkp := mg_k0_pos (B := B) hlam hB
  constructor
  · rintro ⟨π, hπ, -⟩
    by_contra h
    exact mg_no_stat _ _ hk0 hk1 hkm hkp (not_lt.mp h) π hπ
  · intro h
    obtain ⟨π, hπ⟩ := mg_exists _ _ hk0 hk1 hkm hkp h
    exact ⟨π, hπ, fun σ hσ => mg_unique _ _ hk0 hk1 hkm hkp σ π hσ hπ⟩

lemma mg_norm_summable (a : ℕ → ℝ) (ha0 : ∀ i, 0 ≤ a i) (ha : Summable a) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    Summable (fun i => ‖(a i : ℂ) * z ^ i‖) := by
  refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_) ha
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha0 i)]
  exact mul_le_of_le_one_right (ha0 i) (pow_le_one₀ (norm_nonneg _) hz)

lemma mg_pgf0 (a : ℕ → ℝ) : pgf a 0 = a 0 := by
  rw [pgf, tsum_eq_single 0]
  · simp
  · intro b hb; simp [hb]

lemma mg_pgf_identity (k : ℕ → ℝ) (hk0 : ∀ i, 0 ≤ k i) (hk1 : HasSum k 1) (π : ℕ → ℝ)
    (hπ : IsStationaryDist (mgP k) π) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    pgf π z * (z - pgf k z) = (π 0 : ℂ) * pgf k z * (z - 1) := by
  obtain ⟨h0, h1, h2⟩ := hπ
  have hu1 : HasSum (fun n => π (n + 1)) (1 - π 0) := by
    have := (hasSum_nat_add_iff' 1).mpr h1; simpa using this
  have nπ := mg_norm_summable π h0 h1.summable z hz
  have nk := mg_norm_summable k hk0 hk1.summable z hz
  have nu := mg_norm_summable (fun n => π (n + 1)) (fun i => h0 _) hu1.summable z hz
  set U := ∑' i, ((π (i + 1) : ℝ) : ℂ) * z ^ i with hU
  set K := pgf k z with hK
  have e1 : pgf π z = π 0 + z * U := by
    rw [pgf, nπ.of_norm.tsum_eq_zero_add, hU, ← tsum_mul_left]
    simp only [pow_zero, mul_one]
    congr 1; apply tsum_congr; intro i; ring
  have hconv : HasSum (fun m => ∑ kl ∈ antidiagonal m,
      (((π (kl.1 + 1) : ℝ) : ℂ) * z ^ kl.1) * ((k kl.2 : ℂ) * z ^ kl.2)) (U * K) := by
    have := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm nu nk
    rw [hK, pgf, this]
    exact (summable_norm_sum_mul_antidiagonal_of_summable_norm nu nk).of_norm.hasSum
  have hK' : HasSum (fun m => (k m : ℂ) * z ^ m) K := nk.of_norm.hasSum
  have htot := (hK'.mul_left (π 0 : ℂ)).add hconv
  have e2 : pgf π z = π 0 * K + U * K := by
    rw [pgf]
    refine (HasSum.tsum_eq ?_)
    refine htot.congr_fun ?_
    intro m
    have hb := (h2 m).unique (mg_row_hasSum k π m)
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    conv_lhs => rw [hb]
    push_cast
    rw [add_mul, mul_assoc, sum_mul]
    congr 1
    apply sum_congr rfl; intro i hi; simp at hi
    rw [show z ^ m = z ^ i * z ^ (m - i) by rw [← pow_add]; congr 1; omega]
    ring
  linear_combination (-K) * e1 + z * e2

theorem pk_transform_core (lam : ℝ) (hlam : 0 < lam) (B : Measure ℝ) [IsProbabilityMeasure B]
    (hB : B (Set.Iio 0) = 0)
    (hint : Integrable (fun t : ℝ => t) B) (hρ : utilization lam B < 1) :
    (∃ π : ℕ → ℝ, IsStationaryDist (transitionMatrix lam B) π) ∧
      ∀ π : ℕ → ℝ, IsStationaryDist (transitionMatrix lam B) π →
        π 0 = 1 - utilization lam B ∧
        ∀ z : ℂ, ‖z‖ ≤ 1 → z ≠ 1 →
          pgf (arrivalProb lam B) z ≠ z ∧
          pgf π z = (1 - (utilization lam B : ℂ)) * (1 - z) * pgf (arrivalProb lam B) z /
            (pgf (arrivalProb lam B) z - z) := by
  rw [mg_tm_eq]
  have hk0 := mg_k_nonneg (B := B) hlam hB
  have hk1 := mg_k_sum (B := B) hlam hB
  have hkm := mg_k_mean (B := B) hlam hB hint
  have hkp := mg_k0_pos (B := B) hlam hB
  refine ⟨mg_exists _ _ hk0 hk1 hkm hkp hρ, fun π hπ => ?_⟩
  have e0 := mg_stat_pi0 _ _ hk0 hk1 hkm π hπ
  refine ⟨e0, fun z hz hz1 => ?_⟩
  have hid := mg_pgf_identity _ hk0 hk1 π hπ z hz
  rw [e0] at hid
  push_cast at hid
  have hne : pgf (arrivalProb lam B) z ≠ z := by
    intro h
    rw [h, sub_self, mul_zero] at hid
    have hρc : (1 - (utilization lam B : ℂ)) ≠ 0 := by
      intro h'
      have : ((1 - utilization lam B : ℝ) : ℂ) = 0 := by push_cast; exact h'
      rw [Complex.ofReal_eq_zero] at this; linarith
    have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    have hz0 : z = 0 := by
      have := hid.symm
      rcases mul_eq_zero.mp this with h3 | h3
      · rcases mul_eq_zero.mp h3 with h4 | h4
        · exact absurd h4 hρc
        · exact h4
      · exact absurd h3 hz1'
    rw [hz0, mg_pgf0] at h
    have : (arrivalProb lam B 0 : ℂ) ≠ 0 := by exact_mod_cast hkp.ne'
    exact this h
  refine ⟨hne, ?_⟩
  have hne' : pgf (arrivalProb lam B) z - z ≠ 0 := sub_ne_zero.mpr hne
  rw [eq_div_iff hne']
  linear_combination (-1 : ℂ) * hid

lemma mg_lst_hasSum (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0) (lam : ℝ)
    (hlam : 0 < lam) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    HasSum (fun n : ℕ => ((∫ t, Real.exp (-(lam * t)) * (lam * t) ^ n / (Nat.factorial n : ℝ) ∂μ : ℝ) : ℂ)
      * z ^ n) (lst μ (lam * (1 - z))) := by
  have e : ∀ n : ℕ, ((∫ t, Real.exp (-(lam * t)) * (lam * t) ^ n / (Nat.factorial n : ℝ) ∂μ : ℝ) : ℂ)
      * z ^ n = ∫ t, ((Real.exp (-(lam * t)) * (lam * t) ^ n / (Nat.factorial n : ℝ) : ℝ) : ℂ)
        * z ^ n ∂μ := by
    intro n; rw [integral_mul_const]; congr 1; exact integral_ofReal.symm
  simp_rw [e]
  unfold lst
  refine hasSum_integral_of_dominated_convergence
    (fun n t => Real.exp (-(lam * t)) * (lam * t) ^ n / (Nat.factorial n : ℝ)) ?_ ?_ ?_ ?_ ?_
  · intro n; apply Continuous.aestronglyMeasurable; fun_prop
  · intro n
    filter_upwards [mg_ae_nonneg μ hμ] with t ht
    have h0 : 0 ≤ lam * t := mul_nonneg hlam.le ht
    have h1 : 0 ≤ Real.exp (-(lam * t)) * (lam * t) ^ n / (Nat.factorial n : ℝ) := by positivity
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h1, norm_pow]
    exact mul_le_of_le_one_right h1 (pow_le_one₀ (norm_nonneg _) hz)
  · exact Filter.Eventually.of_forall (fun t => (mg_poisson_sum (lam * t)).summable)
  · simp_rw [(mg_poisson_sum _).tsum_eq]; exact integrable_const _
  · refine Filter.Eventually.of_forall (fun t => ?_)
    have h := NormedSpace.expSeries_div_hasSum_exp ((lam : ℂ) * t * z)
    rw [← Complex.exp_eq_exp_ℂ] at h
    have h2 := h.mul_left (Complex.exp (-((lam : ℂ) * t)))
    rw [← Complex.exp_add] at h2
    have e1 : (fun n : ℕ => ((Real.exp (-(lam * t)) * (lam * t) ^ n / (Nat.factorial n : ℝ) : ℝ) : ℂ)
        * z ^ n) = fun i => Complex.exp (-(↑lam * ↑t)) * ((↑lam * ↑t * z) ^ i / ↑i.factorial) := by
      funext n; push_cast; rw [mul_pow, mul_pow]; ring
    have e2 : Complex.exp (-(↑lam * ↑t) + ↑lam * ↑t * z) =
        Complex.exp (-((lam : ℂ) * (1 - z) * (t : ℂ))) := by congr 1; ring
    rw [← e1, e2] at h2
    exact h2

lemma mg_pgf_lst (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0) (lam : ℝ)
    (hlam : 0 < lam) (a : ℕ → ℝ)
    (ha : ∀ n, a n = ∫ t, Real.exp (-(lam * t)) * (lam * t) ^ n / (Nat.factorial n : ℝ) ∂μ)
    (z : ℂ) (hz : ‖z‖ ≤ 1) : pgf a z = lst μ (lam * (1 - z)) := by
  rw [pgf]; simp_rw [ha]; exact (mg_lst_hasSum μ hμ lam hlam z hz).tsum_eq

lemma mg_lst_real (μ : Measure ℝ) (s : ℝ) :
    lst μ (s : ℂ) = ((∫ t, Real.exp (-(s * t)) ∂μ : ℝ) : ℂ) := by
  rw [lst, show (fun t : ℝ => Complex.exp (-((s : ℂ) * (t : ℂ)))) =
    fun t => ((Real.exp (-(s * t)) : ℝ) : ℂ) by funext t; push_cast; rfl]
  exact integral_ofReal

lemma mg_lst_conv (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] (s : ℂ) :
    lst (μ.conv ν) s = lst μ s * lst ν s := by
  unfold lst Measure.conv
  rw [integral_map (by fun_prop) (by apply Continuous.aestronglyMeasurable; fun_prop)]
  rw [← integral_prod_mul]
  congr 1; funext p; push_cast; rw [← Complex.exp_add]; congr 1; ring

lemma mg_lst_analytic (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : μ (Set.Iio 0) = 0) :
    AnalyticOnNhd ℂ (lst μ) {s : ℂ | 0 < s.re} := by
  have h1 : ∀ s, lst μ s = ProbabilityTheory.complexMGF id μ (-s) := by
    intro s; simp [lst, ProbabilityTheory.complexMGF, neg_mul]
  have h2 : (lst μ) = (ProbabilityTheory.complexMGF id μ) ∘ (fun s => -s) := funext h1
  rw [h2]
  refine ProbabilityTheory.analyticOnNhd_complexMGF.comp (analyticOnNhd_id.neg) ?_
  intro s hs
  simp only [Set.mem_setOf_eq, Complex.neg_re] at hs ⊢
  have hsub : Set.Iio (0:ℝ) ⊆ ProbabilityTheory.integrableExpSet id μ := by
    intro r hr
    simp only [ProbabilityTheory.integrableExpSet, Set.mem_setOf_eq, id]
    refine Integrable.mono' (integrable_const 1) ?_ ?_
    · apply Continuous.aestronglyMeasurable; fun_prop
    · filter_upwards [mg_ae_nonneg μ hμ] with t ht
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.mpr
      have : r < 0 := hr
      nlinarith
  exact interior_maximal hsub isOpen_Iio (by simp; linarith)

lemma mg_lst_B_bound (lam : ℝ) (hlam : 0 < lam) (B : Measure ℝ) [IsProbabilityMeasure B]
    (hB : B (Set.Iio 0) = 0) (hint : Integrable (fun t : ℝ => t) B) (s : ℝ) (hs : 0 < s)
    (hρ : utilization lam B < 1) :
    0 < s - lam * (1 - ∫ t, Real.exp (-(s * t)) ∂B) := by
  have hi : Integrable (fun t => Real.exp (-(s * t))) B := by
    refine Integrable.mono' (integrable_const 1) ?_ ?_
    · apply Continuous.aestronglyMeasurable; fun_prop
    · filter_upwards [mg_ae_nonneg B hB] with t ht
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.mpr
      nlinarith
  have hle : 1 - ∫ t, Real.exp (-(s * t)) ∂B ≤ s * meanService B := by
    unfold meanService
    rw [← integral_const_mul]
    have : (1 : ℝ) = ∫ _t, (1 : ℝ) ∂B := by simp
    rw [this, ← integral_sub (integrable_const _) hi]
    apply integral_mono_ae ((integrable_const _).sub hi) (hint.const_mul s)
    filter_upwards with t
    have := Real.add_one_le_exp (-(s * t))
    simp only [Pi.sub_apply]; linarith
  unfold utilization at hρ
  nlinarith

theorem wait_lst_core (lam : ℝ) (hlam : 0 < lam) (B : Measure ℝ) [IsProbabilityMeasure B]
    (hB : B (Set.Iio 0) = 0)
    (hint : Integrable (fun t : ℝ => t) B) (hρ : utilization lam B < 1)
    (π : ℕ → ℝ) (hπ : IsStationaryDist (transitionMatrix lam B) π)
    (W : Measure ℝ) [IsProbabilityMeasure W] (hW : W (Set.Iio 0) = 0)
    (hπW : ∀ n : ℕ, π n = ∫ t, (lam * t) ^ n * Real.exp (-(lam * t)) / (Nat.factorial n : ℝ) ∂W) :
    (∀ z : ℂ, ‖z‖ ≤ 1 → pgf π z = lst W ((lam : ℂ) * (1 - z))) ∧
    ∀ s : ℝ, 0 < s →
      lst W s = (1 - (utilization lam B : ℂ)) * s * lst B s / (s - lam * (1 - lst B s)) := by
  have hπW' : ∀ n : ℕ, π n = ∫ t, Real.exp (-(lam * t)) * (lam * t) ^ n / (Nat.factorial n : ℝ) ∂W := by
    intro n; rw [hπW]; congr 1; funext t; ring
  have part1 : ∀ z : ℂ, ‖z‖ ≤ 1 → pgf π z = lst W ((lam : ℂ) * (1 - z)) :=
    fun z hz => mg_pgf_lst W hW lam hlam π hπW' z hz
  have hK : ∀ z : ℂ, ‖z‖ ≤ 1 → pgf (arrivalProb lam B) z = lst B ((lam : ℂ) * (1 - z)) :=
    fun z hz => mg_pgf_lst B hB lam hlam _ (fun n => rfl) z hz
  refine ⟨part1, ?_⟩
  have pk := (pk_transform_core lam hlam B hB hint hρ).2 π hπ
  have hlamc : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  set ρc : ℂ := (utilization lam B : ℂ)
  -- F vanishes on the ball around lam
  set F : ℂ → ℂ := fun s => lst W s * (s - lam * (1 - lst B s)) - (1 - ρc) * s * lst B s with hF
  have hloc : ∀ s : ℂ, ‖s - lam‖ < lam → F s = 0 := by
    intro s hs
    set z : ℂ := 1 - s / lam with hz
    have hsz : s = (lam : ℂ) * (1 - z) := by rw [hz]; field_simp; ring
    have hzn : ‖z‖ ≤ 1 := by
      have : z = -((s - lam) / lam) := by rw [hz]; field_simp; ring
      rw [this, norm_neg, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam]
      rw [div_le_one hlam]; exact hs.le
    have hz1 : z ≠ 1 := by
      intro h; rw [h, sub_self, mul_zero] at hsz
      rw [hsz, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam] at hs
      exact lt_irrefl _ hs
    obtain ⟨hne, heq⟩ := pk.2 z hzn hz1
    rw [part1 z hzn, hK z hzn, ← hsz] at heq
    rw [hK z hzn, ← hsz] at hne
    have hd : lst B s - z ≠ 0 := sub_ne_zero.mpr hne
    rw [eq_div_iff hd] at heq
    simp only [hF]
    rw [hsz]
    rw [hsz] at heq
    linear_combination (lam : ℂ) * heq
  have hU : IsPreconnected {s : ℂ | 0 < s.re} := (convex_halfSpace_re_gt 0).isPreconnected
  have hFan : AnalyticOnNhd ℂ F {s : ℂ | 0 < s.re} := by
    have hW' := mg_lst_analytic W hW
    have hB' := mg_lst_analytic B hB
    simp only [hF]
    exact (hW'.mul (analyticOnNhd_id.sub (analyticOnNhd_const.mul
      (analyticOnNhd_const.sub hB')))).sub ((analyticOnNhd_const.mul analyticOnNhd_id).mul hB')
  have hev : F =ᶠ[nhds (lam : ℂ)] (fun _ => 0) := by
    have : Metric.ball (lam : ℂ) lam ∈ nhds (lam : ℂ) := Metric.ball_mem_nhds _ hlam
    filter_upwards [this] with s hs
    exact hloc s (by rw [Metric.mem_ball, dist_eq_norm] at hs; exact hs)
  have hEq := hFan.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hU
    (by simp [hlam]) hev
  intro s hs
  have h0 := hEq (show (s : ℂ) ∈ {s : ℂ | 0 < s.re} by simp [hs])
  simp only [hF] at h0
  have hpos := mg_lst_B_bound lam hlam B hB hint s hs hρ
  have hd : ((s : ℂ) - lam * (1 - lst B s)) ≠ 0 := by
    rw [mg_lst_real]
    intro h
    have : ((s - lam * (1 - ∫ t, Real.exp (-(s * t)) ∂B) : ℝ) : ℂ) = 0 := by push_cast; exact h
    rw [Complex.ofReal_eq_zero] at this; linarith
  rw [eq_div_iff hd]
  linear_combination h0

end QueueingFundamentals.MG1

open QueueingFundamentals.MG1
open MeasureTheory

theorem solution (lam : ℝ) (hlam : 0 < lam) (B : Measure ℝ) [IsProbabilityMeasure B]
    (hB : B (Set.Iio 0) = 0)
    (hint : Integrable (fun t : ℝ => t) B) (hρ : utilization lam B < 1)
    (π : ℕ → ℝ) (hπ : IsStationaryDist (transitionMatrix lam B) π)
    (W : Measure ℝ) [IsProbabilityMeasure W] (hW : W (Set.Iio 0) = 0)
    (hπW : ∀ n : ℕ, π n = ∫ t, (lam * t) ^ n * Real.exp (-(lam * t)) / (Nat.factorial n : ℝ) ∂W) :
    (∀ z : ℂ, ‖z‖ ≤ 1 → pgf π z = lst W ((lam : ℂ) * (1 - z))) ∧
    ∀ s : ℝ, 0 < s →
      lst W s = (1 - (utilization lam B : ℂ)) * s * lst B s / (s - lam * (1 - lst B s)) := by
  exact wait_lst_core lam hlam B hB hint hρ π hπ W hW hπW
