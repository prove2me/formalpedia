-- Prove2me | solution 1 for RamanujanNotebooks.entry_8_17_i
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T19:50:28.978349+00:00
-- url     : https://prove2.me/submissions/2c7bc922-1cff-42f1-be5f-be7a6e8bee9f

import Mathlib

namespace RN8EM
open Real Set MeasureTheory intervalIntegral

noncomputable def Pb (n : ℕ) (t : ℝ) : ℝ := bernoulliFun n (Int.fract t) / (n.factorial : ℝ)

noncomputable def Q (j : ℕ) (s : ℝ) : ℝ := bernoulliFun j s / (j.factorial : ℝ)

lemma Q_hasDeriv (j : ℕ) (s : ℝ) : HasDerivAt (Q (j + 1)) (Q j s) s := by
  have h := (hasDerivAt_bernoulliFun (j + 1) s).div_const ((j + 1).factorial : ℝ)
  refine h.congr_deriv ?_
  simp only [Q, Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  field_simp

lemma Q_cont (j : ℕ) : Continuous (Q j) := by
  unfold Q; exact (continuous_bernoulliFun j).div_const _

lemma Q_one_eq_zero (j : ℕ) (hj : j ≠ 1) : Q j 1 = Q j 0 := by
  simp [Q, bernoulliFun_endpoints_eq_of_ne_one hj]

lemma Q_zero_val (j : ℕ) : Q j 0 = (bernoulli j : ℝ) / (j.factorial : ℝ) := by
  simp [Q, bernoulliFun_eval_zero]

section
variable (f : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U) (hU0 : Ici (0 : ℝ) ⊆ U) (m : ℕ)
  (hf : ContDiffOn ℝ (m : WithTop ℕ∞) f U)
include hU hf

lemma D_hasDeriv (j : ℕ) (hj : j < m) (t : ℝ) (ht : t ∈ U) :
    HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f t) t := by
  have h1 := hf.differentiableOn_iteratedDerivWithin (m := j) (by exact_mod_cast hj)
    hU.uniqueDiffOn t ht
  have h2 : DifferentiableAt ℝ (iteratedDerivWithin j f U) t :=
    h1.differentiableAt (hU.mem_nhds ht)
  have heq : iteratedDerivWithin j f U =ᶠ[nhds t] iteratedDeriv j f :=
    Filter.eventually_of_mem (hU.mem_nhds ht) (fun y hy => iteratedDerivWithin_of_isOpen hU hy)
  have h3 : DifferentiableAt ℝ (iteratedDeriv j f) t := h2.congr_of_eventuallyEq heq.symm
  rw [iteratedDeriv_succ]
  exact h3.hasDerivAt

lemma D_cont (j : ℕ) (hj : j ≤ m) : ContinuousOn (iteratedDeriv j f) U := by
  have h1 := hf.continuousOn_iteratedDerivWithin (m := j) (by exact_mod_cast hj) hU.uniqueDiffOn
  exact h1.congr (fun y hy => (iteratedDerivWithin_of_isOpen hU hy).symm)

/-- integration by parts on `[k, k+1]`, raising the Bernoulli index -/
lemma ibp (k : ℝ) (hk : Icc k (k + 1) ⊆ U) (j : ℕ) (hj : j < m) :
    ∫ t in k..k + 1, Q j (t - k) * iteratedDeriv j f t =
      Q (j + 1) 1 * iteratedDeriv j f (k + 1) - Q (j + 1) 0 * iteratedDeriv j f k
        - ∫ t in k..k + 1, Q (j + 1) (t - k) * iteratedDeriv (j + 1) f t := by
  have hu : ∀ x ∈ uIcc k (k + 1), HasDerivAt (fun t => Q (j + 1) (t - k)) (Q j (x - k)) x := by
    intro x _
    have := (Q_hasDeriv j (x - k)).comp x ((hasDerivAt_id x).sub_const k)
    rw [mul_one] at this
    exact this
  have hv : ∀ x ∈ uIcc k (k + 1), HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f x) x := by
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    exact D_hasDeriv f U hU m hf j hj x (hk hx)
  have hu' : IntervalIntegrable (fun t => Q j (t - k)) volume k (k + 1) :=
    ((Q_cont j).comp (continuous_id.sub continuous_const)).intervalIntegrable _ _
  have hv' : IntervalIntegrable (iteratedDeriv (j + 1) f) volume k (k + 1) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by linarith)]
    exact (D_cont f U hU m hf (j + 1) hj).mono hk
  have h := integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  simp only [add_sub_cancel_left, sub_self] at h
  linarith [h]

lemma unit_em (k : ℝ) (hk : Icc k (k + 1) ⊆ U) (n' : ℕ) (hn : 2 * n' + 1 ≤ m) :
    f (k + 1) = (∫ t in k..k + 1, f t) + (f (k + 1) - f k) / 2
      + (∑ i ∈ Finset.range n', ((bernoulli (2 * (i + 1)) : ℚ) : ℝ) / ((2 * (i + 1)).factorial : ℝ)
          * (iteratedDeriv (2 * i + 1) f (k + 1) - iteratedDeriv (2 * i + 1) f k))
      + ∫ t in k..k + 1, Q (2 * n' + 1) (t - k) * iteratedDeriv (2 * n' + 1) f t := by
  induction n' with
  | zero =>
    have h := ibp f U hU m hf k hk 0 (by omega)
    have hQ0 : ∀ s, Q 0 s = 1 := fun s => by simp [Q, bernoulliFun_zero]
    have hQ11 : Q 1 1 = 1 / 2 := by simp [Q, bernoulliFun_one]; norm_num
    have hQ10 : Q 1 0 = -1 / 2 := by simp [Q, bernoulliFun_one]; norm_num
    simp only [hQ0, one_mul, iteratedDeriv_zero, hQ11, hQ10] at h
    simp only [Finset.range_zero, Finset.sum_empty, add_zero, mul_zero, zero_add]
    linarith
  | succ n ih =>
    have ih' := ih (by omega)
    have h1 := ibp f U hU m hf k hk (2 * n + 1) (by omega)
    have h2 := ibp f U hU m hf k hk (2 * n + 1 + 1) (by omega)
    have e1 : Q (2 * n + 1 + 1) 1 = ((bernoulli (2 * (n + 1)) : ℚ) : ℝ) / ((2 * (n + 1)).factorial : ℝ) := by
      rw [Q_one_eq_zero _ (by omega), Q_zero_val]; ring_nf
    have e1' : Q (2 * n + 1 + 1) 0 = ((bernoulli (2 * (n + 1)) : ℚ) : ℝ) / ((2 * (n + 1)).factorial : ℝ) := by
      rw [Q_zero_val]; ring_nf
    have hodd : bernoulli (2 * n + 1 + 1 + 1) = 0 :=
      bernoulli_eq_zero_of_odd ⟨n + 1, by ring⟩ (by omega)
    have e2 : Q (2 * n + 1 + 1 + 1) 1 = 0 := by
      rw [Q_one_eq_zero _ (by omega), Q_zero_val, hodd]; simp
    have e2' : Q (2 * n + 1 + 1 + 1) 0 = 0 := by
      rw [Q_zero_val, hodd]; simp
    rw [e1, e1'] at h1
    rw [e2, e2'] at h2
    rw [Finset.sum_range_succ]
    have h3 : 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 := by ring
    rw [h3]
    linarith

lemma P_eq (j : ℕ) (k : ℕ) : EqOn (fun t => Pb j t)
    (fun t => Q j (t - k)) (uIoo (k : ℝ) (k + 1)) := by
  intro t ht
  rw [uIoo_of_le (by linarith)] at ht
  have hfl : ⌊t⌋ = (k : ℤ) := by
    rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith [ht.1, ht.2]
  simp only [Pb, Q, Int.fract, hfl]
  push_cast; ring_nf

lemma sum_em (hU0 : Ici (0 : ℝ) ⊆ U) (x : ℕ) (n : ℕ) (hn : 2 * n + 1 ≤ m) :
    (∑ k ∈ Finset.range x, f ((k : ℝ) + 1)) = (∫ t in (0 : ℝ)..(x : ℝ), f t) + (f x - f 0) / 2
      + (∑ i ∈ Finset.range n, ((bernoulli (2 * (i + 1)) : ℚ) : ℝ) / ((2 * (i + 1)).factorial : ℝ)
          * (iteratedDeriv (2 * i + 1) f x - iteratedDeriv (2 * i + 1) f 0))
      + ∫ t in (0 : ℝ)..(x : ℝ), Pb (2 * n + 1) t *
          iteratedDeriv (2 * n + 1) f t := by
  have hk : ∀ k : ℕ, Icc (k : ℝ) (k + 1) ⊆ U := fun k t ht => hU0 (le_trans (by positivity) ht.1)
  have hD : ∀ j ≤ m, ∀ k : ℕ, IntervalIntegrable (iteratedDeriv j f) volume (k : ℝ) ((k : ℝ) + 1) := by
    intro j hj k
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by linarith)]
    exact (D_cont f U hU m hf j hj).mono (hk k)
  have hunit := fun k : ℕ => unit_em f U hU m hf (k : ℝ) (hk k) n hn
  rw [Finset.sum_congr rfl (fun k _ => hunit k)]
  simp only [Finset.sum_add_distrib]
  -- integrals of f
  have hf0 : ∀ k < x, IntervalIntegrable f volume ((fun i : ℕ => (i : ℝ)) k) ((fun i : ℕ => (i : ℝ)) (k + 1)) := by
    intro k _
    have := hD 0 (Nat.zero_le _) k
    simp only [iteratedDeriv_zero] at this
    simpa using this
  have I1 := intervalIntegral.sum_integral_adjacent_intervals hf0
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at I1
  -- integrals of P D
  have hPD : ∀ k < x, IntervalIntegrable (fun t => Pb (2 * n + 1) t *
      iteratedDeriv (2 * n + 1) f t) volume ((fun i : ℕ => (i : ℝ)) k) ((fun i : ℕ => (i : ℝ)) (k + 1)) := by
    intro k _
    have h1 : IntervalIntegrable (fun t => Q (2 * n + 1) (t - k) * iteratedDeriv (2 * n + 1) f t) volume
        (k : ℝ) ((k : ℝ) + 1) := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (by linarith)]
      exact (((Q_cont _).comp (continuous_id.sub continuous_const)).continuousOn).mul
        ((D_cont f U hU m hf _ hn).mono (hk k))
    simp only [Nat.cast_add, Nat.cast_one]
    exact h1.congr_uIoo (fun t ht => by have hP := P_eq f U hU m hf (2 * n + 1) k ht; simp only at hP ⊢; rw [hP])
  have I2 := intervalIntegral.sum_integral_adjacent_intervals hPD
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at I2
  have hPQ : ∀ k : ℕ, ∫ t in (k : ℝ)..(k : ℝ) + 1, Q (2 * n + 1) (t - k) * iteratedDeriv (2 * n + 1) f t =
      ∫ t in (k : ℝ)..(k : ℝ) + 1, Pb (2 * n + 1) t *
        iteratedDeriv (2 * n + 1) f t := by
    intro k
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    have hP := P_eq f U hU m hf (2 * n + 1) k ht; simp only at hP ⊢; rw [hP]
  simp only [hPQ]
  rw [I1, I2]
  -- telescoping
  have T1 : ∑ k ∈ Finset.range x, (f ((k : ℝ) + 1) - f k) / 2 = (f x - f 0) / 2 := by
    rw [← Finset.sum_div]
    have := Finset.sum_range_sub (fun k : ℕ => f k) x
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at this
    rw [this]
  have T2 : ∑ k ∈ Finset.range x, ∑ i ∈ Finset.range n,
      ((bernoulli (2 * (i + 1)) : ℚ) : ℝ) / ((2 * (i + 1)).factorial : ℝ)
          * (iteratedDeriv (2 * i + 1) f ((k : ℝ) + 1) - iteratedDeriv (2 * i + 1) f k) =
      ∑ i ∈ Finset.range n, ((bernoulli (2 * (i + 1)) : ℚ) : ℝ) / ((2 * (i + 1)).factorial : ℝ)
          * (iteratedDeriv (2 * i + 1) f x - iteratedDeriv (2 * i + 1) f 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.mul_sum]
    congr 1
    have := Finset.sum_range_sub (fun k : ℕ => iteratedDeriv (2 * i + 1) f k) x
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at this
    rw [this]
  rw [T1, T2]

end

end RN8EM


namespace RN8EM
open Real Set MeasureTheory intervalIntegral Filter Topology

lemma Pb_bound (j : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ t, |Pb j t| ≤ K := by
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    ((continuous_bernoulliFun j).continuousOn)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 ⟨le_rfl, zero_le_one⟩)
  refine ⟨K / (j.factorial : ℝ), by positivity, fun t => ?_⟩
  have h := hK (Int.fract t) ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
  rw [Real.norm_eq_abs] at h
  unfold Pb
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < j.factorial)]
  exact div_le_div_of_nonneg_right h (by positivity)

lemma Pb_meas (j : ℕ) : Measurable (Pb j) := by
  unfold Pb
  exact ((continuous_bernoulliFun j).measurable.comp measurable_fract).div_const _

/-- antiderivative data for `(t+1)^{-(m+1)}` -/
lemma pow_int (m : ℕ) (hm : 1 ≤ m) (x : ℝ) (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ => 1 / (t + 1) ^ (m + 1)) (Ioi x) ∧
    ∫ t in Ioi x, 1 / (t + 1) ^ (m + 1) = 1 / ((m : ℝ) * (x + 1) ^ m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  let G : ℝ → ℝ := fun t => -((m : ℝ) * (t + 1) ^ m)⁻¹
  have hG : ∀ t ∈ Ici x, HasDerivAt G (1 / (t + 1) ^ (m + 1)) t := by
    intro t ht
    have ht1 : 0 < t + 1 := by have := ht.out; linarith
    have h1 : HasDerivAt (fun s : ℝ => (s + 1) ^ m) ((m : ℝ) * (t + 1) ^ (m - 1)) t := by
      have := (hasDerivAt_pow m (t + 1)).comp t ((hasDerivAt_id t).add_const 1)
      simpa [Function.comp_def] using this
    have h2 : HasDerivAt G (-(-((m : ℝ) * ((m : ℝ) * (t + 1) ^ (m - 1))) / ((m : ℝ) * (t + 1) ^ m) ^ 2)) t :=
      ((h1.const_mul (m : ℝ)).inv (by positivity)).neg
    refine h2.congr_deriv ?_
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    field_simp
    ring
  have hpos : ∀ t ∈ Ioi x, 0 ≤ 1 / (t + 1) ^ (m + 1) := by
    intro t ht; have := ht.out; have : 0 < t + 1 := by linarith
    positivity
  have hlim : Tendsto G atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => (m : ℝ) * (t + 1) ^ m) atTop atTop := by
      apply Tendsto.const_mul_atTop hm'
      exact (tendsto_pow_atTop (by omega)).comp (tendsto_atTop_add_const_right _ 1 tendsto_id)
    have h2 := h1.inv_tendsto_atTop
    have h3 := h2.neg
    simp only [neg_zero] at h3
    exact h3
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hG hpos hlim, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hG hpos hlim]
  simp [G]

/-- remainder bound -/
lemma rem_bound (j m : ℕ) (hm : 1 ≤ m) (c : ℝ) (hc : 0 ≤ c) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Ioi (-1))) (hb : ∀ t, 0 ≤ t → |g t| ≤ c / (t + 1) ^ (m + 1)) :
    IntegrableOn (fun t => Pb j t * g t) (Ioi 0) ∧
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 0 ≤ x → |∫ t in Ioi x, Pb j t * g t| ≤ K / (x + 1) ^ m := by
  obtain ⟨K, hK0, hK⟩ := Pb_bound j
  have hmeas : ∀ x : ℝ, 0 ≤ x → AEStronglyMeasurable (fun t => Pb j t * g t) (volume.restrict (Ioi x)) := by
    intro x hx
    apply AEStronglyMeasurable.mul
    · exact (Pb_meas j).aestronglyMeasurable
    · exact (hg.mono (fun t ht => by have := ht.out; simp only [mem_Ioi]; linarith)).aestronglyMeasurable
        measurableSet_Ioi
  have hbd : ∀ x : ℝ, 0 ≤ x → ∀ t ∈ Ioi x, ‖Pb j t * g t‖ ≤ K * c * (1 / (t + 1) ^ (m + 1)) := by
    intro x hx t ht
    have ht0 : 0 ≤ t := le_trans hx (le_of_lt ht)
    rw [Real.norm_eq_abs, abs_mul]
    have := hb t ht0
    calc |Pb j t| * |g t| ≤ K * (c / (t + 1) ^ (m + 1)) :=
          mul_le_mul (hK t) this (abs_nonneg _) hK0
      _ = K * c * (1 / (t + 1) ^ (m + 1)) := by ring
  have hint : ∀ x : ℝ, 0 ≤ x → IntegrableOn (fun t => Pb j t * g t) (Ioi x) := by
    intro x hx
    refine Integrable.mono' (((pow_int m hm x hx).1).const_mul (K * c)) (hmeas x hx) ?_
    exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall (hbd x hx))
  refine ⟨hint 0 le_rfl, K * c / m, by positivity, fun x hx => ?_⟩
  have h := norm_integral_le_of_norm_le (((pow_int m hm x hx).1).const_mul (K * c))
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall (hbd x hx)))
  rw [Real.norm_eq_abs] at h
  refine h.trans (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul, (pow_int m hm x hx).2]
  field_simp

/-- Euler–Maclaurin with tail remainder and an unspecified constant -/
lemma em_tail (f : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U) (hU0 : Ici (0 : ℝ) ⊆ U) (n : ℕ)
    (hf : ContDiffOn ℝ ((2 * n + 1 : ℕ) : WithTop ℕ∞) f U)
    (hint : IntegrableOn (fun t => Pb (2 * n + 1) t * iteratedDeriv (2 * n + 1) f t) (Ioi 0)) :
    ∃ C : ℝ, ∀ x : ℕ, (∑ k ∈ Finset.range x, f ((k : ℝ) + 1)) = (∫ t in (0 : ℝ)..(x : ℝ), f t)
      + f x / 2
      + (∑ i ∈ Finset.range n, ((bernoulli (2 * (i + 1)) : ℚ) : ℝ) / ((2 * (i + 1)).factorial : ℝ)
          * iteratedDeriv (2 * i + 1) f x)
      - (∫ t in Ioi (x : ℝ), Pb (2 * n + 1) t * iteratedDeriv (2 * n + 1) f t) + C := by
  refine ⟨-(f 0 / 2) - (∑ i ∈ Finset.range n, ((bernoulli (2 * (i + 1)) : ℚ) : ℝ) /
      ((2 * (i + 1)).factorial : ℝ) * iteratedDeriv (2 * i + 1) f 0)
      + ∫ t in Ioi (0 : ℝ), Pb (2 * n + 1) t * iteratedDeriv (2 * n + 1) f t, fun x => ?_⟩
  rw [sum_em f U hU (2 * n + 1) hf hU0 x n le_rfl]
  have hx0 : (0 : ℝ) ≤ x := by positivity
  have hP : (∫ t in Set.Ioi (0 : ℝ), Pb (2 * n + 1) t * iteratedDeriv (2 * n + 1) f t) =
      (∫ t in (0 : ℝ)..(x : ℝ), Pb (2 * n + 1) t * iteratedDeriv (2 * n + 1) f t) +
      ∫ t in Set.Ioi (x : ℝ), Pb (2 * n + 1) t * iteratedDeriv (2 * n + 1) f t := by
    rw [intervalIntegral.integral_of_le hx0, ← Ioc_union_Ioi_eq_Ioi hx0]
    exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hx0))
  rw [hP]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

end RN8EM


namespace RN8EM
open Real Set MeasureTheory intervalIntegral Filter Topology

noncomputable def f1 (t : ℝ) : ℝ := Real.log (t + 1) / (t + 1)
noncomputable def f2 (t : ℝ) : ℝ := 1 / (t + 1)
noncomputable def H (j : ℕ) : ℝ := ∑ i ∈ Finset.range j, 1 / ((i : ℝ) + 1)

lemma f1_cd (m : ℕ) : ContDiffOn ℝ (m : WithTop ℕ∞) f1 (Ioi (-1)) := by
  have h1 : ContDiffOn ℝ (m : WithTop ℕ∞) (fun t : ℝ => t + 1) (Ioi (-1)) :=
    (contDiff_id.add contDiff_const).contDiffOn
  have h2 : ContDiffOn ℝ (m : WithTop ℕ∞) (fun t : ℝ => Real.log (t + 1)) (Ioi (-1)) := by
    apply (Real.contDiffOn_log.comp h1)
    intro t ht; have := ht.out; simp only [mem_compl_iff, mem_singleton_iff]; linarith
  exact h2.div h1 (fun t ht => by have := ht.out; linarith)

lemma f2_cd (m : ℕ) : ContDiffOn ℝ (m : WithTop ℕ∞) f2 (Ioi (-1)) := by
  have h1 : ContDiffOn ℝ (m : WithTop ℕ∞) (fun t : ℝ => t + 1) (Ioi (-1)) :=
    (contDiff_id.add contDiff_const).contDiffOn
  exact contDiffOn_const.div h1 (fun t ht => by have := ht.out; linarith)

lemma hp_deriv (j : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (s + 1) ^ (j + 1)) (((j + 1 : ℕ) : ℝ) * (t + 1) ^ j) t := by
  have := (hasDerivAt_pow (j + 1) (t + 1)).comp t ((hasDerivAt_id t).add_const 1)
  simpa [Function.comp_def] using this

lemma d1 (j : ℕ) : ∀ t : ℝ, -1 < t → iteratedDeriv j f1 t =
    (-1) ^ j * (j.factorial : ℝ) * (Real.log (t + 1) - H j) / (t + 1) ^ (j + 1) := by
  induction j with
  | zero => intro t ht; simp [f1, H]
  | succ j ih =>
    intro t ht
    have ht1 : 0 < t + 1 := by linarith
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv j f1 =ᶠ[𝓝 t] fun s =>
        (-1) ^ j * (j.factorial : ℝ) * (Real.log (s + 1) - H j) / (s + 1) ^ (j + 1) :=
      Filter.eventually_of_mem (isOpen_Ioi.mem_nhds (show t ∈ Ioi (-1) from ht)) (fun s hs => ih s hs)
    rw [heq.deriv_eq]
    have hl : HasDerivAt (fun s : ℝ => Real.log (s + 1)) ((t + 1)⁻¹) t := by
      have := ((hasDerivAt_id t).add_const 1).log (ne_of_gt ht1)
      simpa [one_div] using this
    have hd0 := ((hl.sub_const (H j)).const_mul ((-1) ^ j * (j.factorial : ℝ))).div (hp_deriv j t)
      (by positivity)
    have hd : HasDerivAt (fun s => (-1) ^ j * (j.factorial : ℝ) * (Real.log (s + 1) - H j) / (s + 1) ^ (j + 1)) _ t := hd0
    rw [hd.deriv]
    have hH : H (j + 1) = H j + 1 / ((j : ℝ) + 1) := by
      simp [H, Finset.sum_range_succ]
    rw [hH, Nat.factorial_succ]
    push_cast
    field_simp
    ring

lemma d2 (j : ℕ) : ∀ t : ℝ, -1 < t → iteratedDeriv j f2 t =
    (-1) ^ j * (j.factorial : ℝ) / (t + 1) ^ (j + 1) := by
  induction j with
  | zero => intro t ht; simp [f2]
  | succ j ih =>
    intro t ht
    have ht1 : 0 < t + 1 := by linarith
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv j f2 =ᶠ[𝓝 t] fun s =>
        (-1) ^ j * (j.factorial : ℝ) / (s + 1) ^ (j + 1) :=
      Filter.eventually_of_mem (isOpen_Ioi.mem_nhds (show t ∈ Ioi (-1) from ht)) (fun s hs => ih s hs)
    rw [heq.deriv_eq]
    have hd0 := (hasDerivAt_const t ((-1) ^ j * (j.factorial : ℝ))).div (hp_deriv j t) (by positivity)
    have hd : HasDerivAt (fun s => (-1) ^ j * (j.factorial : ℝ) / (s + 1) ^ (j + 1)) _ t := hd0
    rw [hd.deriv, Nat.factorial_succ]
    push_cast
    field_simp
    ring

lemma H_nonneg (j : ℕ) : 0 ≤ H j := by
  unfold H; apply Finset.sum_nonneg; intro i _; positivity

lemma d1_bound (J : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    |iteratedDeriv J f1 t| ≤ (J.factorial : ℝ) * (1 + H J) / (t + 1) ^ J := by
  rw [d1 J t (by linarith)]
  have ht1 : 1 ≤ t + 1 := by linarith
  have hL0 : 0 ≤ Real.log (t + 1) := Real.log_nonneg ht1
  have hL : Real.log (t + 1) ≤ t + 1 := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < t + 1); linarith
  have hH := H_nonneg J
  rw [abs_div, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (by positivity : (0 : ℝ) < J.factorial), abs_of_pos (by positivity : (0 : ℝ) < (t + 1) ^ (J + 1))]
  rw [div_le_div_iff₀ (by positivity) (by positivity), pow_succ]
  have hab : |Real.log (t + 1) - H J| ≤ (1 + H J) * (t + 1) := by
    rw [abs_le]; constructor <;> nlinarith
  have hf : (0 : ℝ) ≤ J.factorial := by positivity
  have hp : (0 : ℝ) ≤ (t + 1) ^ J := by positivity
  calc (J.factorial : ℝ) * |Real.log (t + 1) - H J| * (t + 1) ^ J
      ≤ (J.factorial : ℝ) * ((1 + H J) * (t + 1)) * (t + 1) ^ J := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hab hf) hp
    _ = (J.factorial : ℝ) * (1 + H J) * ((t + 1) ^ J * (t + 1)) := by ring

lemma d2_bound (J : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    |iteratedDeriv J f2 t| ≤ (J.factorial : ℝ) / (t + 1) ^ (J + 1) := by
  rw [d2 J t (by linarith)]
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (by positivity : (0 : ℝ) < J.factorial), abs_of_pos (by positivity : (0 : ℝ) < (t + 1) ^ (J + 1))]

end RN8EM


namespace RN8Main
open Real Set MeasureTheory intervalIntegral Filter Topology RN8EM

lemma lim_aux (p : ℕ) (hp : 1 ≤ p) (a b : ℝ) :
    Tendsto (fun x : ℕ => (a * Real.log ((x : ℝ) + 1) + b) / ((x : ℝ) + 1) ^ p) atTop (𝓝 0) := by
  have hy : Tendsto (fun x : ℕ => (x : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hL : Tendsto (fun x : ℕ => Real.log ((x : ℝ) + 1) / ((x : ℝ) + 1)) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hy
    simpa [Function.comp_def] using this
  have hI : Tendsto (fun x : ℕ => 1 / ((x : ℝ) + 1)) atTop (𝓝 0) := by
    have := tendsto_inv_atTop_zero.comp hy
    simpa [Function.comp_def, one_div] using this
  have hsum : Tendsto (fun x : ℕ => |a| * (Real.log ((x : ℝ) + 1) / ((x : ℝ) + 1)) +
      |b| * (1 / ((x : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (hL.const_mul |a|).add (hI.const_mul |b|)
  apply squeeze_zero_norm' _ hsum
  filter_upwards with x
  have hy1 : (1 : ℝ) ≤ (x : ℝ) + 1 := by have : (0 : ℝ) ≤ x := Nat.cast_nonneg x; linarith
  have hL0 : 0 ≤ Real.log ((x : ℝ) + 1) := Real.log_nonneg hy1
  have hpow : (x : ℝ) + 1 ≤ ((x : ℝ) + 1) ^ p := le_self_pow₀ hy1 (by omega)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((x : ℝ) + 1) ^ p)]
  calc |a * Real.log (↑x + 1) + b| / (↑x + 1) ^ p ≤ (|a| * Real.log (↑x + 1) + |b|) / (↑x + 1) := by
        apply div_le_div₀ (by positivity) _ (by positivity) hpow
        calc |a * Real.log (↑x + 1) + b| ≤ |a * Real.log (↑x + 1)| + |b| := abs_add_le _ _
          _ = |a| * Real.log (↑x + 1) + |b| := by rw [abs_mul, abs_of_nonneg hL0]
    _ = _ := by ring

noncomputable def bb (i : ℕ) : ℝ := ((bernoulli (2 * (i + 1)) : ℚ) : ℝ) / ((2 * (i + 1)).factorial : ℝ)

lemma hl_deriv (t : ℝ) (ht1 : 0 < t + 1) : HasDerivAt (fun s : ℝ => Real.log (s + 1)) ((t + 1)⁻¹) t := by
  have := ((hasDerivAt_id t).add_const 1).log (ne_of_gt ht1)
  simpa [one_div] using this

lemma int_f1 (x : ℝ) (hx : 0 ≤ x) : ∫ t in (0 : ℝ)..x, f1 t = Real.log (x + 1) ^ 2 / 2 := by
  have hd : ∀ t ∈ uIcc (0 : ℝ) x,
      HasDerivAt (fun s => Real.log (s + 1) * Real.log (s + 1) / 2) (f1 t) t := by
    intro t ht
    rw [uIcc_of_le hx] at ht
    have ht1 : 0 < t + 1 := by linarith [ht.1]
    have h := ((hl_deriv t ht1).mul (hl_deriv t ht1)).div_const 2
    refine h.congr_deriv ?_
    rw [show f1 t = Real.log (t + 1) / (t + 1) from rfl]
    field_simp
    ring
  have hc : ContinuousOn f1 (uIcc 0 x) := by
    rw [uIcc_of_le hx]
    exact ((f1_cd 0).continuousOn).mono (fun t ht => by simp only [mem_Ioi]; linarith [ht.1])
  rw [integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable)]
  simp; ring

lemma int_f2 (x : ℝ) (hx : 0 ≤ x) : ∫ t in (0 : ℝ)..x, f2 t = Real.log (x + 1) := by
  have hd : ∀ t ∈ uIcc (0 : ℝ) x, HasDerivAt (fun s => Real.log (s + 1)) (f2 t) t := by
    intro t ht
    rw [uIcc_of_le hx] at ht
    have ht1 : 0 < t + 1 := by linarith [ht.1]
    refine (hl_deriv t ht1).congr_deriv ?_
    rw [show f2 t = 1 / (t + 1) from rfl, one_div]
  have hc : ContinuousOn f2 (uIcc 0 x) := by
    rw [uIcc_of_le hx]
    exact ((f2_cd 0).continuousOn).mono (fun t ht => by simp only [mem_Ioi]; linarith [ht.1])
  rw [integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable)]
  simp

lemma odd_pow (i : ℕ) : ((-1 : ℝ)) ^ (2 * i + 1) = -1 := Odd.neg_one_pow ⟨i, rfl⟩

lemma term_id (i : ℕ) (y : ℝ) (hy : 0 < y) :
    bb i * ((-1) ^ (2 * i + 1) * ((2 * i + 1).factorial : ℝ) * (Real.log y - H (2 * i + 1)) / y ^ (2 * i + 1 + 1))
    - Real.log y * (bb i * ((-1) ^ (2 * i + 1) * ((2 * i + 1).factorial : ℝ) / y ^ (2 * i + 1 + 1)))
    = (bernoulli (2 * i + 2) : ℝ) * H (2 * i + 1) / ((2 * (i : ℝ) + 2) * y ^ (2 * i + 2)) := by
  rw [odd_pow]
  unfold bb
  have e : 2 * (i + 1) = 2 * i + 1 + 1 := by ring
  rw [e, Nat.factorial_succ]
  have e2 : 2 * i + 2 = 2 * i + 1 + 1 := by ring
  rw [e2]
  push_cast
  field_simp
  ring

end RN8Main


open Real Set MeasureTheory intervalIntegral Filter Topology RN8EM RN8Main

theorem solution (c₁ : ℝ)
    (hc : Filter.Tendsto
      (fun n : ℕ => (∑ k ∈ Finset.range n, Real.log ((k : ℝ) + 1) / ((k : ℝ) + 1))
        - Real.log (n : ℝ) ^ 2 / 2) Filter.atTop (nhds c₁))
    (M : ℕ) :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ => (∑ k ∈ Finset.range n, Real.log ((k : ℝ) + 1) / ((k : ℝ) + 1))
        - logDeriv Real.Gamma ((n : ℝ) + 1) * Real.log (n : ℝ)
        - (-(Real.log (n : ℝ) ^ 2) / 2 + c₁
            + ∑ k ∈ Finset.range M, (bernoulli (2 * k + 2) : ℝ)
                * (∑ j ∈ Finset.range (2 * k + 1), 1 / ((j : ℝ) + 1))
                / ((2 * (k : ℝ) + 2) * (n : ℝ) ^ (2 * k + 2))))
      (fun n : ℕ => 1 / (n : ℝ) ^ (2 * M + 2)) := by
  have hU0 : Ici (0 : ℝ) ⊆ Ioi (-1) := fun t ht => by
    simp only [mem_Ici] at ht; simp only [mem_Ioi]; linarith
  have e1 : 2 * (M + 1) + 1 = 2 * M + 2 + 1 := by ring
  have hJ1 : ∀ t : ℝ, 0 ≤ t → |iteratedDeriv (2 * (M + 1) + 1) f1 t| ≤
      ((2 * (M + 1) + 1).factorial : ℝ) * (1 + H (2 * (M + 1) + 1)) / (t + 1) ^ (2 * M + 2 + 1) := by
    intro t ht
    have := d1_bound (2 * (M + 1) + 1) t ht
    rwa [e1] at this ⊢
  have hJ2 : ∀ t : ℝ, 0 ≤ t → |iteratedDeriv (2 * (M + 1) + 1) f2 t| ≤
      ((2 * (M + 1) + 1).factorial : ℝ) / (t + 1) ^ (2 * M + 3 + 1) := by
    intro t ht
    have := d2_bound (2 * (M + 1) + 1) t ht
    have e2 : 2 * (M + 1) + 1 + 1 = 2 * M + 3 + 1 := by ring
    rwa [e2] at this
  obtain ⟨hint1, K1, hK1, hT1⟩ := rem_bound (2 * (M + 1) + 1) (2 * M + 2) (by omega) _
    (by have := H_nonneg (2 * (M + 1) + 1); positivity) _
    (D_cont f1 (Ioi (-1)) isOpen_Ioi (2 * (M + 1) + 1) (f1_cd _) (2 * (M + 1) + 1) le_rfl) hJ1
  obtain ⟨hint2, K2, hK2, hT2⟩ := rem_bound (2 * (M + 1) + 1) (2 * M + 3) (by omega) _
    (by positivity) _
    (D_cont f2 (Ioi (-1)) isOpen_Ioi (2 * (M + 1) + 1) (f2_cd _) (2 * (M + 1) + 1) le_rfl) hJ2
  obtain ⟨C1, hC1⟩ := em_tail f1 (Ioi (-1)) isOpen_Ioi hU0 (M + 1) (f1_cd _) hint1
  obtain ⟨C2, hC2⟩ := em_tail f2 (Ioi (-1)) isOpen_Ioi hU0 (M + 1) (f2_cd _) hint2
  -- notation-free abbreviations via functions
  obtain ⟨T1, hT1d⟩ : ∃ T1 : ℕ → ℝ, T1 = fun x : ℕ =>
      ∫ t in Ioi (x : ℝ), Pb (2 * (M + 1) + 1) t * iteratedDeriv (2 * (M + 1) + 1) f1 t := ⟨_, rfl⟩
  obtain ⟨T2, hT2d⟩ : ∃ T2 : ℕ → ℝ, T2 = fun x : ℕ =>
      ∫ t in Ioi (x : ℝ), Pb (2 * (M + 1) + 1) t * iteratedDeriv (2 * (M + 1) + 1) f2 t := ⟨_, rfl⟩
  have hT1b : ∀ x : ℕ, |T1 x| ≤ K1 / ((x : ℝ) + 1) ^ (2 * M + 2) := by
    intro x; rw [hT1d]; exact hT1 x (Nat.cast_nonneg x)
  have hT2b : ∀ x : ℕ, |T2 x| ≤ K2 / ((x : ℝ) + 1) ^ (2 * M + 3) := by
    intro x; rw [hT2d]; exact hT2 x (Nat.cast_nonneg x)
  -- the two Euler–Maclaurin expansions
  have hA : ∀ x : ℕ, (∑ k ∈ Finset.range (x + 1), Real.log ((k : ℝ) + 1) / ((k : ℝ) + 1)) =
      Real.log ((x : ℝ) + 1) ^ 2 / 2 + f1 x / 2
        + (∑ i ∈ Finset.range (M + 1), bb i * iteratedDeriv (2 * i + 1) f1 x) - T1 x + C1 := by
    intro x
    have hs : (∑ k ∈ Finset.range (x + 1), Real.log ((k : ℝ) + 1) / ((k : ℝ) + 1)) =
        ∑ k ∈ Finset.range x, f1 ((k : ℝ) + 1) := by
      rw [Finset.sum_range_succ']
      simp only [f1]
      push_cast
      simp
    rw [hs, hC1 x, int_f1 _ (Nat.cast_nonneg x), hT1d]
    simp only [bb]
  have hHs : ∀ x : ℕ, ((harmonic (x + 1) : ℚ) : ℝ) =
      1 + Real.log ((x : ℝ) + 1) + f2 x / 2
        + (∑ i ∈ Finset.range (M + 1), bb i * iteratedDeriv (2 * i + 1) f2 x) - T2 x + C2 := by
    intro x
    have hs : ((harmonic (x + 1) : ℚ) : ℝ) = 1 + ∑ k ∈ Finset.range x, f2 ((k : ℝ) + 1) := by
      rw [harmonic, Finset.sum_range_succ']
      push_cast
      simp only [f2]
      rw [add_comm]
      congr 1
      · simp
      · apply Finset.sum_congr rfl; intro k _; rw [one_div]
    rw [hs, hC2 x, int_f2 _ (Nat.cast_nonneg x), hT2d]
    simp only [bb]
    ring
  have hlog : ∀ x : ℕ, logDeriv Real.Gamma ((x : ℝ) + 1 + 1) =
      ((harmonic (x + 1) : ℚ) : ℝ) - eulerMascheroniConstant := by
    intro x
    have h1 := Real.deriv_Gamma_nat (x + 1)
    have h2 := Real.Gamma_nat_eq_factorial (x + 1)
    push_cast at h1 h2
    rw [logDeriv_apply, h1, h2]
    have : ((x + 1).factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  -- limits of the remainders
  have hy : ∀ x : ℕ, (-1 : ℝ) < (x : ℝ) := fun x => by
    have := Nat.cast_nonneg (α := ℝ) x; linarith
  have hr1 : Tendsto (fun x : ℕ => f1 x / 2
      + (∑ i ∈ Finset.range (M + 1), bb i * iteratedDeriv (2 * i + 1) f1 x) - T1 x) atTop (𝓝 0) := by
    have a1 : Tendsto (fun x : ℕ => f1 x / 2) atTop (𝓝 0) := by
      have := lim_aux 1 le_rfl (1 / 2) 0
      refine this.congr (fun x => ?_)
      simp only [f1]; ring
    have a2 : Tendsto (fun x : ℕ => ∑ i ∈ Finset.range (M + 1), bb i * iteratedDeriv (2 * i + 1) f1 x)
        atTop (𝓝 0) := by
      rw [show (0 : ℝ) = ∑ i ∈ Finset.range (M + 1), (0 : ℝ) by simp]
      apply tendsto_finsetSum
      intro i _
      have := (lim_aux (2 * i + 1 + 1) (by omega) 1 (-H (2 * i + 1))).const_mul
        (bb i * ((-1) ^ (2 * i + 1) * ((2 * i + 1).factorial : ℝ)))
      rw [mul_zero] at this
      refine this.congr (fun x => ?_)
      rw [d1 _ _ (hy x)]; ring
    have a3 : Tendsto T1 atTop (𝓝 0) := by
      apply squeeze_zero_norm' _ (lim_aux (2 * M + 2) (by omega) 0 K1)
      filter_upwards with x
      rw [Real.norm_eq_abs]; simpa using hT1b x
    simpa using (a1.add a2).sub a3
  have hr2 : Tendsto (fun x : ℕ => f2 x / 2
      + (∑ i ∈ Finset.range (M + 1), bb i * iteratedDeriv (2 * i + 1) f2 x) - T2 x) atTop (𝓝 0) := by
    have a1 : Tendsto (fun x : ℕ => f2 x / 2) atTop (𝓝 0) := by
      have := lim_aux 1 le_rfl 0 (1 / 2)
      refine this.congr (fun x => ?_)
      simp only [f2]; ring
    have a2 : Tendsto (fun x : ℕ => ∑ i ∈ Finset.range (M + 1), bb i * iteratedDeriv (2 * i + 1) f2 x)
        atTop (𝓝 0) := by
      rw [show (0 : ℝ) = ∑ i ∈ Finset.range (M + 1), (0 : ℝ) by simp]
      apply tendsto_finsetSum
      intro i _
      have := (lim_aux (2 * i + 1 + 1) (by omega) 0 1).const_mul
        (bb i * ((-1) ^ (2 * i + 1) * ((2 * i + 1).factorial : ℝ)))
      rw [mul_zero] at this
      refine this.congr (fun x => ?_)
      rw [d2 _ _ (hy x)]; ring
    have a3 : Tendsto T2 atTop (𝓝 0) := by
      apply squeeze_zero_norm' _ (lim_aux (2 * M + 3) (by omega) 0 K2)
      filter_upwards with x
      rw [Real.norm_eq_abs]; simpa using hT2b x
    simpa using (a1.add a2).sub a3
  -- identification of the constants
  have hC1v : C1 = c₁ := by
    have t1 := hc.comp (tendsto_add_atTop_nat 1)
    have t2 := (tendsto_const_nhds (x := C1)).add hr1
    rw [add_zero] at t2
    refine tendsto_nhds_unique (t2.congr (fun x => ?_)) t1
    simp only [Function.comp_apply]
    rw [hA x]; push_cast; ring
  have hC2v : C2 = eulerMascheroniConstant - 1 := by
    have t1 := tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat 1)
    have t2 := (tendsto_const_nhds (x := 1 + C2)).add hr2
    rw [add_zero] at t2
    have := tendsto_nhds_unique (t2.congr (fun x => ?_)) t1
    · linarith
    simp only [Function.comp_apply]
    rw [hHs x]; push_cast; ring
  -- the final estimate
  obtain ⟨cl, hcl⟩ : ∃ cl : ℝ, cl = (bernoulli (2 * M + 2) : ℝ) * H (2 * M + 1) / (2 * (M : ℝ) + 2) :=
    ⟨_, rfl⟩
  have hH' : ∀ k : ℕ, (∑ j ∈ Finset.range (2 * k + 1), 1 / ((j : ℝ) + 1)) = H (2 * k + 1) :=
    fun k => rfl
  apply Asymptotics.IsBigO.of_bound (|cl| + K1 + K2)
  filter_upwards [eventually_ge_atTop 1] with n hn
  obtain ⟨x, rfl⟩ : ∃ x, n = x + 1 := ⟨n - 1, by omega⟩
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hy0 : (0 : ℝ) < (x : ℝ) + 1 := by linarith
  have hS : (∑ i ∈ Finset.range (M + 1), bb i * iteratedDeriv (2 * i + 1) f1 x)
      - Real.log ((x : ℝ) + 1) * (∑ i ∈ Finset.range (M + 1), bb i * iteratedDeriv (2 * i + 1) f2 x)
      = (∑ k ∈ Finset.range M, (bernoulli (2 * k + 2) : ℝ) * H (2 * k + 1)
          / ((2 * (k : ℝ) + 2) * ((x : ℝ) + 1) ^ (2 * k + 2)))
        + cl / ((x : ℝ) + 1) ^ (2 * M + 2) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    rw [Finset.sum_range_succ]
    have hterm : ∀ i : ℕ, bb i * iteratedDeriv (2 * i + 1) f1 x
        - Real.log ((x : ℝ) + 1) * (bb i * iteratedDeriv (2 * i + 1) f2 x)
        = (bernoulli (2 * i + 2) : ℝ) * H (2 * i + 1) / ((2 * (i : ℝ) + 2) * ((x : ℝ) + 1) ^ (2 * i + 2)) := by
      intro i
      rw [d1 _ _ (hy x), d2 _ _ (hy x)]
      exact term_id i _ hy0
    rw [Finset.sum_congr rfl (fun i _ => hterm i), hterm M, hcl]
    congr 1
    field_simp
  have hf1x : f1 x = Real.log ((x : ℝ) + 1) / ((x : ℝ) + 1) := rfl
  have hf2x : f2 x = 1 / ((x : ℝ) + 1) := rfl
  have key : (∑ k ∈ Finset.range (x + 1), Real.log ((k : ℝ) + 1) / ((k : ℝ) + 1))
        - logDeriv Real.Gamma ((((x + 1 : ℕ) : ℝ)) + 1) * Real.log (((x + 1 : ℕ) : ℝ))
        - (-(Real.log (((x + 1 : ℕ) : ℝ)) ^ 2) / 2 + c₁
            + ∑ k ∈ Finset.range M, (bernoulli (2 * k + 2) : ℝ)
                * (∑ j ∈ Finset.range (2 * k + 1), 1 / ((j : ℝ) + 1))
                / ((2 * (k : ℝ) + 2) * (((x + 1 : ℕ) : ℝ)) ^ (2 * k + 2)))
      = cl / ((x : ℝ) + 1) ^ (2 * M + 2) - T1 x + Real.log ((x : ℝ) + 1) * T2 x := by
    simp only [hH']
    push_cast
    rw [hlog x, hHs x, hA x, hC1v, hC2v, hf1x, hf2x]
    have hyne : (x : ℝ) + 1 ≠ 0 := ne_of_gt hy0
    linear_combination hS
  rw [key]
  have hL0 : 0 ≤ Real.log ((x : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hLy : Real.log ((x : ℝ) + 1) ≤ (x : ℝ) + 1 := by
    have := Real.log_le_sub_one_of_pos hy0; linarith
  have hp : (0 : ℝ) < ((x : ℝ) + 1) ^ (2 * M + 2) := by positivity
  have hnorm : ‖1 / (((x + 1 : ℕ) : ℝ)) ^ (2 * M + 2)‖ = 1 / ((x : ℝ) + 1) ^ (2 * M + 2) := by
    push_cast
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hnorm, Real.norm_eq_abs]
  have b1 : |cl / ((x : ℝ) + 1) ^ (2 * M + 2)| = |cl| / ((x : ℝ) + 1) ^ (2 * M + 2) := by
    rw [abs_div, abs_of_pos hp]
  have b3 : |Real.log ((x : ℝ) + 1) * T2 x| ≤ K2 / ((x : ℝ) + 1) ^ (2 * M + 2) := by
    rw [abs_mul, abs_of_nonneg hL0]
    calc Real.log ((x : ℝ) + 1) * |T2 x| ≤ ((x : ℝ) + 1) * (K2 / ((x : ℝ) + 1) ^ (2 * M + 3)) :=
          mul_le_mul hLy (hT2b x) (abs_nonneg _) (by linarith)
      _ = K2 / ((x : ℝ) + 1) ^ (2 * M + 2) := by
          rw [show 2 * M + 3 = 2 * M + 2 + 1 by ring, pow_succ]
          field_simp
  calc |cl / ((x : ℝ) + 1) ^ (2 * M + 2) - T1 x + Real.log ((x : ℝ) + 1) * T2 x|
      ≤ |cl / ((x : ℝ) + 1) ^ (2 * M + 2)| + |T1 x| + |Real.log ((x : ℝ) + 1) * T2 x| := by
        have := abs_add_le (cl / ((x : ℝ) + 1) ^ (2 * M + 2) - T1 x) (Real.log ((x : ℝ) + 1) * T2 x)
        have := abs_sub (cl / ((x : ℝ) + 1) ^ (2 * M + 2)) (T1 x)
        linarith
    _ ≤ |cl| / ((x : ℝ) + 1) ^ (2 * M + 2) + K1 / ((x : ℝ) + 1) ^ (2 * M + 2)
          + K2 / ((x : ℝ) + 1) ^ (2 * M + 2) := by
        rw [b1]; linarith [hT1b x, b3]
    _ = (|cl| + K1 + K2) * (1 / ((x : ℝ) + 1) ^ (2 * M + 2)) := by ring

