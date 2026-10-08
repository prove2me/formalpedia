-- Prove2me | solution 1 for QueueingFundamentals.Transient.mmInf_transient
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T16:57:29.723908+00:00
-- url     : https://prove2.me/submissions/2423a44e-7d3b-4611-9699-867324c26907

import Mathlib
import Definitions.Def_QueueingFundamentals_Transient_forwardEquations
import Definitions.Def_QueueingFundamentals_Transient_mmInfTransient



namespace QueueingFundamentals.Transient

open Filter Topology MeasureTheory

/-- algebraic telescoping identity -/
lemma qmi_tele (lam mu : ℝ) (q u : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (mmInfRHS lam mu q n * u n
      + q n * (-(lam * (u (n + 1) - u n) + (n : ℝ) * mu * (u (n - 1) - u n))))
      = -lam * q N * u (N + 1) + ((N : ℝ) + 1) * mu * q (N + 1) * u N := by
  induction N with
  | zero => simp [mmInfRHS]; ring
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [mmInfRHS, Nat.add_sub_cancel]
    push_cast
    ring

lemma qmi_cont {lam mu : ℝ} {q : ℕ → ℝ → ℝ} (hsol : IsForwardSolution (mmInfRHS lam mu) q)
    (n : ℕ) : ContinuousOn (q n) (Set.Ici 0) :=
  fun s hs => (hsol n s hs).continuousWithinAt

lemma qmi_rhs_cont {lam mu : ℝ} {q : ℕ → ℝ → ℝ} (hsol : IsForwardSolution (mmInfRHS lam mu) q)
    (n : ℕ) : ContinuousOn (fun s => mmInfRHS lam mu (fun m => q m s) n) (Set.Ici 0) := by
  cases n with
  | zero =>
    simp only [mmInfRHS]
    have h1 := qmi_cont hsol 0
    have h2 := qmi_cont hsol 1
    fun_prop
  | succ n =>
    simp only [mmInfRHS]
    have h1 := qmi_cont hsol (n + 1)
    have h2 := qmi_cont hsol n
    have h3 := qmi_cont hsol (n + 2)
    fun_prop

/-- Duality identity: for a dual family `u` solving the backward equations. -/
lemma qmi_dual {lam mu : ℝ} {q : ℕ → ℝ → ℝ} (hsol : IsForwardSolution (mmInfRHS lam mu) q)
    (u : ℕ → ℝ → ℝ)
    (hu : ∀ n s, HasDerivAt (u n) (-(lam * (u (n + 1) s - u n s) + (n : ℝ) * mu * (u (n - 1) s - u n s))) s)
    (N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ∑ n ∈ Finset.range (N + 1), q n t * u n t - ∑ n ∈ Finset.range (N + 1), q n 0 * u n 0
      = ∫ s in (0:ℝ)..t, (-lam * q N s * u (N + 1) s + ((N : ℝ) + 1) * mu * q (N + 1) s * u N s) := by
  have hucont : ∀ n, Continuous (u n) := fun n =>
    continuous_iff_continuousAt.2 (fun s => (hu n s).continuousAt)
  have hsub : Set.Icc 0 t ⊆ Set.Ici (0:ℝ) := fun s hs => hs.1
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht
  · apply continuousOn_finsetSum
    intro n _
    exact ((qmi_cont hsol n).mono hsub).mul (hucont n).continuousOn
  · intro s hs
    have hs0 : Set.Ici (0:ℝ) ∈ 𝓝 s := Ici_mem_nhds hs.1
    have hd : HasDerivAt (fun s => ∑ n ∈ Finset.range (N + 1), q n s * u n s)
        (∑ n ∈ Finset.range (N + 1), (mmInfRHS lam mu (fun m => q m s) n * u n s
          + q n s * (-(lam * (u (n + 1) s - u n s) + (n : ℝ) * mu * (u (n - 1) s - u n s))))) s := by
      apply HasDerivAt.fun_sum
      intro n _
      exact ((hsol n s hs.1.le).hasDerivAt hs0).mul (hu n s)
    rwa [qmi_tele lam mu (fun m => q m s) (fun m => u m s) N] at hd
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le ht]
    have h1 := (qmi_cont hsol N).mono hsub
    have h2 := (qmi_cont hsol (N + 1)).mono hsub
    have h3 := (hucont (N + 1)).continuousOn (s := Set.Icc 0 t)
    have h4 := (hucont N).continuousOn (s := Set.Icc 0 t)
    fun_prop

lemma qmi_int_tendsto {q : ℕ → ℝ → ℝ} (lam mu : ℝ) (hsol : IsForwardSolution (mmInfRHS lam mu) q)
    (hprob : IsProbabilityFamily q) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun N => ∫ s in (0:ℝ)..t, q N s) atTop (𝓝 0) := by
  have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (a := 0) (b := t) (l := atTop) (F := fun N s => q N s) (f := fun _ => (0:ℝ)) (fun _ => 1) ?_ ?_ ?_ ?_
  · simpa using h
  · refine Eventually.of_forall (fun N => ?_)
    rw [Set.uIoc_of_le ht]
    exact ((qmi_cont hsol N).mono (fun s hs => le_of_lt hs.1)).aestronglyMeasurable measurableSet_Ioc
  · refine Eventually.of_forall (fun N => Eventually.of_forall (fun s hs => ?_))
    rw [Set.uIoc_of_le ht] at hs
    have h0 := hprob s (le_of_lt hs.1)
    rw [Real.norm_eq_abs, abs_of_nonneg (h0.1 N)]
    rw [← h0.2.tsum_eq]
    exact h0.2.summable.le_tsum N (fun k _ => h0.1 k)
  · exact intervalIntegrable_const
  · refine Eventually.of_forall (fun s hs => ?_)
    rw [Set.uIoc_of_le ht] at hs
    exact (hprob s (le_of_lt hs.1)).2.summable.tendsto_atTop_zero

/-- The key uniqueness consequence: for a bounded dual family, the pairing is conserved. -/
lemma qmi_conserved {lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu) {q : ℕ → ℝ → ℝ}
    (hsol : IsForwardSolution (mmInfRHS lam mu) q) (hprob : IsProbabilityFamily q)
    (hinit : ∀ n : ℕ, q n 0 = if n = 0 then 1 else 0) {t : ℝ} (ht : 0 ≤ t)
    (u : ℕ → ℝ → ℝ)
    (hu : ∀ n s, HasDerivAt (u n) (-(lam * (u (n + 1) s - u n s) + (n : ℝ) * mu * (u (n - 1) s - u n s))) s)
    (hub : ∀ n, ∀ s ∈ Set.Icc 0 t, |u n s| ≤ 1) :
    HasSum (fun n => q n t * u n t) (u 0 0) := by
  have hinit0 : ∀ (v : ℕ → ℝ → ℝ) N, ∑ n ∈ Finset.range (N + 1), q n 0 * v n 0 = v 0 0 := by
    intro v N
    rw [Finset.sum_eq_single 0]
    · simp [hinit]
    · intro b _ hb; simp [hinit, hb]
    · intro h; simp at h
  have hsum : Summable (fun n => q n t * u n t) := by
    refine Summable.of_norm_bounded (hprob t ht).2.summable (fun n => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ((hprob t ht).1 n)]
    exact mul_le_of_le_one_right ((hprob t ht).1 n) (hub n t ⟨ht, le_rfl⟩)
  -- the "flux" integral bound, using the constant dual 1
  have hone : ∀ N : ℕ, ∫ s in (0:ℝ)..t, ((N : ℝ) + 1) * mu * q (N + 1) s
      ≤ lam * ∫ s in (0:ℝ)..t, q N s := by
    intro N
    have h := qmi_dual hsol (fun _ _ => 1) (fun n s => by simpa using hasDerivAt_const s (1:ℝ)) N ht
    rw [hinit0 (fun _ _ => 1) N] at h
    simp only [mul_one] at h
    have hle : ∑ n ∈ Finset.range (N + 1), q n t ≤ 1 :=
      sum_le_hasSum _ (fun k _ => (hprob t ht).1 k) (hprob t ht).2
    have hsub : Set.Icc 0 t ⊆ Set.Ici (0:ℝ) := fun s hs => hs.1
    have hi1 : IntervalIntegrable (fun s => -lam * q N s) volume 0 t := by
      apply ContinuousOn.intervalIntegrable; rw [Set.uIcc_of_le ht]
      exact ((qmi_cont hsol N).mono hsub).const_smul (-lam) |>.congr (fun s _ => by simp [smul_eq_mul])
    have hi2 : IntervalIntegrable (fun s => ((N : ℝ) + 1) * mu * q (N + 1) s) volume 0 t := by
      apply ContinuousOn.intervalIntegrable; rw [Set.uIcc_of_le ht]
      exact ((qmi_cont hsol (N+1)).mono hsub).const_smul (((N : ℝ) + 1) * mu) |>.congr
        (fun s _ => by simp [smul_eq_mul])
    rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul] at h
    linarith
  have hlimN := qmi_int_tendsto lam mu hsol hprob ht
  -- error term
  have herr : Tendsto (fun N => ∑ n ∈ Finset.range (N + 1), q n t * u n t - u 0 0) atTop (𝓝 0) := by
    have hbd : ∀ N, |∑ n ∈ Finset.range (N + 1), q n t * u n t - u 0 0|
        ≤ 2 * lam * ∫ s in (0:ℝ)..t, q N s := by
      intro N
      have h := qmi_dual hsol u hu N ht
      rw [hinit0 u N] at h
      rw [h, ← Real.norm_eq_abs]
      have hsub : Set.Icc 0 t ⊆ Set.Ici (0:ℝ) := fun s hs => hs.1
      have hiq : IntervalIntegrable (fun s => q N s) volume 0 t := by
        apply ContinuousOn.intervalIntegrable; rw [Set.uIcc_of_le ht]
        exact (qmi_cont hsol N).mono hsub
      have hiq1 : IntervalIntegrable (fun s => ((N : ℝ) + 1) * mu * q (N + 1) s) volume 0 t := by
        apply ContinuousOn.intervalIntegrable; rw [Set.uIcc_of_le ht]
        exact ((qmi_cont hsol (N+1)).mono hsub).const_smul (((N : ℝ) + 1) * mu) |>.congr
          (fun s _ => by simp [smul_eq_mul])
      refine le_trans (intervalIntegral.norm_integral_le_of_norm_le ht
        (g := fun s => lam * q N s + ((N : ℝ) + 1) * mu * q (N + 1) s) ?_ ?_) ?_
      · refine Eventually.of_forall (fun s hs => ?_)
        have hs0 : (0:ℝ) ≤ s := le_of_lt hs.1
        have hsI : s ∈ Set.Icc 0 t := ⟨hs0, hs.2⟩
        have hq0 := (hprob s hs0).1 N
        have hq1 := (hprob s hs0).1 (N + 1)
        have hu1 := abs_le.1 (hub (N + 1) s hsI)
        have hu0 := abs_le.1 (hub N s hsI)
        have hc : 0 ≤ ((N : ℝ) + 1) * mu := by positivity
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> nlinarith [mul_nonneg hc hq1, mul_nonneg hlam.le hq0]
      · exact (hiq.const_mul lam).add hiq1
      · rw [intervalIntegral.integral_add (hiq.const_mul lam) hiq1, intervalIntegral.integral_const_mul]
        linarith [hone N]
    rw [Metric.tendsto_atTop]
    intro ε hε
    have := (hlimN.const_mul (2 * lam))
    rw [mul_zero, Metric.tendsto_atTop] at this
    obtain ⟨N0, hN0⟩ := this ε hε
    refine ⟨N0, fun N hN => ?_⟩
    have h1 := hN0 N hN
    rw [Real.dist_eq, sub_zero] at h1 ⊢
    exact lt_of_le_of_lt (hbd N) (lt_of_le_of_lt (le_abs_self _) h1)
  have hlim2 : Tendsto (fun N => ∑ n ∈ Finset.range (N + 1), q n t * u n t) atTop (𝓝 (u 0 0)) := by
    have := herr.add_const (u 0 0)
    simpa using this
  have hlim3 := (hsum.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have := tendsto_nhds_unique hlim3 hlim2
  rw [← this]; exact hsum.hasSum

lemma qmi_expsum (x : ℝ) : HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp x

noncomputable def qmiW (mu t z s : ℝ) : ℝ := 1 + (z - 1) * Real.exp (-mu * (t - s))
noncomputable def qmiE (lam mu t z s : ℝ) : ℝ :=
  Real.exp (lam * (z - 1) * (1 - Real.exp (-mu * (t - s))) / mu)
noncomputable def qmiU (lam mu t z : ℝ) (n : ℕ) (s : ℝ) : ℝ := qmiW mu t z s ^ n * qmiE lam mu t z s

lemma qmi_U_deriv (lam mu t z : ℝ) (hmu : mu ≠ 0) (n : ℕ) (s : ℝ) :
    HasDerivAt (qmiU lam mu t z n)
      (-(lam * (qmiU lam mu t z (n + 1) s - qmiU lam mu t z n s)
        + (n : ℝ) * mu * (qmiU lam mu t z (n - 1) s - qmiU lam mu t z n s))) s := by
  have hE : HasDerivAt (fun s => Real.exp (-mu * (t - s))) (Real.exp (-mu * (t - s)) * mu) s := by
    have h1 : HasDerivAt (fun s => -mu * (t - s)) mu s := by
      have := ((hasDerivAt_id s).const_sub t).const_mul (-mu)
      simpa using this
    exact h1.exp
  have hw : HasDerivAt (qmiW mu t z) ((z - 1) * (Real.exp (-mu * (t - s)) * mu)) s := by
    unfold qmiW; exact (hE.const_mul (z - 1)).const_add 1
  have he : HasDerivAt (qmiE lam mu t z)
      (qmiE lam mu t z s * (lam * (z - 1) * (-(Real.exp (-mu * (t - s)) * mu)) / mu)) s := by
    unfold qmiE
    have := ((hE.const_sub 1).const_mul (lam * (z - 1))).div_const mu
    have h2 := this.exp
    convert h2 using 1
  have hu := (hw.fun_pow n).fun_mul he
  have hfun : qmiU lam mu t z n = fun s => qmiW mu t z s ^ n * qmiE lam mu t z s := rfl
  rw [hfun]
  refine hu.congr_deriv ?_
  simp only [qmiU]
  cases n with
  | zero => simp [qmiW]; field_simp; ring
  | succ k =>
    simp only [Nat.add_sub_cancel, qmiW, Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp
    ring

lemma qmi_U_bound (lam mu t z : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hz1 : -1 ≤ z) (hz2 : z ≤ 1)
    (n : ℕ) (s : ℝ) (hs : s ∈ Set.Icc 0 t) : |qmiU lam mu t z n s| ≤ 1 := by
  have hE1 : Real.exp (-mu * (t - s)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [hs.2]
  have hE0 : 0 < Real.exp (-mu * (t - s)) := Real.exp_pos _
  have hw : |qmiW mu t z s| ≤ 1 := by
    unfold qmiW; rw [abs_le]; constructor <;> nlinarith
  have he : |qmiE lam mu t z s| ≤ 1 := by
    unfold qmiE
    rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    apply div_nonpos_of_nonpos_of_nonneg _ hmu.le
    have : lam * (z - 1) ≤ 0 := by nlinarith
    exact mul_nonpos_of_nonpos_of_nonneg this (by linarith)
  unfold qmiU
  rw [abs_mul, abs_pow]
  calc |qmiW mu t z s| ^ n * |qmiE lam mu t z s| ≤ 1 * 1 := by
        apply mul_le_mul (pow_le_one₀ (abs_nonneg _) hw) he (abs_nonneg _) zero_le_one
    _ = 1 := by ring

lemma qmi_gen_q {lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu) {q : ℕ → ℝ → ℝ}
    (hsol : IsForwardSolution (mmInfRHS lam mu) q) (hprob : IsProbabilityFamily q)
    (hinit : ∀ n : ℕ, q n 0 = if n = 0 then 1 else 0) {t : ℝ} (ht : 0 ≤ t)
    (z : ℝ) (hz1 : -1 ≤ z) (hz2 : z ≤ 1) :
    HasSum (fun n => q n t * z ^ n)
      (Real.exp (lam * (z - 1) * (1 - Real.exp (-mu * t)) / mu)) := by
  have h := qmi_conserved hlam hmu hsol hprob hinit ht (qmiU lam mu t z)
    (fun n s => qmi_U_deriv lam mu t z hmu.ne' n s)
    (fun n s hs => qmi_U_bound lam mu t z hlam hmu hz1 hz2 n s hs)
  have h1 : ∀ n, qmiU lam mu t z n t = z ^ n := by
    intro n; simp [qmiU, qmiW, qmiE]
  have h2 : qmiU lam mu t z 0 0 = Real.exp (lam * (z - 1) * (1 - Real.exp (-mu * t)) / mu) := by
    simp [qmiU, qmiE]
  simp only [h1, h2] at h
  exact h

lemma qmi_coeff (c : ℕ → ℝ) (hb : ∀ n, |c n| ≤ 2)
    (h : ∀ z : ℝ, 0 < z → z ≤ 1 / 2 → HasSum (fun n => c n * z ^ n) 0) : ∀ n, c n = 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  have key : ∀ z : ℝ, 0 < z → z ≤ 1 / 2 → |c m| ≤ 4 * z := by
    intro z hz0 hz1
    have hz := h z hz0 hz1
    have h1 := (hasSum_nat_add_iff' m).2 hz
    have hfin : ∑ i ∈ Finset.range m, c i * z ^ i = 0 :=
      Finset.sum_eq_zero (fun i hi => by rw [IH i (Finset.mem_range.1 hi), zero_mul])
    rw [hfin, sub_zero] at h1
    have h2 := h1.mul_left (z ^ m)⁻¹
    rw [mul_zero] at h2
    have hzm : z ^ m ≠ 0 := pow_ne_zero _ hz0.ne'
    have h3 : HasSum (fun n => c (n + m) * z ^ n) 0 := by
      refine h2.congr_fun (fun n => ?_)
      rw [pow_add]; field_simp
    have h4 := (hasSum_nat_add_iff' 1).2 h3
    simp only [Finset.sum_range_one, zero_add, pow_zero, mul_one, zero_sub] at h4
    have hgeo : HasSum (fun n : ℕ => 2 * z * z ^ n) (2 * z * (1 - z)⁻¹) :=
      (hasSum_geometric_of_lt_one hz0.le (by linarith)).mul_left (2 * z)
    have hup : -c m ≤ 2 * z * (1 - z)⁻¹ := by
      refine hasSum_le (fun n => ?_) h4 hgeo
      have := hb (n + 1 + m)
      have hp : 0 < z ^ (n + 1) := by positivity
      calc c (n + 1 + m) * z ^ (n + 1) ≤ |c (n + 1 + m)| * z ^ (n + 1) := by
            gcongr; exact le_abs_self _
        _ ≤ 2 * z ^ (n + 1) := by gcongr
        _ = 2 * z * z ^ n := by ring
    have hlow : c m ≤ 2 * z * (1 - z)⁻¹ := by
      have h5 := h4.neg
      rw [neg_neg] at h5
      refine hasSum_le (fun n => ?_) h5 hgeo
      have := hb (n + 1 + m)
      have hp : 0 < z ^ (n + 1) := by positivity
      calc -(c (n + 1 + m) * z ^ (n + 1)) = (-c (n + 1 + m)) * z ^ (n + 1) := by ring
        _ ≤ |c (n + 1 + m)| * z ^ (n + 1) := by gcongr; exact neg_le_abs _
        _ ≤ 2 * z ^ (n + 1) := by gcongr
        _ = 2 * z * z ^ n := by ring
    have hq : 2 * z * (1 - z)⁻¹ ≤ 4 * z := by
      rw [← div_eq_mul_inv, div_le_iff₀ (by linarith)]; nlinarith
    rw [abs_le]; constructor <;> linarith
  by_contra hne
  have hpos : 0 < |c m| := abs_pos.2 hne
  have := key (min (1/2) (|c m| / 8)) (lt_min (by norm_num) (by positivity)) (min_le_left _ _)
  have := min_le_right (1/2 : ℝ) (|c m| / 8)
  nlinarith

lemma qmi_p_deriv (lam mu : ℝ) (hmu : 0 < mu) (n : ℕ) (t : ℝ) :
    HasDerivAt (mmInfTransient lam mu n) (mmInfRHS lam mu (fun m => mmInfTransient lam mu m t) n) t := by
  have ha : HasDerivAt (fun t => (1 - Real.exp (-mu * t)) * (lam / mu))
      (lam * Real.exp (-mu * t)) t := by
    have h1 : HasDerivAt (fun t => -mu * t) (-mu) t := by
      simpa using (hasDerivAt_id t).const_mul (-mu)
    have := ((h1.exp).const_sub 1).mul_const (lam / mu)
    refine this.congr_deriv ?_
    field_simp
  have hp := ((ha.fun_pow n).div_const (n.factorial : ℝ)).fun_mul ha.fun_neg.exp
  have hfun : mmInfTransient lam mu n = fun t =>
      ((1 - Real.exp (-mu * t)) * (lam / mu)) ^ n / (n.factorial : ℝ)
        * Real.exp (-((1 - Real.exp (-mu * t)) * (lam / mu))) := rfl
  rw [hfun]
  refine hp.congr_deriv ?_
  have hm : mu ≠ 0 := hmu.ne'
  cases n with
  | zero =>
    simp only [mmInfRHS, mmInfTransient]
    simp
    field_simp
    ring
  | succ k =>
    simp only [mmInfRHS, mmInfTransient, Nat.add_sub_cancel]
    have hrel : lam * Real.exp (-mu * t) = lam - mu * ((1 - Real.exp (-mu * t)) * (lam / mu)) := by
      field_simp; ring
    rw [hrel]
    generalize (1 - Real.exp (-mu * t)) * (lam / mu) = A
    generalize Real.exp (-A) = X
    rw [Nat.factorial_succ (k + 1), Nat.factorial_succ k]
    push_cast
    have hk : (k.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring

theorem mmInf_transient_core (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) :
    IsForwardSolution (mmInfRHS lam mu) (mmInfTransient lam mu) ∧
      (∀ n : ℕ, mmInfTransient lam mu n 0 = if n = 0 then 1 else 0) ∧
      IsProbabilityFamily (mmInfTransient lam mu) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ z : ℂ, ‖z‖ ≤ 1 →
        HasSum (fun n : ℕ => (mmInfTransient lam mu n t : ℂ) * z ^ n)
          (Complex.exp ((z - 1) * ((1 - Real.exp (-mu * t)) * (lam / mu) : ℝ)))) ∧
      ∀ q : ℕ → ℝ → ℝ, IsForwardSolution (mmInfRHS lam mu) q → IsProbabilityFamily q →
        (∀ n : ℕ, q n 0 = if n = 0 then 1 else 0) →
        ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → q n t = mmInfTransient lam mu n t := by
  have hsol : IsForwardSolution (mmInfRHS lam mu) (mmInfTransient lam mu) :=
    fun n t _ => (qmi_p_deriv lam mu hmu n t).hasDerivWithinAt
  -- real generating function of p
  have hgen : ∀ t z : ℝ, HasSum (fun n => mmInfTransient lam mu n t * z ^ n)
      (Real.exp ((1 - Real.exp (-mu * t)) * (lam / mu) * z) *
        Real.exp (-((1 - Real.exp (-mu * t)) * (lam / mu)))) := by
    intro t z
    have := (qmi_expsum ((1 - Real.exp (-mu * t)) * (lam / mu) * z)).mul_right
      (Real.exp (-((1 - Real.exp (-mu * t)) * (lam / mu))))
    refine this.congr_fun (fun n => ?_)
    simp only [mmInfTransient, mul_pow]
    ring
  have hprob : IsProbabilityFamily (mmInfTransient lam mu) := by
    intro t ht
    have ha : 0 ≤ (1 - Real.exp (-mu * t)) * (lam / mu) := by
      apply mul_nonneg _ (by positivity)
      rw [sub_nonneg, Real.exp_le_one_iff]; nlinarith
    refine ⟨fun n => ?_, ?_⟩
    · unfold mmInfTransient; positivity
    · have := hgen t 1
      simp only [one_pow, mul_one] at this
      rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at this
  refine ⟨hsol, ?_, hprob, ?_, ?_⟩
  · intro n
    cases n <;> simp [mmInfTransient]
  · intro t _ z _
    have hc := NormedSpace.expSeries_div_hasSum_exp ((((1 - Real.exp (-mu * t)) * (lam / mu) : ℝ) : ℂ) * z)
    rw [← Complex.exp_eq_exp_ℂ] at hc
    have := hc.mul_right (Complex.exp (-(((1 - Real.exp (-mu * t)) * (lam / mu) : ℝ) : ℂ)))
    rw [← Complex.exp_add] at this
    have e : (z - 1) * (((1 - Real.exp (-mu * t)) * (lam / mu) : ℝ) : ℂ)
        = (((1 - Real.exp (-mu * t)) * (lam / mu) : ℝ) : ℂ) * z
          + -(((1 - Real.exp (-mu * t)) * (lam / mu) : ℝ) : ℂ) := by ring
    rw [e]
    refine this.congr_fun (fun n => ?_)
    simp only [mmInfTransient]
    generalize (1 - Real.exp (-mu * t)) * (lam / mu) = A
    push_cast [Complex.ofReal_exp]
    rw [mul_pow]
    ring
  · intro q hq hqp hqi n t ht
    have hc := qmi_coeff (fun n => q n t - mmInfTransient lam mu n t) ?_ ?_ n
    · simpa [sub_eq_zero] using hc
    · intro m
      have h1 := (hqp t ht).1 m
      have h2 := (hprob t ht).1 m
      have h3 : q m t ≤ 1 := by
        rw [← (hqp t ht).2.tsum_eq]
        exact (hqp t ht).2.summable.le_tsum m (fun k _ => (hqp t ht).1 k)
      have h4 : mmInfTransient lam mu m t ≤ 1 := by
        rw [← (hprob t ht).2.tsum_eq]
        exact (hprob t ht).2.summable.le_tsum m (fun k _ => (hprob t ht).1 k)
      rw [abs_le]; constructor <;> linarith
    · intro z hz0 hz1
      have hq' := qmi_gen_q hlam hmu hq hqp hqi ht z (by linarith) (by linarith)
      have hp' := hgen t z
      have heq : Real.exp (lam * (z - 1) * (1 - Real.exp (-mu * t)) / mu)
          = Real.exp ((1 - Real.exp (-mu * t)) * (lam / mu) * z) *
            Real.exp (-((1 - Real.exp (-mu * t)) * (lam / mu))) := by
        rw [← Real.exp_add]; congr 1; field_simp; ring
      rw [heq] at hq'
      have := hq'.sub hp'
      rw [sub_self] at this
      refine this.congr_fun (fun m => ?_)
      ring

end QueueingFundamentals.Transient

open QueueingFundamentals.Transient


theorem solution (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) :
    IsForwardSolution (mmInfRHS lam mu) (mmInfTransient lam mu) ∧
      (∀ n : ℕ, mmInfTransient lam mu n 0 = if n = 0 then 1 else 0) ∧
      IsProbabilityFamily (mmInfTransient lam mu) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ z : ℂ, ‖z‖ ≤ 1 →
        HasSum (fun n : ℕ => (mmInfTransient lam mu n t : ℂ) * z ^ n)
          (Complex.exp ((z - 1) * ((1 - Real.exp (-mu * t)) * (lam / mu) : ℝ)))) ∧
      ∀ q : ℕ → ℝ → ℝ, IsForwardSolution (mmInfRHS lam mu) q → IsProbabilityFamily q →
        (∀ n : ℕ, q n 0 = if n = 0 then 1 else 0) →
        ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → q n t = mmInfTransient lam mu n t := by
  exact mmInf_transient_core lam mu hlam hmu
