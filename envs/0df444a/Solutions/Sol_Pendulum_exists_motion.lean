-- Prove2me | solution 1 for Pendulum.exists_motion
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:49:33.77869+00:00
-- url     : https://prove2.me/submissions/92ccb3e6-4754-48cc-b71c-d08d1dd2acdb

import Mathlib
import Definitions.Def_PendulumDefs

open Pendulum

/-- The coefficient `(2n)! / (2^{2n} (n!)^2)`. -/
noncomputable def W7b_Pendulum_c (n : ℕ) : ℝ :=
  ((2 * n).factorial : ℝ) / (2 ^ (2 * n) * (n.factorial : ℝ) ^ 2)

theorem W7b_Pendulum_c_zero : W7b_Pendulum_c 0 = 1 := by simp [W7b_Pendulum_c]

theorem W7b_Pendulum_c_succ (n : ℕ) :
    W7b_Pendulum_c (n + 1) = W7b_Pendulum_c n * ((2 * n + 1) / (2 * n + 2)) := by
  unfold W7b_Pendulum_c
  have h1 : 2 * (n + 1) = (2 * n + 1) + 1 := by ring
  rw [h1, Nat.factorial_succ, Nat.factorial_succ (2 * n), Nat.factorial_succ n]
  push_cast
  have : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have : (0 : ℝ) < ((2 * n).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  field_simp
  ring

theorem W7b_Pendulum_c_nonneg (n : ℕ) : 0 ≤ W7b_Pendulum_c n := by
  unfold W7b_Pendulum_c; positivity

theorem W7b_Pendulum_c_le_one (n : ℕ) : W7b_Pendulum_c n ≤ 1 := by
  induction n with
  | zero => rw [W7b_Pendulum_c_zero]
  | succ n ih =>
    rw [W7b_Pendulum_c_succ]
    have h0 := W7b_Pendulum_c_nonneg n
    have : (2 * (n : ℝ) + 1) / (2 * n + 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have : 0 ≤ (2 * (n : ℝ) + 1) / (2 * n + 2) := by positivity
    nlinarith

/-- The binomial coefficient `binom(n - 1/2, n)` equals `c n`. -/
theorem W7b_Pendulum_choose (n : ℕ) :
    Ring.choose ((1 / 2 : ℝ) + n - 1) n = W7b_Pendulum_c n := by
  have key : ∀ n : ℕ, (ascPochhammer ℝ n).eval (1 / 2 : ℝ) =
      (n.factorial : ℝ) * W7b_Pendulum_c n := by
    intro n
    induction n with
    | zero => simp [W7b_Pendulum_c_zero]
    | succ n ih =>
      rw [ascPochhammer_succ_eval, ih, W7b_Pendulum_c_succ, Nat.factorial_succ]
      push_cast
      field_simp
      ring
  rw [Ring.choose_eq_smul, Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_eq_eval]
  have : (1 / 2 : ℝ) + n - 1 - n + 1 = 1 / 2 := by ring
  rw [this, key, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero n),
    one_mul]

/-- `1/√(1-y) = ∑ c n y^n` for `0 ≤ y < 1`. -/
theorem W7b_Pendulum_series (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    HasSum (fun n => W7b_Pendulum_c n * y ^ n) (Real.sqrt (1 - y))⁻¹ := by
  have hb := Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero (1 / 2 : ℝ)
  have hmem : y ∈ EMetric.ball (0 : ℝ) 1 := by
    show y ∈ Metric.eball (0 : ℝ) 1
    rw [Metric.mem_eball', edist_dist, Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hy0]
    exact ENNReal.ofReal_lt_one.mpr hy1
  have hs := hb.hasSum hmem
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, W7b_Pendulum_choose, zero_add,
    smul_eq_mul] at hs
  have hval : (1 : ℝ) / (1 - y) ^ (1 / 2 : ℝ) = (Real.sqrt (1 - y))⁻¹ := by
    rw [Real.sqrt_eq_rpow, one_div]
  rw [hval] at hs
  exact hs

/-- Wallis: `∫₀^{π/2} sin^{2n} = (π/2) c n`. -/
theorem W7b_Pendulum_wallis (n : ℕ) :
    ∫ u in (0 : ℝ)..(Real.pi / 2), Real.sin u ^ (2 * n) = Real.pi / 2 * W7b_Pendulum_c n := by
  induction n with
  | zero => simp [W7b_Pendulum_c_zero]
  | succ n ih =>
    have h : 2 * (n + 1) = 2 * n + 2 := by ring
    rw [h, integral_sin_pow, ih, W7b_Pendulum_c_succ]
    simp only [Real.sin_zero, Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_zero]
    push_cast
    ring_nf

theorem W7b_Pendulum_ellipticK (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1) :
    ellipticK k = Real.pi / 2 * ∑' n : ℕ, W7b_Pendulum_c n ^ 2 * k ^ (2 * n) := by
  unfold ellipticK
  let F : ℕ → C(ℝ, ℝ) := fun n =>
    ⟨fun u => W7b_Pendulum_c n * k ^ (2 * n) * Real.sin u ^ (2 * n), by fun_prop⟩
  have hk2 : k ^ 2 < 1 := by nlinarith
  have hsum : Summable fun n : ℕ =>
      ‖(F n).restrict (⟨Set.uIcc 0 (Real.pi / 2), isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (summable_geometric_of_lt_one (by positivity) hk2)
    refine (ContinuousMap.norm_le _ (by positivity)).mpr (fun u => ?_)
    simp only [ContinuousMap.restrict_apply, ContinuousMap.coe_mk, F, Real.norm_eq_abs]
    rw [abs_mul, abs_mul, abs_of_nonneg (W7b_Pendulum_c_nonneg n), abs_of_nonneg (by positivity),
      abs_pow]
    have hs : |Real.sin u| ^ (2 * n) ≤ 1 := pow_le_one₀ (abs_nonneg _) (Real.abs_sin_le_one _)
    have hc := W7b_Pendulum_c_le_one n
    have hc0 := W7b_Pendulum_c_nonneg n
    have hkp : 0 ≤ k ^ (2 * n) := by positivity
    rw [pow_mul]
    calc W7b_Pendulum_c n * (k ^ 2) ^ n * |Real.sin u| ^ (2 * n) ≤ 1 * (k ^ 2) ^ n * 1 := by
          gcongr
      _ = (k ^ 2) ^ n := by ring
  have hH := intervalIntegral.hasSum_intervalIntegral_of_summable_norm hsum
  have hpt : ∀ u, ∑' n, F n u = (Real.sqrt (1 - k ^ 2 * Real.sin u ^ 2))⁻¹ := by
    intro u
    have hy0 : 0 ≤ k ^ 2 * Real.sin u ^ 2 := by positivity
    have hy1 : k ^ 2 * Real.sin u ^ 2 < 1 := by
      have : Real.sin u ^ 2 ≤ 1 := Real.sin_sq_le_one u
      nlinarith
    have := (W7b_Pendulum_series _ hy0 hy1).tsum_eq
    rw [← this]
    congr 1; funext n
    simp only [ContinuousMap.coe_mk, F]
    rw [mul_pow, ← pow_mul, ← pow_mul]; ring
  simp_rw [hpt] at hH
  rw [← hH.tsum_eq, ← tsum_mul_left]
  congr 1; funext n
  simp only [ContinuousMap.coe_mk, F]
  rw [intervalIntegral.integral_const_mul, W7b_Pendulum_wallis]
  ring

theorem W7b_Pendulum_exactPeriod_series (g l theta0 : ℝ) (hg : 0 < g) (hl : 0 < l)
    (hpos : 0 ≤ theta0) (hlt : theta0 < Real.pi) :
    exactPeriod g l theta0
      = 2 * Real.pi * Real.sqrt (l / g) *
        ∑' n : ℕ, (((2 * n).factorial : ℝ) / (2 ^ (2 * n) * (n.factorial : ℝ) ^ 2)) ^ 2
          * Real.sin (theta0 / 2) ^ (2 * n) := by
  have hk0 : 0 ≤ Real.sin (theta0 / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hk1 : Real.sin (theta0 / 2) < 1 := by
    rw [← Real.sin_pi_div_two]
    apply Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  unfold exactPeriod
  rw [W7b_Pendulum_ellipticK _ hk0 hk1]
  unfold W7b_Pendulum_c
  ring

/-! ## Global existence of pendulum motions -/

/-- Clamping to `[-R, R]`. -/
noncomputable def W7b_Pendulum_cl (R w : ℝ) : ℝ := max (-R) (min R w)

theorem W7b_Pendulum_cl_lip (R u v : ℝ) :
    |W7b_Pendulum_cl R u - W7b_Pendulum_cl R v| ≤ |u - v| := by
  unfold W7b_Pendulum_cl
  refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero]
  refine max_le (abs_nonneg _) ?_
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero]
  exact max_le (abs_nonneg _) le_rfl

theorem W7b_Pendulum_cl_of_abs_le (R w : ℝ) (h : |w| ≤ R) : W7b_Pendulum_cl R w = w := by
  unfold W7b_Pendulum_cl
  rw [abs_le] at h
  rw [min_eq_right h.2, max_eq_right h.1]

theorem W7b_Pendulum_cl_abs (R w : ℝ) (hR : 0 ≤ R) : |W7b_Pendulum_cl R w| ≤ R := by
  unfold W7b_Pendulum_cl
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

theorem W7b_Pendulum_cl_cont (R : ℝ) : Continuous (W7b_Pendulum_cl R) := by
  unfold W7b_Pendulum_cl; fun_prop

theorem solution (g l theta0 omega0 : ℝ) :
    ∃ theta omega alpha : ℝ → ℝ,
      IsMotion g l theta omega alpha ∧ theta 0 = theta0 ∧ omega 0 = omega0 := by
  set kk := g / l with hkk
  set R : ℝ := |omega0| + 2 * |kk| + 1 with hR
  have hR0 : 0 < R := by positivity
  set cl := W7b_Pendulum_cl R with hcl
  -- the modified, bounded vector field on `Fin 2 → ℝ`
  set F : ℝ → (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun _ v => ![cl (v 1), -kk * Real.sin (v 0)] with hF
  set K : NNReal := ⟨max 1 |kk|, by positivity⟩ with hK
  set L : ℝ := max R |kk| with hL
  have hL0 : 0 ≤ L := le_trans hR0.le (le_max_left _ _)
  have hLip : ∀ t, LipschitzWith K (F t) := by
    intro t
    apply LipschitzWith.of_dist_le_mul
    intro v w
    rw [dist_pi_le_iff (by positivity)]
    intro i
    fin_cases i
    · simp only [hF, Fin.zero_eta, Matrix.cons_val_zero, Real.dist_eq]
      refine (W7b_Pendulum_cl_lip R _ _).trans ?_
      have h1 : |v 1 - w 1| ≤ dist v w := by
        rw [← Real.dist_eq]; exact dist_le_pi_dist v w 1
      have h2 : (1 : ℝ) ≤ (K : ℝ) := le_max_left _ _
      nlinarith [dist_nonneg (x := v) (y := w)]
    · simp only [hF, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Real.dist_eq]
      rw [show -kk * Real.sin (v 0) - -kk * Real.sin (w 0) = -kk * (Real.sin (v 0) - Real.sin (w 0))
        by ring, abs_mul, abs_neg]
      have h1 : |Real.sin (v 0) - Real.sin (w 0)| ≤ dist v w := by
        refine (Real.abs_sin_sub_sin_le _ _).trans ?_
        rw [← Real.dist_eq]; exact dist_le_pi_dist v w 0
      have h2 : |kk| ≤ (K : ℝ) := le_max_right _ _
      calc |kk| * |Real.sin (v 0) - Real.sin (w 0)| ≤ |kk| * dist v w :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ ≤ K * dist v w := mul_le_mul_of_nonneg_right h2 dist_nonneg
  have hbound : ∀ t v, ‖F t v‖ ≤ L := by
    intro t v
    rw [pi_norm_le_iff_of_nonneg hL0]
    intro i
    fin_cases i
    · simp only [hF, Fin.zero_eta, Matrix.cons_val_zero, Real.norm_eq_abs]
      exact (W7b_Pendulum_cl_abs R _ hR0.le).trans (le_max_left _ _)
    · simp only [hF, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Real.norm_eq_abs]
      rw [abs_mul, abs_neg]
      calc |kk| * |Real.sin (v 0)| ≤ |kk| * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
        _ = |kk| := mul_one _
        _ ≤ L := le_max_right _ _
  set x0 : Fin 2 → ℝ := ![theta0, omega0] with hx0
  -- solutions on `[-(n+1), n+1]`
  have hsol : ∀ n : ℕ, ∃ α : ℝ → (Fin 2 → ℝ), α 0 = x0 ∧
      ∀ t ∈ Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1),
        HasDerivWithinAt α (F t (α t)) (Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) t := by
    intro n
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    let t0 : Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) := ⟨0, by constructor <;> linarith⟩
    have hPL : IsPicardLindelof F t0 x0 (Real.toNNReal (L * ((n : ℝ) + 1))) 0
        (Real.toNNReal L) K :=
      { lipschitzOnWith := fun t _ => (hLip t).lipschitzOnWith
        continuousOn := fun _ _ => continuousOn_const
        norm_le := fun t _ v _ => by rw [Real.coe_toNNReal _ hL0]; exact hbound t v
        mul_max_le := by
          simp only [t0, Real.coe_toNNReal _ hL0, Real.coe_toNNReal _ (by positivity : 0 ≤ L * ((n:ℝ) + 1)),
            NNReal.coe_zero, sub_zero]
          apply mul_le_mul_of_nonneg_left _ hL0
          apply max_le <;> linarith }
    obtain ⟨α, hα0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    exact ⟨α, hα0, hα⟩
  choose sol hsol0 hsold using hsol
  have hsolAt : ∀ n : ℕ, ∀ t, |t| < (n : ℝ) + 1 → HasDerivAt (sol n) (F t (sol n t)) t := by
    intro n t ht
    rw [abs_lt] at ht
    exact (hsold n t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  -- uniqueness: the solutions agree on common intervals
  have huniq : ∀ n m : ℕ, n ≤ m → ∀ t ∈ Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1), sol n t = sol m t := by
    intro n m hnm
    have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    apply ODE_solution_unique_of_mem_Icc (v := F) (s := fun _ => Set.univ) (K := K)
      (fun t _ => (hLip t).lipschitzOnWith) (⟨by linarith, by linarith⟩ : (0 : ℝ) ∈ Set.Ioo _ _)
    · intro t ht; exact (hsold n t ht).continuousWithinAt
    · intro t ht; exact hsolAt n t (by rw [abs_lt]; exact ⟨ht.1, ht.2⟩)
    · intro t _; trivial
    · intro t ht
      exact (hsold m t ⟨by linarith [ht.1], by linarith [ht.2]⟩).continuousWithinAt.mono
        (Set.Icc_subset_Icc (by linarith) (by linarith))
    · intro t ht; exact hsolAt m t (by rw [abs_lt]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    · intro t _; trivial
    · rw [hsol0, hsol0]
  -- the global solution
  set γ : ℝ → (Fin 2 → ℝ) := fun t => sol ⌈|t|⌉₊ t with hγ
  have hγd : ∀ t, HasDerivAt γ (F t (γ t)) t := by
    intro t
    set n := ⌈|t|⌉₊ with hn
    have htn : |t| ≤ n := Nat.le_ceil _
    have hev : γ =ᶠ[nhds t] sol (n + 1) := by
      have hU : Set.Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1) ∈ nhds t := by
        apply Ioo_mem_nhds <;> [skip; skip] <;> (rw [abs_le] at htn; linarith [htn.1, htn.2])
      filter_upwards [hU] with s hs
      have hs' : |s| ≤ (n : ℝ) + 1 := by rw [abs_le]; exact ⟨hs.1.le, hs.2.le⟩
      have hcs : ⌈|s|⌉₊ ≤ n + 1 := by
        rw [Nat.ceil_le]; push_cast; exact hs'
      simp only [hγ]
      apply huniq _ _ hcs
      have := Nat.le_ceil |s|
      rw [abs_le] at this
      exact ⟨by linarith [this.1], by linarith [this.2]⟩
    have hd := hsolAt (n + 1) t (by push_cast; linarith)
    have heq : γ t = sol (n + 1) t := hev.eq_of_nhds
    rw [heq]
    exact hd.congr_of_eventuallyEq hev
  have hγ0 : γ 0 = x0 := by simp [hγ, hsol0]
  set theta : ℝ → ℝ := fun t => γ t 0 with htheta
  set omega : ℝ → ℝ := fun t => γ t 1 with homega
  have hθd : ∀ t, HasDerivAt theta (cl (omega t)) t := by
    intro t
    have := (hasDerivAt_pi.mp (hγd t)) 0
    simpa [hF] using this
  have hωd : ∀ t, HasDerivAt omega (-kk * Real.sin (theta t)) t := by
    intro t
    have := (hasDerivAt_pi.mp (hγd t)) 1
    simpa [hF] using this
  -- the conserved quantity
  set Γ : ℝ → ℝ := fun w => ∫ s in (0 : ℝ)..w, cl s with hΓ
  have hΓd : ∀ w, HasDerivAt Γ (cl w) w := fun w =>
    intervalIntegral.integral_hasDerivAt_right
      ((W7b_Pendulum_cl_cont R).intervalIntegrable _ _)
      ((W7b_Pendulum_cl_cont R).stronglyMeasurableAtFilter _ _) (W7b_Pendulum_cl_cont R).continuousAt
  have hΓsq : ∀ w, |w| ≤ R → Γ w = w ^ 2 / 2 := by
    intro w hw
    simp only [hΓ]
    rw [intervalIntegral.integral_congr (g := fun s => s) (fun s hs => by
      apply W7b_Pendulum_cl_of_abs_le
      rw [Set.mem_uIcc] at hs
      rw [abs_le] at hw ⊢
      rcases hs with h | h <;> constructor <;> linarith [h.1, h.2])]
    rw [integral_id]; ring
  have hΓmono : MonotoneOn Γ (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun w _ => (hΓd w).continuousAt.continuousWithinAt
    · exact fun w _ => (hΓd w).differentiableAt.differentiableWithinAt
    · intro w hw
      rw [interior_Ici] at hw
      rw [(hΓd w).deriv]
      unfold cl W7b_Pendulum_cl
      exact le_max_of_le_right (le_min hR0.le (le_of_lt hw))
  have hΓanti : AntitoneOn Γ (Set.Iic 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Iic 0)
    · exact fun w _ => (hΓd w).continuousAt.continuousWithinAt
    · exact fun w _ => (hΓd w).differentiableAt.differentiableWithinAt
    · intro w hw
      rw [interior_Iic] at hw
      rw [(hΓd w).deriv]
      unfold cl W7b_Pendulum_cl
      exact max_le (by linarith) (min_le_of_right_le (le_of_lt hw))
  have hΓbig : ∀ w, R ≤ |w| → R ^ 2 / 2 ≤ Γ w := by
    intro w hw
    rcases le_total 0 w with h0 | h0
    · rw [abs_of_nonneg h0] at hw
      have := hΓmono (Set.mem_Ici.mpr hR0.le) (Set.mem_Ici.mpr h0) hw
      rwa [hΓsq R (by rw [abs_of_pos hR0])] at this
    · rw [abs_of_nonpos h0] at hw
      have := hΓanti (Set.mem_Iic.mpr h0) (Set.mem_Iic.mpr (by linarith)) (by linarith : w ≤ -R)
      rw [hΓsq (-R) (by rw [abs_neg, abs_of_pos hR0]), neg_sq] at this
      exact this
  -- conservation
  set H : ℝ → ℝ := fun t => Γ (omega t) - kk * Real.cos (theta t) with hH
  have hHd : ∀ t, HasDerivAt H 0 t := by
    intro t
    have h1 := (hΓd (omega t)).comp t (hωd t)
    have h2 := ((hθd t).cos).const_mul kk
    exact (h1.sub h2).congr_deriv (by ring)
  have hHc : ∀ t, H t = H 0 := fun t =>
    is_const_of_deriv_eq_zero (fun s => (hHd s).differentiableAt) (fun s => (hHd s).deriv) t 0
  have hθ0 : theta 0 = theta0 := by simp [htheta, hγ0, hx0]
  have hω0 : omega 0 = omega0 := by simp [homega, hγ0, hx0]
  have hsmall : ∀ t, |omega t| < R := by
    intro t
    by_contra hcon
    push_neg at hcon
    have h1 := hΓbig _ hcon
    have h2 := hHc t
    simp only [hH, hθ0, hω0] at h2
    rw [hΓsq omega0 (by rw [hR]; have := abs_nonneg kk; linarith)] at h2
    have hc1 : |kk * Real.cos (theta t)| ≤ |kk| := by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
    have hc2 : |kk * Real.cos theta0| ≤ |kk| := by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
    rw [abs_le] at hc1 hc2
    have hRsq : omega0 ^ 2 / 2 + 2 * |kk| < R ^ 2 / 2 := by
      rw [hR]
      have := abs_nonneg kk
      have := abs_nonneg omega0
      nlinarith [sq_abs omega0]
    linarith [hc1.1, hc1.2, hc2.1, hc2.2]
  refine ⟨theta, omega, fun t => -(g / l) * Real.sin (theta t), ⟨?_, ?_, ?_⟩, hθ0, hω0⟩
  · intro t
    have := hθd t
    rwa [hcl, W7b_Pendulum_cl_of_abs_le R _ (hsmall t).le] at this
  · intro t; exact hωd t
  · intro t; rfl

/-! ## The quarter period as a complete elliptic integral -/

theorem W7b_Pendulum_quarterPeriod_eq_ellipticK (theta0 : ℝ) (hpos : 0 < theta0) (hlt : theta0 < Real.pi) :
    (∫ x in (0 : ℝ)..theta0, (Real.sqrt (Real.cos x - Real.cos theta0))⁻¹)
      = Real.sqrt 2 * ellipticK (Real.sin (theta0 / 2)) := by
  set k := Real.sin (theta0 / 2) with hk
  have hk0 : 0 < k := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hk1 : k < 1 := by
    rw [hk, ← Real.sin_pi_div_two]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  have harck : Real.arcsin k = theta0 / 2 := Real.arcsin_sin (by linarith) (by linarith)
  set s := Set.Ioo (0 : ℝ) (Real.pi / 2) with hs
  set T : ℝ → ℝ := fun φ => 2 * Real.arcsin (k * Real.sin φ) with hT
  set T' : ℝ → ℝ := fun φ => 2 * (1 / Real.sqrt (1 - (k * Real.sin φ) ^ 2) * (k * Real.cos φ))
    with hT'
  have hu : ∀ φ ∈ s, 0 < k * Real.sin φ ∧ k * Real.sin φ < k := by
    intro φ hφ
    have h1 : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ.1 (by linarith [hφ.2, Real.pi_pos])
    have h2 : Real.sin φ < 1 := by
      rw [← Real.sin_pi_div_two]
      exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [hφ.1]) le_rfl hφ.2
    exact ⟨by positivity, by nlinarith⟩
  have hTd : ∀ φ ∈ s, HasDerivWithinAt T (T' φ) s φ := by
    intro φ hφ
    obtain ⟨u0, u1⟩ := hu φ hφ
    have := ((Real.hasDerivAt_arcsin (x := k * Real.sin φ) (by linarith) (by linarith)).comp φ
      ((Real.hasDerivAt_sin φ).const_mul k)).const_mul 2
    exact this.hasDerivWithinAt
  have hTinj : Set.InjOn T s := by
    intro φ1 h1 φ2 h2 heq
    simp only [hT] at heq
    have ha := hu φ1 h1
    have hb := hu φ2 h2
    have e1 : Real.arcsin (k * Real.sin φ1) = Real.arcsin (k * Real.sin φ2) := by linarith
    have e2 : k * Real.sin φ1 = k * Real.sin φ2 :=
      Real.injOn_arcsin ⟨by linarith [ha.1], by linarith [ha.2]⟩
        ⟨by linarith [hb.1], by linarith [hb.2]⟩ e1
    have e3 : Real.sin φ1 = Real.sin φ2 := mul_left_cancel₀ hk0.ne' e2
    exact Real.injOn_sin ⟨by linarith [h1.1, Real.pi_pos], h1.2.le⟩
      ⟨by linarith [h2.1, Real.pi_pos], h2.2.le⟩ e3
  have himage : T '' s = Set.Ioo 0 theta0 := by
    ext x
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      obtain ⟨u0, u1⟩ := hu φ hφ
      simp only [hT, Set.mem_Ioo]
      constructor
      · have := Real.arcsin_pos.mpr u0; linarith
      · have := Real.arcsin_lt_arcsin (by linarith) u1 hk1.le
        linarith
    · rintro ⟨hx0, hx1⟩
      have hsx : 0 < Real.sin (x / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      have hsxk : Real.sin (x / 2) < k := by
        rw [hk]; exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
      set v := Real.sin (x / 2) / k with hv
      have hv0 : 0 < v := by positivity
      have hv1 : v < 1 := by rw [hv, div_lt_one hk0]; exact hsxk
      refine ⟨Real.arcsin v, ⟨Real.arcsin_pos.mpr hv0, Real.arcsin_lt_pi_div_two.mpr hv1⟩, ?_⟩
      simp only [hT]
      rw [Real.sin_arcsin (by linarith) hv1.le, hv, mul_div_cancel₀ _ hk0.ne',
        Real.arcsin_sin (by linarith) (by linarith)]
      ring
  have hcv := MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hTd hTinj
    (fun x => (Real.sqrt (Real.cos x - Real.cos theta0))⁻¹)
  rw [himage] at hcv
  rw [intervalIntegral.integral_of_le hpos.le, MeasureTheory.integral_Ioc_eq_integral_Ioo, hcv]
  unfold ellipticK
  rw [intervalIntegral.integral_of_le (by positivity), MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← MeasureTheory.integral_const_mul]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
  intro φ hφ
  obtain ⟨u0, u1⟩ := hu φ hφ
  have hcos : 0 < Real.cos φ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hφ.1, Real.pi_pos], hφ.2⟩
  have hsq : 0 < 1 - (k * Real.sin φ) ^ 2 := by nlinarith
  have hsin2 : Real.sin φ ^ 2 = 1 - Real.cos φ ^ 2 := Real.sin_sq φ
  -- `cos (T φ) - cos θ₀ = 2 k² cos² φ`
  have hcT : Real.cos (T φ) = 1 - 2 * (k * Real.sin φ) ^ 2 := by
    simp only [hT]
    rw [Real.cos_two_mul, Real.cos_arcsin, Real.sq_sqrt hsq.le]; ring
  have hc0 : Real.cos theta0 = 1 - 2 * k ^ 2 := by
    have : theta0 = 2 * (theta0 / 2) := by ring
    rw [this, Real.cos_two_mul, hk, Real.cos_sq']; ring
  have hdiff : Real.cos (T φ) - Real.cos theta0 = (Real.sqrt 2 * k * Real.cos φ) ^ 2 := by
    rw [hcT, hc0, show (Real.sqrt 2 * k * Real.cos φ) ^ 2 =
      (Real.sqrt 2) ^ 2 * k ^ 2 * Real.cos φ ^ 2 by ring, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    linear_combination (-2 * k ^ 2) * hsin2
  have hTpos : 0 < T' φ := by simp only [hT']; positivity
  simp only [smul_eq_mul]
  rw [abs_of_pos hTpos, hdiff, Real.sqrt_sq (by positivity)]
  simp only [hT']
  have hs2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [show 1 - k ^ 2 * Real.sin φ ^ 2 = 1 - (k * Real.sin φ) ^ 2 by ring]
  set w := Real.sqrt (1 - (k * Real.sin φ) ^ 2) with hw
  have hw0 : 0 < w := Real.sqrt_pos.mpr hsq
  have hkc : k * Real.cos φ ≠ 0 := by positivity
  trans 2 / (Real.sqrt 2 * w)
  · field_simp
  · rw [div_eq_iff (by positivity)]
    field_simp <;> first
      | linear_combination (-w) * hsq2
      | linear_combination w * hsq2
      | linear_combination hsq2
      | linear_combination (-1 : ℝ) * hsq2
      | nlinarith [hsq2]
