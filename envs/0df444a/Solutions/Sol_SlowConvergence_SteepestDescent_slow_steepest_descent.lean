-- Prove2me | solution 1 for SlowConvergence.SteepestDescent.slow_steepest_descent
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T05:05:32.39422+00:00
-- url     : https://prove2.me/submissions/841367f8-1a19-47b7-b020-4308337e087f

import Mathlib

set_option autoImplicit false

namespace B01358bcAux

open Filter Topology Function

/-! ### Locally finite sums of real functions -/

lemma lf_eventually (F : ℕ → ℝ → ℝ) (hlf : LocallyFinite fun i => support (F i)) (y : ℝ) :
    ∃ s : Finset ℕ, (fun x => ∑ᶠ i, F i x) =ᶠ[𝓝 y] (fun x => ∑ i ∈ s, F i x) ∧
      ∀ i ∉ s, F i =ᶠ[𝓝 y] fun _ => 0 := by
  obtain ⟨s, hs⟩ := hlf.exists_finset_support y
  refine ⟨s, ?_, ?_⟩
  · filter_upwards [hs] with x hx
    exact finsum_eq_sum_of_support_subset _ hx
  · intro i hi
    filter_upwards [hs] with x hx
    by_contra h
    exact hi (hx h)

lemma contDiff_fs (F : ℕ → ℝ → ℝ) {n : WithTop ℕ∞} (hF : ∀ i, ContDiff ℝ n (F i))
    (hlf : LocallyFinite fun i => support (F i)) : ContDiff ℝ n (fun x => ∑ᶠ i, F i x) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  obtain ⟨s, hs, -⟩ := lf_eventually F hlf y
  have : ContDiff ℝ n (fun x => ∑ i ∈ s, F i x) := ContDiff.sum (fun i _ => hF i)
  exact this.contDiffAt.congr_of_eventuallyEq hs

lemma deriv_fs (F : ℕ → ℝ → ℝ) (hF : ∀ i, Differentiable ℝ (F i))
    (hlf : LocallyFinite fun i => support (F i)) :
    deriv (fun x => ∑ᶠ i, F i x) = fun y => ∑ᶠ i, deriv (F i) y := by
  funext y
  obtain ⟨s, hs, hz⟩ := lf_eventually F hlf y
  rw [hs.deriv_eq]
  rw [deriv_fun_sum (fun i _ => (hF i).differentiableAt)]
  symm
  apply finsum_eq_sum_of_support_subset
  intro i hi
  by_contra h
  apply hi
  show deriv (F i) y = 0
  rw [(hz i h).deriv_eq]
  simp

lemma abs_fs_le (G : ℕ → ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ i x, |G i x| ≤ M)
    (hd : ∀ x i j, G i x ≠ 0 → G j x ≠ 0 → i = j) (x : ℝ) : |∑ᶠ i, G i x| ≤ M := by
  by_cases h : ∃ i, G i x ≠ 0
  · obtain ⟨i, hi⟩ := h
    rw [finsum_eq_single (fun j => G j x) i (fun j hj => by
      by_contra hne
      exact hj (hd x j i hne hi))]
    exact hb i x
  · push Not at h
    simp [h, hM]

lemma lf_of (G : ℕ → ℝ → ℝ) (c : ℕ → ℝ) (hc : Tendsto c atTop atTop)
    (h : ∀ i x, G i x ≠ 0 → |x - c i| ≤ 1) : LocallyFinite fun i => support (G i) := by
  intro y
  refine ⟨Metric.ball y 1, Metric.ball_mem_nhds y one_pos, ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hc.eventually_gt_atTop (y + 2))
  apply (Set.finite_Iio N).subset
  rintro i ⟨z, hz1, hz2⟩
  simp only [Set.mem_Iio]
  by_contra hi
  push Not at hi
  have h1 := hN i hi
  have h2 := h i z hz1
  rw [Metric.mem_ball, Real.dist_eq] at hz2
  rw [abs_le] at h2
  rw [abs_lt] at hz2
  linarith [h2.1, hz2.2]

/-! ### The bump profile -/

noncomputable def bmp : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

noncomputable def ψ (y : ℝ) : ℝ := y * bmp y

lemma ψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ :=
  contDiff_id.mul (bmp.contDiff (n := ⊤))

lemma ψ_supp : ∀ y, ψ y ≠ 0 → |y| ≤ 1 := by
  intro y hy
  have hb : bmp y ≠ 0 := by
    intro h0
    apply hy
    simp [ψ, h0]
  have : y ∈ support (bmp : ℝ → ℝ) := hb
  rw [bmp.support_eq] at this
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at this
  have : bmp.rOut = 1 := rfl
  linarith

lemma supp_deriv (φ : ℝ → ℝ) (h : ∀ y, φ y ≠ 0 → |y| ≤ 1) : ∀ y, deriv φ y ≠ 0 → |y| ≤ 1 := by
  intro y hy
  have h1 : y ∈ tsupport φ := support_deriv_subset hy
  have h2 : tsupport φ ⊆ {y : ℝ | |y| ≤ 1} :=
    closure_minimal (fun z hz => h z hz) (isClosed_le continuous_abs continuous_const)
  exact h2 h1

lemma bound_of (φ : ℝ → ℝ) (hc : Continuous φ) (h : ∀ y, φ y ≠ 0 → |y| ≤ 1) :
    ∃ B, 0 ≤ B ∧ ∀ y, |φ y| ≤ B := by
  have hcs : HasCompactSupport φ := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) 1)
    intro y hy
    by_contra hne
    apply hy
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    exact h y hne
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcs
  refine ⟨C, le_trans (abs_nonneg _) (hC 0), fun y => hC y⟩

lemma ψ_diff : Differentiable ℝ ψ := ψ_smooth.differentiable (by simp)

lemma dψ_smooth : ContDiff ℝ (⊤ : ℕ∞) (deriv ψ) := by
  have := ψ_smooth.iterate_deriv 1
  simpa using this

lemma ddψ_smooth : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv ψ)) := by
  have := ψ_smooth.iterate_deriv 2
  simpa using this

lemma dψ_zero : deriv ψ 0 = 1 := by
  have h : ψ =ᶠ[𝓝 0] id := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with y hy
    have : bmp y = 1 := bmp.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
    simp [ψ, this]
  rw [h.deriv_eq]
  simp

/-! ### Scaled copies -/

lemma deriv_scaled (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) (c a r : ℝ) :
    deriv (fun x => c * φ ((x - a) / r)) = fun x => c / r * deriv φ ((x - a) / r) := by
  funext x
  have h1 : HasDerivAt (fun x : ℝ => (x - a) / r) (1 / r) x := by
    simpa using ((hasDerivAt_id x).sub_const a).div_const r
  have h2 : HasDerivAt (fun x => c * φ ((x - a) / r)) (c * (deriv φ ((x - a) / r) * (1 / r))) x :=
    ((hφ ((x - a) / r)).hasDerivAt.comp x h1).const_mul c
  rw [h2.deriv]
  ring

lemma supp_scaled (φ : ℝ → ℝ) (h : ∀ y, φ y ≠ 0 → |y| ≤ 1) (c a r x : ℝ) (hr : 0 < r)
    (hx : c * φ ((x - a) / r) ≠ 0) : |x - a| ≤ r := by
  have h1 : φ ((x - a) / r) ≠ 0 := by
    intro h0
    apply hx
    simp [h0]
  have h2 := h _ h1
  rw [abs_div, abs_of_pos hr, div_le_one hr] at h2
  exact h2

/-! ### The sequences -/

noncomputable def gg (τ : ℝ) (k : ℕ) : ℝ := (1 / ((k : ℝ) + 1)) ^ (1 / (2 - τ))

noncomputable def rr (τ αlo : ℝ) (k : ℕ) : ℝ := αlo * gg τ k / 3

noncomputable def xs (τ : ℝ) (α : ℕ → ℝ) (k : ℕ) : ℝ := ∑ j ∈ Finset.range k, α j * gg τ j

noncomputable def TT (τ αlo : ℝ) (α : ℕ → ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  -(gg τ k * rr τ αlo k) * ψ ((x - xs τ α k) / rr τ αlo k)

section seq

variable (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1)

include hτ1 in
lemma p_pos : 0 < 1 / (2 - τ) := by
  apply div_pos one_pos; linarith

include hτ1 in
lemma p_le_one : 1 / (2 - τ) ≤ 1 := by
  have h : (0 : ℝ) < 2 - τ := by linarith
  rw [div_le_one h]; linarith

lemma base_pos (k : ℕ) : 0 < 1 / ((k : ℝ) + 1) := by positivity

lemma base_le_one (k : ℕ) : 1 / ((k : ℝ) + 1) ≤ 1 := by
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

lemma gg_pos (k : ℕ) : 0 < gg τ k := Real.rpow_pos_of_pos (base_pos k) _

include hτ1 in
lemma gg_le_one (k : ℕ) : gg τ k ≤ 1 :=
  Real.rpow_le_one (base_pos k).le (base_le_one k) (p_pos τ hτ1).le

include hτ1 in
lemma gg_ge (k : ℕ) : 1 / ((k : ℝ) + 1) ≤ gg τ k := by
  have := Real.rpow_le_rpow_of_exponent_ge (base_pos k) (base_le_one k) (p_le_one τ hτ1)
  rwa [Real.rpow_one] at this

include hτ1 in
lemma gg_anti {j k : ℕ} (hjk : j ≤ k) : gg τ k ≤ gg τ j := by
  apply Real.rpow_le_rpow (base_pos k).le _ (p_pos τ hτ1).le
  apply one_div_le_one_div_of_le (by positivity)
  have : (j : ℝ) ≤ k := Nat.cast_le.2 hjk
  linarith

include hτ1 in
lemma gg_pow (k : ℕ) : gg τ k ^ (2 - τ) = 1 / ((k : ℝ) + 1) := by
  unfold gg
  rw [← Real.rpow_mul (base_pos k).le]
  have hne : (2 - τ) ≠ 0 := by linarith
  have : 1 / (2 - τ) * (2 - τ) = 1 := by
    rw [one_div, inv_mul_cancel₀ hne]
  rw [this, Real.rpow_one]

end seq

section main

variable (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (αlo αhi : ℝ) (hlo : 0 < αlo) (hlohi : αlo ≤ αhi) (hhi : αhi < 2)
    (α : ℕ → ℝ) (hα : ∀ k, αlo ≤ α k ∧ α k ≤ αhi)

include hlo in
lemma rr_pos (k : ℕ) : 0 < rr τ αlo k := by
  unfold rr
  have := gg_pos τ k
  positivity

include hτ1 hhi hlohi in
lemma rr_le_one (k : ℕ) : rr τ αlo k ≤ 1 := by
  unfold rr
  have h1 := gg_le_one τ hτ1 k
  have h2 := gg_pos τ k
  rw [div_le_one (by norm_num)]
  nlinarith

lemma xs_succ (k : ℕ) : xs τ α (k + 1) = xs τ α k + α k * gg τ k := by
  unfold xs
  rw [Finset.sum_range_succ]

include hlo hα in
lemma xs_mono : Monotone (xs τ α) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [xs_succ]
  have h1 := gg_pos τ k
  have h2 := (hα k).1
  nlinarith

include hτ1 hlo hα in
lemma xs_tendsto : Tendsto (xs τ α) atTop atTop := by
  have h := Real.tendsto_sum_range_one_div_nat_succ_atTop.const_mul_atTop hlo
  apply tendsto_atTop_mono _ h
  intro k
  unfold xs
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have h1 := gg_ge τ hτ1 j
  have h2 := (hα j).1
  have h3 : (0 : ℝ) ≤ 1 / ((j : ℝ) + 1) := (base_pos j).le
  have h4 := gg_pos τ j
  nlinarith

include hτ1 hlo hα in
lemma sep_lt (i j : ℕ) (hij : i < j) (x : ℝ) (hi : |x - xs τ α i| ≤ rr τ αlo i)
    (hj : |x - xs τ α j| ≤ rr τ αlo j) : False := by
  have h1 : xs τ α (i + 1) ≤ xs τ α j := xs_mono τ αlo αhi hlo α hα hij
  rw [xs_succ] at h1
  have h2 : αlo * gg τ i ≤ α i * gg τ i :=
    mul_le_mul_of_nonneg_right (hα i).1 (gg_pos τ i).le
  have h3 : rr τ αlo j ≤ rr τ αlo i := by
    unfold rr
    have := gg_anti τ hτ1 hij.le
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact mul_le_mul_of_nonneg_left this hlo.le
  have h4 := rr_pos τ αlo hlo i
  have h5 : rr τ αlo i * 3 = αlo * gg τ i := by unfold rr; ring
  rw [abs_le] at hi hj
  linarith [hi.1, hi.2, hj.1, hj.2]

include hτ1 hlo hα in
lemma sep (i j : ℕ) (x : ℝ) (hi : |x - xs τ α i| ≤ rr τ αlo i)
    (hj : |x - xs τ α j| ≤ rr τ αlo j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exact (sep_lt τ hτ1 αlo αhi hlo α hα i j h x hi hj).elim
  · exact h
  · exact (sep_lt τ hτ1 αlo αhi hlo α hα j i h x hj hi).elim

end main

theorem main (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (αlo αhi : ℝ) (hlo : 0 < αlo) (hlohi : αlo ≤ αhi) (hhi : αhi < 2)
    (α : ℕ → ℝ) (hα : ∀ k, αlo ≤ α k ∧ α k ≤ αhi) :
    ∃ f : ℝ → ℝ, ContDiff ℝ 2 f ∧ BddBelow (Set.range f) ∧ (∃ M : ℝ, ∀ x, |deriv f x| ≤ M) ∧
      (∃ L : NNReal, LipschitzWith L (deriv f)) ∧
      ∃ x : ℕ → ℝ, x 0 = 0 ∧ (∀ k : ℕ, x (k + 1) = x k - α k * deriv f (x k)) ∧
        (∀ k : ℕ, |deriv f (x k)| = (1 / ((k : ℝ) + 1)) ^ (1 / (2 - τ))) ∧
        (∀ ε : ℝ, 0 < ε → ε < 1 → ∀ k : ℕ, |deriv f (x k)| ≤ ε →
          (⌊ε ^ (-(2 - τ))⌋₊ : ℝ) ≤ (k : ℝ) + 1) := by
  -- notation
  set g := gg τ with hg
  set r := rr τ αlo with hr
  set c := xs τ α with hc
  have rpos : ∀ k, 0 < r k := rr_pos τ αlo hlo
  have rle : ∀ k, r k ≤ 1 := rr_le_one τ hτ1 αlo αhi hlohi hhi
  have gpos : ∀ k, 0 < g k := gg_pos τ
  have gle : ∀ k, g k ≤ 1 := gg_le_one τ hτ1
  have ctend : Filter.Tendsto c Filter.atTop Filter.atTop := xs_tendsto τ hτ1 αlo αhi hlo α hα
  have hsep : ∀ i j x, |x - c i| ≤ r i → |x - c j| ≤ r j → i = j :=
    sep τ hτ1 αlo αhi hlo α hα
  have hdψ := supp_deriv ψ ψ_supp
  have hddψ := supp_deriv (deriv ψ) hdψ
  -- the three families
  set T : ℕ → ℝ → ℝ := fun k x => -(g k * r k) * ψ ((x - c k) / r k) with hT
  set D : ℕ → ℝ → ℝ := fun k x => -(g k * r k) / r k * deriv ψ ((x - c k) / r k) with hD
  set E : ℕ → ℝ → ℝ := fun k x => -(g k * r k) / r k / r k * deriv (deriv ψ) ((x - c k) / r k)
    with hE
  have dT : ∀ k, deriv (T k) = D k := fun k => deriv_scaled ψ ψ_diff _ _ _
  have dD : ∀ k, deriv (D k) = E k := fun k =>
    deriv_scaled (deriv ψ) (dψ_smooth.differentiable (by simp)) _ _ _
  have smooth_aff : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => (x - c k) / r k) := fun k =>
    (contDiff_id.sub contDiff_const).div_const _
  have Tsm : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (T k) := fun k =>
    contDiff_const.mul (ψ_smooth.comp (smooth_aff k))
  have Dsm : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (D k) := fun k =>
    contDiff_const.mul (dψ_smooth.comp (smooth_aff k))
  have Tsupp : ∀ k x, T k x ≠ 0 → |x - c k| ≤ r k := fun k x h =>
    supp_scaled ψ ψ_supp _ _ _ x (rpos k) h
  have Dsupp : ∀ k x, D k x ≠ 0 → |x - c k| ≤ r k := fun k x h =>
    supp_scaled (deriv ψ) hdψ _ _ _ x (rpos k) h
  have Esupp : ∀ k x, E k x ≠ 0 → |x - c k| ≤ r k := fun k x h =>
    supp_scaled (deriv (deriv ψ)) hddψ _ _ _ x (rpos k) h
  have lf1 : ∀ G : ℕ → ℝ → ℝ, (∀ k x, G k x ≠ 0 → |x - c k| ≤ r k) →
      LocallyFinite fun i => Function.support (G i) := fun G hG =>
    lf_of G c ctend (fun k x h => le_trans (hG k x h) (rle k))
  have dj : ∀ G : ℕ → ℝ → ℝ, (∀ k x, G k x ≠ 0 → |x - c k| ≤ r k) →
      ∀ x i j, G i x ≠ 0 → G j x ≠ 0 → i = j := fun G hG x i j hi hj =>
    hsep i j x (hG i x hi) (hG j x hj)
  have TlF := lf1 T Tsupp
  have DlF := lf1 D Dsupp
  have ElF := lf1 E Esupp
  -- bounds of the profile
  obtain ⟨B0, hB0, hb0⟩ := bound_of ψ ψ_smooth.continuous ψ_supp
  obtain ⟨B1, hB1, hb1⟩ := bound_of (deriv ψ) dψ_smooth.continuous hdψ
  obtain ⟨B2, hB2, hb2⟩ := bound_of (deriv (deriv ψ)) ddψ_smooth.continuous hddψ
  set f : ℝ → ℝ := fun x => ∑ᶠ k, T k x with hf
  have hdf : deriv f = fun y => ∑ᶠ k, D k y := by
    rw [hf, deriv_fs T (fun k => (Tsm k).differentiable (by simp)) TlF]
    funext y
    simp only [dT]
  have hddf : deriv (deriv f) = fun y => ∑ᶠ k, E k y := by
    rw [hdf, deriv_fs D (fun k => (Dsm k).differentiable (by simp)) DlF]
    funext y
    simp only [dD]
  have coefD : ∀ k, -(g k * r k) / r k = -g k := fun k => by
    field_simp [(rpos k).ne']
  have coefE : ∀ k, |-(g k * r k) / r k / r k| = 3 / αlo := fun k => by
    rw [coefD k]
    have h5 : r k = αlo * g k / 3 := rfl
    have : -g k / r k = -(3 / αlo) := by
      rw [h5]
      field_simp [(gpos k).ne', hlo.ne']
    rw [this, abs_neg, abs_of_pos (by positivity)]
  -- derivative at the iterates
  have dfc : ∀ k, deriv f (c k) = -g k := by
    intro k
    rw [hdf]
    simp only
    rw [finsum_eq_single (fun j => D j (c k)) k (fun j hj => by
      by_contra hne
      exact hj (hsep j k (c k) (Dsupp j (c k) hne) (by simp [(rpos k).le])))]
    simp only [hD, sub_self, zero_div, dψ_zero, mul_one]
    exact coefD k
  refine ⟨f, ?_, ?_, ?_, ?_, c, ?_, ?_, ?_, ?_⟩
  · exact contDiff_fs T (fun k => by exact_mod_cast contDiff_infty.1 (Tsm k) 2) TlF
  · refine ⟨-B0, ?_⟩
    rintro _ ⟨x, rfl⟩
    have hb : ∀ k x, |T k x| ≤ B0 := by
      intro k x
      show |(-(g k * r k)) * ψ ((x - c k) / r k)| ≤ B0
      rw [abs_mul, abs_neg]
      have h1 : |g k * r k| ≤ 1 := by
        rw [abs_of_pos (mul_pos (gpos k) (rpos k))]
        nlinarith [gpos k, rpos k, gle k, rle k]
      have h2 := hb0 ((x - c k) / r k)
      exact le_trans (mul_le_mul h1 h2 (abs_nonneg _) zero_le_one) (by linarith)
    have := abs_fs_le T B0 hB0 hb (dj T Tsupp) x
    have := (abs_le.1 this).1
    exact this
  · refine ⟨B1, ?_⟩
    intro x
    rw [hdf]
    apply abs_fs_le D B1 hB1 _ (dj D Dsupp) x
    intro k y
    show |(-(g k * r k) / r k) * deriv ψ ((y - c k) / r k)| ≤ B1
    rw [abs_mul, coefD k, abs_neg, abs_of_pos (gpos k)]
    exact le_trans (mul_le_mul (gle k) (hb1 _) (abs_nonneg _) zero_le_one) (by linarith)
  · refine ⟨⟨3 / αlo * B2, by positivity⟩, ?_⟩
    apply lipschitzWith_of_nnnorm_deriv_le
    · rw [hdf]
      exact (contDiff_fs D (fun k => Dsm k) DlF).differentiable (by simp)
    · intro x
      apply NNReal.coe_le_coe.1
      simp only [coe_nnnorm, Real.norm_eq_abs]
      rw [hddf]
      apply abs_fs_le E (3 / αlo * B2) (by positivity) _ (dj E Esupp) x
      intro k y
      show |(-(g k * r k) / r k / r k) * deriv (deriv ψ) ((y - c k) / r k)| ≤ 3 / αlo * B2
      rw [abs_mul, coefE k]
      have h3 : 0 ≤ 3 / αlo := by positivity
      exact mul_le_mul_of_nonneg_left (hb2 _) h3
  · show xs τ α 0 = 0
    simp [xs]
  · intro k
    rw [dfc k, hc, xs_succ]
    ring
  · intro k
    rw [dfc k, abs_neg, abs_of_pos (gpos k)]
    rfl
  · intro ε hε0 hε1 k hk
    rw [dfc k, abs_neg, abs_of_pos (gpos k)] at hk
    have h2 : 0 ≤ 2 - τ := by linarith
    have h1 : g k ^ (2 - τ) ≤ ε ^ (2 - τ) := Real.rpow_le_rpow (gpos k).le hk h2
    rw [hg, gg_pow τ hτ1 k] at h1
    have hεp : 0 < ε ^ (2 - τ) := Real.rpow_pos_of_pos hε0 _
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h3 : (ε ^ (2 - τ))⁻¹ ≤ (k : ℝ) + 1 := by
      apply inv_le_of_inv_le₀ hk1
      rw [inv_eq_one_div]
      exact h1
    rw [Real.rpow_neg hε0.le]
    have h4 := Nat.floor_le (inv_nonneg.2 hεp.le)
    linarith

end B01358bcAux

theorem solution (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (αlo αhi : ℝ) (hlo : 0 < αlo) (hlohi : αlo ≤ αhi) (hhi : αhi < 2)
    (α : ℕ → ℝ) (hα : ∀ k, αlo ≤ α k ∧ α k ≤ αhi) :
    ∃ f : ℝ → ℝ, ContDiff ℝ 2 f ∧ BddBelow (Set.range f) ∧ (∃ M : ℝ, ∀ x, |deriv f x| ≤ M) ∧
      (∃ L : NNReal, LipschitzWith L (deriv f)) ∧
      ∃ x : ℕ → ℝ, x 0 = 0 ∧ (∀ k : ℕ, x (k + 1) = x k - α k * deriv f (x k)) ∧
        (∀ k : ℕ, |deriv f (x k)| = (1 / ((k : ℝ) + 1)) ^ (1 / (2 - τ))) ∧
        (∀ ε : ℝ, 0 < ε → ε < 1 → ∀ k : ℕ, |deriv f (x k)| ≤ ε →
          (⌊ε ^ (-(2 - τ))⌋₊ : ℝ) ≤ (k : ℝ) + 1) := by
  exact B01358bcAux.main τ hτ0 hτ1 αlo αhi hlo hlohi hhi α hα
