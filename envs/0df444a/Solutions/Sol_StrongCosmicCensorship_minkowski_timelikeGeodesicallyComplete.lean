-- Prove2me | solution 1 for StrongCosmicCensorship.minkowski_timelikeGeodesicallyComplete
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T18:51:52.8699+00:00
-- url     : https://prove2.me/submissions/0eb85754-0a78-4567-a0f8-9cbfa25c7e80

import Mathlib
import Definitions.Def_scc_coordinate_framework

/-! Disproof of 7580707c `StrongCosmicCensorship.minkowski_timelikeGeodesicallyComplete`.

`vel` and `acc` are built from `deriv`, which is `0` wherever the function is not
differentiable.  So a curve that jumps can meet the geodesic equation `acc = 0` and the
normalisation `g(vel, vel) = -1` on `[0, 1)` without being extendable to `[0, ∞)`.

Counterexample, with `osc t = sin (π / (1 - t))` (zero exactly at `t = 1 - 1/k`, `t < 1`):
* `γ⁰ = (5/4) t`
* `γ¹ = (3/4) t + [osc t = 0]`            (jumps at the isolated zeros of `osc`)
* `γ² = (3/4) t + 1_ℚ(t) · osc(t)²`       (Dirichlet-type, differentiable only at zeros of `osc`)
* `γ³ = 0`.
On `[0,1)` the velocity is `(5/4, 3/4, 0, 0)` off the zeros and `(5/4, 0, 3/4, 0)` on them;
both have Minkowski norm `-1`, and every velocity component is locally constant off an
isolated point, so `acc = 0`.  Any extension has, at `τ = 1`, `vel⁰ ∈ {0, 5/4}`, `vel³ = 0`,
and `vel¹ = vel² = 0` (neither `γ¹` nor `γ²` has a limit as `t → 1⁻`), so its norm at `1`
is `0` or `-25/16`, never `-1`. -/

set_option autoImplicit false

open Set Filter
open scoped Matrix Topology

namespace StrongCosmicCensorship.DP7580

/-! ### The curve -/

/-- The oscillating factor. -/
noncomputable def osc (t : ℝ) : ℝ := Real.sin (Real.pi / (1 - t))

/-- Jump of height one at the zeros of `osc`. -/
noncomputable def jmp (t : ℝ) : ℝ := if osc t = 0 then 1 else 0

/-- Dirichlet-type term: `osc²` on the rationals, `0` on the irrationals. -/
noncomputable def dq (t : ℝ) : ℝ :=
  Set.indicator (Set.range ((↑) : ℚ → ℝ)) (fun u => osc u ^ 2) t

/-- The counterexample curve. -/
noncomputable def γ (t : ℝ) : Coords :=
  ![(5/4 : ℝ) * t, (3/4 : ℝ) * t + jmp t, (3/4 : ℝ) * t + dq t, 0]


/-! ### Minkowski reductions -/

lemma christoffel_minkowski (a b c : Fin 4) (x : Coords) :
    christoffel minkowski a b c x = 0 := by
  simp [christoffel, pd, minkowski]

lemma gip_minkowski (x v : Coords) :
    gip minkowski x v v = -(v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2 := by
  simp [gip, minkowski, minkowskiMatrix, Fin.sum_univ_four, Matrix.diagonal]
  ring

/-! ### Real-analysis helpers -/

lemma hasDerivAt_line (c x : ℝ) : HasDerivAt (fun t : ℝ => c * t) c x := by
  simpa using (hasDerivAt_id x).const_mul c

/-- A function equal to a constant on a punctured neighbourhood but not at the point is not
differentiable there. -/
lemma not_diff_of_punctured (f : ℝ → ℝ) (x c : ℝ) (h : f =ᶠ[𝓝[≠] x] fun _ => c)
    (hx : f x ≠ c) : ¬ DifferentiableAt ℝ f x := by
  intro hd
  have h1 : Tendsto f (𝓝[≠] x) (𝓝 (f x)) :=
    hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto f (𝓝[≠] x) (𝓝 c) := tendsto_const_nhds.congr' h.symm
  exact hx (tendsto_nhds_unique h1 h2)

/-- A function constant on a punctured neighbourhood has `deriv = 0` at the point. -/
lemma deriv_zero_of_punctured_const (f : ℝ → ℝ) (x c : ℝ) (h : f =ᶠ[𝓝[≠] x] fun _ => c) :
    deriv f x = 0 := by
  by_cases hx : f x = c
  · have h' : f =ᶠ[𝓝 x] fun _ => c := by
      rw [Filter.EventuallyEq, ← nhdsNE_sup_pure x, Filter.eventually_sup]
      exact ⟨h, by simpa using hx⟩
    rw [h'.deriv_eq]
    simp
  · exact deriv_zero_of_not_differentiableAt (not_diff_of_punctured f x c h hx)

lemma deriv_line_add_of_not_diff (c : ℝ) (j : ℝ → ℝ) (x : ℝ) (hj : ¬ DifferentiableAt ℝ j x) :
    deriv (fun t => c * t + j t) x = 0 := by
  apply deriv_zero_of_not_differentiableAt
  intro hd
  apply hj
  have h2 : DifferentiableAt ℝ (fun t : ℝ => c * t) x := (hasDerivAt_line c x).differentiableAt
  have h3 := hd.sub h2
  refine h3.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp

/-- Squeeze: `|f| ≤ |g|`, `g(x) = 0`, `g'(x) = 0` give `f'(x) = 0`. -/
lemma hasDerivAt_zero_of_le (f g : ℝ → ℝ) (x : ℝ) (hg : HasDerivAt g 0 x) (hgx : g x = 0)
    (hfx : f x = 0) (hle : ∀ t, |f t| ≤ |g t|) : HasDerivAt f 0 x := by
  rw [hasDerivAt_iff_isLittleO] at hg ⊢
  simp only [hfx, hgx, sub_zero, smul_zero] at hg ⊢
  refine Asymptotics.IsBigO.trans_isLittleO ?_ hg
  exact Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun t => by simpa using hle t)

/-- `1_ℚ · h` is discontinuous where `h` is continuous and nonzero. -/
lemma not_continuousAt_indicator (h : ℝ → ℝ) (x : ℝ) (hc : ContinuousAt h x) (hx : h x ≠ 0) :
    ¬ ContinuousAt (Set.indicator (Set.range ((↑) : ℚ → ℝ)) h) x := by
  intro hf
  have hirr : ∃ᶠ t in 𝓝 x,
      Set.indicator (Set.range ((↑) : ℚ → ℝ)) h t = (fun _ => (0:ℝ)) t := by
    have : ∃ᶠ t in 𝓝 x, t ∈ {t : ℝ | Irrational t} := by
      rw [← mem_closure_iff_frequently, dense_irrational.closure_eq]; exact mem_univ x
    refine this.mono fun t ht => ?_
    simp only [Set.indicator_apply_eq_zero]
    rintro ⟨q, rfl⟩
    exact (Rat.not_irrational q ht).elim
  have hrat : ∃ᶠ t in 𝓝 x, Set.indicator (Set.range ((↑) : ℚ → ℝ)) h t = h t := by
    have : ∃ᶠ t in 𝓝 x, t ∈ Set.range ((↑) : ℚ → ℝ) := by
      rw [← mem_closure_iff_frequently, (Rat.denseRange_cast (𝕜 := ℝ)).closure_eq]; exact mem_univ x
    exact this.mono fun t ht => Set.indicator_of_mem ht h
  have e1 := tendsto_nhds_unique_of_frequently_eq hf.tendsto tendsto_const_nhds hirr
  have e2 := tendsto_nhds_unique_of_frequently_eq hf.tendsto hc.tendsto hrat
  exact hx (e2.symm.trans e1)

/-! ### The oscillating factor -/

lemma osc_hasDerivAt (t0 : ℝ) (ht : t0 < 1) :
    HasDerivAt osc (Real.cos (Real.pi / (1 - t0)) * (Real.pi / (1 - t0) ^ 2)) t0 := by
  have hne : (1 - t0) ≠ 0 := by intro h; linarith
  have hd : HasDerivAt (fun t => Real.pi / (1 - t)) (Real.pi / (1 - t0) ^ 2) t0 := by
    have h1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) t0 := by
      simpa using (hasDerivAt_id' t0).const_sub (1:ℝ)
    have h2 := (hasDerivAt_const t0 Real.pi).fun_div h1 hne
    exact h2.congr_deriv (by ring)
  exact (Real.hasDerivAt_sin (Real.pi / (1 - t0))).comp t0 hd

lemma osc_cont (t0 : ℝ) (ht : t0 < 1) : ContinuousAt osc t0 :=
  (osc_hasDerivAt t0 ht).continuousAt

lemma osc_isolated (t0 : ℝ) (ht : t0 < 1) (h0 : osc t0 = 0) : ∀ᶠ t in 𝓝[≠] t0, osc t ≠ 0 := by
  have hne : (1 - t0) ≠ 0 := by intro h; linarith
  have hcos : Real.cos (Real.pi / (1 - t0)) ≠ 0 := by
    intro hc
    have := Real.sin_sq_add_cos_sq (Real.pi / (1 - t0))
    have h0' : Real.sin (Real.pi / (1 - t0)) = 0 := h0
    rw [h0', hc] at this; norm_num at this
  have hder : Real.cos (Real.pi / (1 - t0)) * (Real.pi / (1 - t0) ^ 2) ≠ 0 :=
    mul_ne_zero hcos (div_ne_zero Real.pi_ne_zero (pow_ne_zero 2 hne))
  have := (osc_hasDerivAt t0 ht).eventually_ne (c := 0) hder
  exact this

lemma ev_good (τ : ℝ) (hτ : τ < 1) : ∀ᶠ t in 𝓝[≠] τ, t < 1 ∧ osc t ≠ 0 := by
  have h1 : ∀ᶠ t in 𝓝[≠] τ, t < 1 := nhdsWithin_le_nhds (Iio_mem_nhds hτ)
  have h2 : ∀ᶠ t in 𝓝[≠] τ, osc t ≠ 0 := by
    by_cases h0 : osc τ = 0
    · exact osc_isolated τ hτ h0
    · exact nhdsWithin_le_nhds ((osc_cont τ hτ).eventually_ne h0)
  exact h1.and h2

/-! ### Velocity on `[0, 1)` -/

lemma deriv_g1 (τ : ℝ) (hτ : τ < 1) :
    deriv (fun t => (3/4 : ℝ) * t + jmp t) τ = if osc τ = 0 then 0 else 3/4 := by
  split_ifs with h0
  · apply deriv_line_add_of_not_diff
    apply not_diff_of_punctured jmp τ 0
    · filter_upwards [osc_isolated τ hτ h0] with t ht
      simp [jmp, ht]
    · simp [jmp, h0]
  · have hj : jmp =ᶠ[𝓝 τ] fun _ => 0 := by
      filter_upwards [(osc_cont τ hτ).eventually_ne h0] with t ht
      simp [jmp, ht]
    have := (hasDerivAt_line (3/4) τ).fun_add ((hasDerivAt_const τ (0:ℝ)).congr_of_eventuallyEq hj)
    exact this.deriv.trans (add_zero _)

lemma abs_dq_le (t : ℝ) : |dq t| ≤ |(fun u => osc u ^ 2) t| := by
  classical
  simp only [dq, Set.indicator_apply]
  split_ifs <;> simp [sq_nonneg]

lemma dq_of_osc_zero (t : ℝ) (h0 : osc t = 0) : dq t = 0 := by
  classical
  simp [dq, Set.indicator_apply, h0]

lemma deriv_g2 (τ : ℝ) (hτ : τ < 1) :
    deriv (fun t => (3/4 : ℝ) * t + dq t) τ = if osc τ = 0 then 3/4 else 0 := by
  split_ifs with h0
  · have hsq : HasDerivAt (fun t => osc t ^ 2) 0 τ :=
      ((osc_hasDerivAt τ hτ).fun_pow 2).congr_deriv (by simp [h0])
    have hdq : HasDerivAt dq 0 τ :=
      hasDerivAt_zero_of_le dq (fun t => osc t ^ 2) τ hsq (by simp [h0])
        (dq_of_osc_zero τ h0) abs_dq_le
    exact ((hasDerivAt_line (3/4) τ).fun_add hdq).deriv.trans (add_zero _)
  · apply deriv_line_add_of_not_diff
    intro hd
    exact not_continuousAt_indicator (fun u => osc u ^ 2) τ ((osc_cont τ hτ).fun_pow 2)
      (pow_ne_zero 2 h0) hd.continuousAt

lemma vel0 (τ : ℝ) : vel γ τ 0 = 5/4 := by
  show deriv (fun t => (5/4 : ℝ) * t) τ = 5/4
  exact (hasDerivAt_line _ τ).deriv

lemma vel3 (τ : ℝ) : vel γ τ 3 = 0 := by
  show deriv (fun _ => (0 : ℝ)) τ = 0
  simp

lemma vel1 (τ : ℝ) (hτ : τ < 1) : vel γ τ 1 = if osc τ = 0 then 0 else 3/4 := by
  show deriv (fun t => (3/4 : ℝ) * t + jmp t) τ = _
  exact deriv_g1 τ hτ

lemma vel2 (τ : ℝ) (hτ : τ < 1) : vel γ τ 2 = if osc τ = 0 then 3/4 else 0 := by
  show deriv (fun t => (3/4 : ℝ) * t + dq t) τ = _
  exact deriv_g2 τ hτ

/-! ### Acceleration on `[0, 1)` -/

lemma acc0 (τ : ℝ) : acc γ τ 0 = 0 := by
  show deriv (fun s => vel γ s 0) τ = 0
  simp only [vel0]
  simp

lemma acc3 (τ : ℝ) : acc γ τ 3 = 0 := by
  show deriv (fun s => vel γ s 3) τ = 0
  simp only [vel3]
  simp

lemma acc1 (τ : ℝ) (hτ : τ < 1) : acc γ τ 1 = 0 := by
  show deriv (fun s => vel γ s 1) τ = 0
  apply deriv_zero_of_punctured_const _ τ (3/4)
  filter_upwards [ev_good τ hτ] with t ht
  show vel γ t 1 = 3/4
  rw [vel1 t ht.1, if_neg ht.2]

lemma acc2 (τ : ℝ) (hτ : τ < 1) : acc γ τ 2 = 0 := by
  show deriv (fun s => vel γ s 2) τ = 0
  apply deriv_zero_of_punctured_const _ τ 0
  filter_upwards [ev_good τ hτ] with t ht
  show vel γ t 2 = 0
  rw [vel2 t ht.1, if_neg ht.2]

lemma gip_on (τ : ℝ) (hτ : τ < 1) : gip minkowski (γ τ) (vel γ τ) (vel γ τ) = -1 := by
  rw [gip_minkowski, vel0, vel3, vel1 τ hτ, vel2 τ hτ]
  split_ifs <;> norm_num

/-- The hypothesis of completeness holds for `γ` on `[0, 1)`. -/
lemma hyp : IsTimelikeGeodesicOn (univ : Set Coords) minkowski (Ico 0 1) γ := by
  refine ⟨?_, fun _ _ => mem_univ _, fun τ hτ => gip_on τ hτ.2⟩
  intro τ hτ a
  simp only [christoffel_minkowski, zero_mul, Finset.sum_const_zero, add_zero]
  fin_cases a
  · exact acc0 τ
  · exact acc1 τ hτ.2
  · exact acc2 τ hτ.2
  · exact acc3 τ

/-! ### No extension through `τ = 1` -/

/-- Agreeing with `c t` on `[0,1)` forces `deriv f 1 ∈ {0, c}`. -/
lemma deriv_at_one (f : ℝ → ℝ) (c : ℝ) (hf : ∀ t ∈ Ico (0:ℝ) 1, f t = c * t) :
    deriv f 1 = 0 ∨ deriv f 1 = c := by
  by_cases hd : DifferentiableAt ℝ f 1
  · right
    have h1 : HasDerivWithinAt f (deriv f 1) (Ico 0 1) 1 := hd.hasDerivAt.hasDerivWithinAt
    have hf1 : f 1 = c * 1 := by
      have hcont : Tendsto f (𝓝[Ico 0 1] 1) (𝓝 (f 1)) :=
        hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have hlin : Tendsto f (𝓝[Ico 0 1] 1) (𝓝 (c * 1)) := by
        have : Tendsto (fun t : ℝ => c * t) (𝓝[Ico 0 1] 1) (𝓝 (c * 1)) :=
          ((continuous_const.mul continuous_id).tendsto 1).mono_left nhdsWithin_le_nhds
        exact this.congr' (eventually_nhdsWithin_of_forall fun t ht => (hf t ht).symm)
      have : (𝓝[Ico (0:ℝ) 1] 1).NeBot := by
        rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ico (by norm_num)]; simp
      exact tendsto_nhds_unique hcont hlin
    have h2 : HasDerivWithinAt f c (Ico 0 1) 1 :=
      (hasDerivAt_line c 1).hasDerivWithinAt.congr (fun t ht => hf t ht) hf1
    have hu : UniqueDiffWithinAt ℝ (Ico (0:ℝ) 1) 1 :=
      uniqueDiffWithinAt_convex (convex_Ico 0 1) (by rw [interior_Ico]; exact ⟨1/2, by norm_num⟩)
        (by rw [closure_Ico (by norm_num)]; simp)
    exact hu.eq_deriv _ h1 h2
  · left; exact deriv_zero_of_not_differentiableAt hd

/-- Two sequences tending to `1` along which `f` has different limits: `deriv f 1 = 0`. -/
lemma deriv_one_of_two_seq (f : ℝ → ℝ) (u v : ℕ → ℝ) (L M : ℝ) (hLM : L ≠ M)
    (hu : Tendsto u atTop (𝓝 1)) (hv : Tendsto v atTop (𝓝 1))
    (hfu : Tendsto (fun k => f (u k)) atTop (𝓝 L))
    (hfv : Tendsto (fun k => f (v k)) atTop (𝓝 M)) : deriv f 1 = 0 := by
  apply deriv_zero_of_not_differentiableAt
  intro hd
  have h1 := tendsto_nhds_unique (hd.continuousAt.tendsto.comp hu) hfu
  have h2 := tendsto_nhds_unique (hd.continuousAt.tendsto.comp hv) hfv
  exact hLM (h1.symm.trans h2)

/-- Zeros of `osc`. -/
noncomputable def sa (k : ℕ) : ℝ := 1 - 1 / ((k : ℝ) + 1)

/-- Rational points where `osc² = 1`. -/
noncomputable def sb (k : ℕ) : ℝ := 1 - 2 / (2 * (k : ℝ) + 3)

lemma sa_tendsto : Tendsto sa atTop (𝓝 1) := by
  have h : Tendsto (fun k : ℕ => (1:ℝ) / ((k:ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_mono (fun k => by linarith) tendsto_natCast_atTop_atTop)
  have := (tendsto_const_nhds (x := (1:ℝ))).sub h
  rw [sub_zero] at this
  exact this

lemma sb_tendsto : Tendsto sb atTop (𝓝 1) := by
  have h : Tendsto (fun k : ℕ => (2:ℝ) / (2 * (k:ℝ) + 3)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_mono (fun k => by have := (Nat.cast_nonneg k : (0:ℝ) ≤ k); linarith)
        tendsto_natCast_atTop_atTop)
  have := (tendsto_const_nhds (x := (1:ℝ))).sub h
  rw [sub_zero] at this
  exact this

lemma sa_mem (k : ℕ) : sa k ∈ Ico (0:ℝ) 1 := by
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hpos : (0:ℝ) < (k:ℝ) + 1 := by linarith
  have h1 : (1:ℝ) / ((k:ℝ) + 1) ≤ 1 := by rw [div_le_iff₀ hpos]; linarith
  have h2 : (0:ℝ) < 1 / ((k:ℝ) + 1) := by positivity
  show 0 ≤ 1 - 1 / ((k:ℝ) + 1) ∧ 1 - 1 / ((k:ℝ) + 1) < 1
  constructor <;> linarith

lemma sb_mem (k : ℕ) : sb k ∈ Ico (0:ℝ) 1 := by
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hpos : (0:ℝ) < 2 * (k:ℝ) + 3 := by linarith
  have h1 : (2:ℝ) / (2 * (k:ℝ) + 3) ≤ 1 := by rw [div_le_iff₀ hpos]; linarith
  have h2 : (0:ℝ) < 2 / (2 * (k:ℝ) + 3) := by positivity
  show 0 ≤ 1 - 2 / (2 * (k:ℝ) + 3) ∧ 1 - 2 / (2 * (k:ℝ) + 3) < 1
  constructor <;> linarith

lemma osc_sa (k : ℕ) : osc (sa k) = 0 := by
  have h1 : 1 - sa k = 1 / ((k:ℝ) + 1) := by simp only [sa]; ring
  rw [osc, h1, div_div_eq_mul_div, div_one, mul_comm]
  exact_mod_cast Real.sin_nat_mul_pi (k + 1)

lemma osc_sb (k : ℕ) : osc (sb k) ^ 2 = 1 := by
  have h1 : 1 - sb k = 2 / (2 * (k:ℝ) + 3) := by simp only [sb]; ring
  have hc : Real.cos (Real.pi / (1 - sb k)) = 0 := by
    rw [Real.cos_eq_zero_iff]
    refine ⟨(k:ℤ) + 1, ?_⟩
    rw [h1, div_div_eq_mul_div]
    push_cast
    ring
  have := Real.sin_sq_add_cos_sq (Real.pi / (1 - sb k))
  have h0sq : (0:ℝ) ^ 2 = 0 := by norm_num
  rw [hc, h0sq, add_zero] at this
  simp only [osc]
  exact this

lemma sb_rat (k : ℕ) : sb k ∈ Set.range ((↑) : ℚ → ℝ) :=
  ⟨1 - 2 / (2 * (k:ℚ) + 3), by unfold sb; push_cast; try ring⟩

lemma jmp_sa (k : ℕ) : jmp (sa k) = 1 := by simp [jmp, osc_sa k]

lemma jmp_sb (k : ℕ) : jmp (sb k) = 0 := by
  have : osc (sb k) ≠ 0 := by
    intro h; have := osc_sb k; rw [h] at this; norm_num at this
  simp [jmp, this]

lemma dq_sa (k : ℕ) : dq (sa k) = 0 := dq_of_osc_zero _ (osc_sa k)

lemma dq_sb (k : ℕ) : dq (sb k) = 1 := by
  unfold dq
  rw [Set.indicator_of_mem (sb_rat k)]
  exact osc_sb k

/-- The obstruction at `τ = 1`. -/
lemma no_ext (γ' : ℝ → Coords) (hEq : EqOn γ' γ (Ico 0 1))
    (hgeo : IsTimelikeGeodesicOn (univ : Set Coords) minkowski (Ici 0) γ') : False := by
  have hn := hgeo.2.2 1 (by norm_num : (1:ℝ) ∈ Ici 0)
  rw [gip_minkowski] at hn
  -- component 0
  have h0 : vel γ' 1 0 = 0 ∨ vel γ' 1 0 = 5/4 :=
    deriv_at_one (fun s => γ' s 0) (5/4) (fun t ht => by
      show γ' t 0 = 5/4 * t
      rw [hEq ht]; rfl)
  -- component 3
  have h3 : vel γ' 1 3 = 0 := by
    have := deriv_at_one (fun s => γ' s 3) 0 (fun t ht => by
      show γ' t 3 = 0 * t
      rw [hEq ht, zero_mul]; rfl)
    rcases this with h | h <;> exact h
  -- component 1: jumps accumulate at 1
  have h1 : vel γ' 1 1 = 0 := by
    apply deriv_one_of_two_seq (fun s => γ' s 1) sa sb (3/4 * 1 + 1) (3/4 * 1)
      (by norm_num) sa_tendsto sb_tendsto
    · refine (((tendsto_const_nhds (x := (3/4 : ℝ))).mul sa_tendsto).add
        (tendsto_const_nhds (x := (1 : ℝ)))).congr (fun k => ?_)
      show (3/4 : ℝ) * sa k + 1 = γ' (sa k) 1
      rw [hEq (sa_mem k)]
      show _ = (3/4 : ℝ) * sa k + jmp (sa k)
      rw [jmp_sa]
    · refine ((tendsto_const_nhds (x := (3/4 : ℝ))).mul sb_tendsto).congr (fun k => ?_)
      show (3/4 : ℝ) * sb k = γ' (sb k) 1
      rw [hEq (sb_mem k)]
      show _ = (3/4 : ℝ) * sb k + jmp (sb k)
      rw [jmp_sb, add_zero]
  -- component 2: the Dirichlet term has no limit at 1
  have h2 : vel γ' 1 2 = 0 := by
    apply deriv_one_of_two_seq (fun s => γ' s 2) sa sb (3/4 * 1) (3/4 * 1 + 1)
      (by norm_num) sa_tendsto sb_tendsto
    · refine ((tendsto_const_nhds (x := (3/4 : ℝ))).mul sa_tendsto).congr (fun k => ?_)
      show (3/4 : ℝ) * sa k = γ' (sa k) 2
      rw [hEq (sa_mem k)]
      show _ = (3/4 : ℝ) * sa k + dq (sa k)
      rw [dq_sa, add_zero]
    · refine (((tendsto_const_nhds (x := (3/4 : ℝ))).mul sb_tendsto).add
        (tendsto_const_nhds (x := (1 : ℝ)))).congr (fun k => ?_)
      show (3/4 : ℝ) * sb k + 1 = γ' (sb k) 2
      rw [hEq (sb_mem k)]
      show _ = (3/4 : ℝ) * sb k + dq (sb k)
      rw [dq_sb]
  rw [h1, h2, h3] at hn
  rcases h0 with h | h <;> rw [h] at hn <;> norm_num at hn

end StrongCosmicCensorship.DP7580

open StrongCosmicCensorship Set in
theorem solution : ¬ TimelikeGeodesicallyComplete (univ : Set Coords) minkowski := by
  intro h
  obtain ⟨γ', hEq, hgeo⟩ := h 1 DP7580.γ one_pos DP7580.hyp
  exact DP7580.no_ext γ' hEq hgeo
