-- Prove2me | solution 1 for Reiman84.QueueLength.weakConvD_of_fdd_and_modulus
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-18T13:10:51.95595+00:00
-- url     : https://prove2.me/submissions/92ba630d-1fa9-411c-b014-1d95534a1796

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths
import Definitions.Def_Reiman84_QueueLength_Network
import Definitions.Def_Reiman84_QueueLength_HeavyTraffic

set_option autoImplicit false

/-! Child RepThm of Reiman (1984) Proposition 5 (755ffe80), work file.
Billingsley 1999 Thm 7.5 (fdd + modulus tightness ⇒ convergence of expectations of bounded
functionals that are Lipschitz for the truncated rational-time sup distance `D1`), then the
Skorohod-type coupling of Thm 6.7. -/

namespace RepP

open Filter Topology MeasureTheory Set Reiman84.QueueLength

variable {K : ℕ}

/-- rational times in `[0,1]`. -/
noncomputable def cq (q : ℚ) : ℝ := clamp01 q

lemma clamp01_mem (t : ℝ) : clamp01 t ∈ Icc (0:ℝ) 1 :=
  ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩

lemma clamp01_of_mem {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : clamp01 t = t := by
  unfold clamp01; rw [max_eq_left ht.1, min_eq_left ht.2]

lemma cq_mem (q : ℚ) : cq q ∈ Icc (0:ℝ) 1 := clamp01_mem _

lemma onUnit_of_mem (x : ℝ → Fin K → ℝ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : onUnit x t = x t := by
  simp only [onUnit, clamp01_of_mem ht]

/-- truncated sup distance over rational times in `[0,1]`. -/
noncomputable def D1 (x y : ℝ → Fin K → ℝ) : ℝ := ⨆ q : ℚ, min 1 ‖x (cq q) - y (cq q)‖

lemma D1_bdd (x y : ℝ → Fin K → ℝ) :
    BddAbove (range fun q : ℚ => min 1 ‖x (cq q) - y (cq q)‖) :=
  ⟨1, by rintro _ ⟨q, rfl⟩; exact min_le_left _ _⟩

lemma le_D1 (x y : ℝ → Fin K → ℝ) (q : ℚ) : min 1 ‖x (cq q) - y (cq q)‖ ≤ D1 x y :=
  le_ciSup (D1_bdd x y) q

lemma D1_nonneg (x y : ℝ → Fin K → ℝ) : 0 ≤ D1 x y :=
  (le_min zero_le_one (norm_nonneg _)).trans (le_D1 x y 0)

lemma D1_le {x y : ℝ → Fin K → ℝ} {ε : ℝ} (h : ∀ q, ‖x (cq q) - y (cq q)‖ ≤ ε) : D1 x y ≤ ε :=
  ciSup_le fun q => (min_le_right _ _).trans (h q)

lemma D1_le_one (x y : ℝ → Fin K → ℝ) : D1 x y ≤ 1 := ciSup_le fun _ => min_le_left _ _

/-! ### piecewise-linear interpolation on the grid `l/m` -/

noncomputable def hat (m l : ℕ) (t : ℝ) : ℝ := max 0 (1 - |(m:ℝ) * clamp01 t - l|)

noncomputable def Hs (m : ℕ) (t : ℝ) : ℝ := ∑ l : Fin (m + 1), hat m l t

noncomputable def wt (m : ℕ) (l : Fin (m + 1)) (t : ℝ) : ℝ := hat m l t / Hs m t

noncomputable def ipol (m : ℕ) (v : Fin (m + 1) → Fin K → ℝ) : ℝ → Fin K → ℝ :=
  fun t => ∑ l, wt m l t • v l

noncomputable def grid (m : ℕ) (x : ℝ → Fin K → ℝ) : Fin (m + 1) → Fin K → ℝ :=
  fun l => x ((l : ℝ) / m)

lemma hat_nonneg (m l : ℕ) (t : ℝ) : 0 ≤ hat m l t := le_max_left _ _

lemma Hs_pos (m : ℕ) (t : ℝ) : 0 < Hs m t := by
  set s := (m:ℝ) * clamp01 t with hs
  have hs0 : 0 ≤ s := mul_nonneg (Nat.cast_nonneg m) (clamp01_mem t).1
  have hsm : s ≤ m := by
    have := mul_le_mul_of_nonneg_left (clamp01_mem t).2 (Nat.cast_nonneg m (α := ℝ))
    simpa [hs] using this
  set l := ⌊s + 1 / 2⌋₊ with hl
  have h1 : (l:ℝ) ≤ s + 1 / 2 := Nat.floor_le (by linarith)
  have h2 : s + 1 / 2 < l + 1 := Nat.lt_floor_add_one _
  have hlm : l < m + 1 := by
    have : (l:ℝ) < m + 1 := by linarith
    exact_mod_cast this
  have hhat : 1 / 2 ≤ hat m l t := by
    unfold hat
    refine le_max_of_le_right ?_
    have : |s - l| ≤ 1 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    rw [← hs]; linarith
  have hle : hat m (⟨l, hlm⟩ : Fin (m + 1)) t ≤ Hs m t :=
    Finset.single_le_sum (f := fun l : Fin (m + 1) => hat m l t)
      (fun i _ => hat_nonneg _ _ _) (Finset.mem_univ _)
  simp only at hle
  linarith

lemma wt_nonneg (m : ℕ) (l : Fin (m + 1)) (t : ℝ) : 0 ≤ wt m l t :=
  div_nonneg (hat_nonneg _ _ _) (Hs_pos m t).le

lemma wt_sum (m : ℕ) (t : ℝ) : ∑ l, wt m l t = 1 := by
  simp only [wt, ← Finset.sum_div]
  exact div_self (Hs_pos m t).ne'

lemma wt_pos_near {m : ℕ} (hm : 0 < m) {l : Fin (m + 1)} {t : ℝ} (h : 0 < wt m l t) :
    |clamp01 t - (l : ℝ) / m| < 1 / m := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hh : 0 < hat m l t := by
    by_contra hc; push_neg at hc
    have : hat m l t = 0 := le_antisymm hc (hat_nonneg _ _ _)
    simp [wt, this] at h
  unfold hat at hh
  have h1 : |(m:ℝ) * clamp01 t - l| < 1 := by
    by_contra hc; push_neg at hc
    have : max 0 (1 - |(m:ℝ) * clamp01 t - l|) = 0 := max_eq_left (by linarith)
    linarith
  have : clamp01 t - (l:ℝ) / m = ((m:ℝ) * clamp01 t - l) / m := by field_simp
  rw [this, abs_div, abs_of_pos hm', div_lt_div_iff_of_pos_right hm']
  exact h1

lemma grid_mem {m : ℕ} (l : Fin (m + 1)) : (l : ℝ) / m ∈ Icc (0:ℝ) 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have hm' : (0:ℝ) < m := by exact_mod_cast hm
    refine ⟨div_nonneg (Nat.cast_nonneg _) hm'.le, (div_le_one hm').2 ?_⟩
    exact_mod_cast Nat.lt_succ_iff.1 l.2

/-- interpolation is 1-Lipschitz from grid values to rational-time values. -/
lemma ipol_sub_le (m : ℕ) (v v' : Fin (m + 1) → Fin K → ℝ) (t : ℝ) :
    ‖ipol m v t - ipol m v' t‖ ≤ ‖v - v'‖ := by
  have : ipol m v t - ipol m v' t = ∑ l, wt m l t • (v l - v' l) := by
    simp only [ipol, smul_sub, Finset.sum_sub_distrib]
  rw [this]
  calc ‖∑ l, wt m l t • (v l - v' l)‖ ≤ ∑ l, ‖wt m l t • (v l - v' l)‖ := norm_sum_le _ _
    _ ≤ ∑ l, wt m l t * ‖v - v'‖ := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (wt_nonneg _ _ _)]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (v - v') l) (wt_nonneg _ _ _)
    _ = ‖v - v'‖ := by rw [← Finset.sum_mul, wt_sum, one_mul]

/-- a path is uniformly close to its interpolation when its modulus at scale `1/m` is small. -/
lemma sub_ipol_le {m : ℕ} (hm : 0 < m) (x : ℝ → Fin K → ℝ) {t ε : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (hε : 0 ≤ ε)
    (h : ∀ s ∈ Icc (0:ℝ) 1, |t - s| < 1 / m → ‖x t - x s‖ ≤ ε) :
    ‖x t - ipol m (grid m x) t‖ ≤ ε := by
  have hx : x t = ∑ l, wt m l t • x t := by rw [← Finset.sum_smul, wt_sum, one_smul]
  have : x t - ipol m (grid m x) t = ∑ l, wt m l t • (x t - x ((l : ℝ) / m)) := by
    conv_lhs => rw [hx]
    simp only [ipol, grid, smul_sub, Finset.sum_sub_distrib]
  rw [this]
  calc ‖∑ l, wt m l t • (x t - x ((l : ℝ) / m))‖
        ≤ ∑ l, ‖wt m l t • (x t - x ((l : ℝ) / m))‖ := norm_sum_le _ _
    _ ≤ ∑ l, wt m l t * ε := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (wt_nonneg _ _ _)]
        rcases (wt_nonneg m l t).eq_or_lt with h0 | hpos
        · rw [← h0]; simp
        · refine mul_le_mul_of_nonneg_left (h _ (grid_mem l) ?_) (wt_nonneg _ _ _)
          have := wt_pos_near hm hpos
          rwa [clamp01_of_mem ht] at this
    _ = ε := by rw [← Finset.sum_mul, wt_sum, one_mul]

lemma meas_ipol_grid (m : ℕ) : Measurable fun x : ℝ → Fin K → ℝ => ipol m (grid m x) := by
  refine measurable_pi_lambda _ fun t => ?_
  simp only [ipol, grid]
  exact Finset.measurable_sum _ fun l _ =>
    (measurable_pi_apply ((l : ℝ) / m)).const_smul (wt m l t)

lemma grid_onUnit (m : ℕ) (x : ℝ → Fin K → ℝ) : grid m (onUnit x) = grid m x := by
  funext l; simp only [grid, onUnit_of_mem x (grid_mem l)]

/-! ### fdd convergence + modulus tightness ⇒ convergence of `D1`-Lipschitz expectations -/

/-- Finite-dimensional convergence on `[0,1]` (copy of the parent's `P5.FddConv`). -/
def FddConv {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    (X : ∀ n, Ω n → ℝ → Fin K → ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    (X' : Ω' → ℝ → Fin K → ℝ) : Prop :=
  ∀ (m : ℕ) (τ : Fin m → ℝ), (∀ i, τ i ∈ Set.Icc (0:ℝ) 1) →
    ∀ (f : (Fin m → Fin K → ℝ) → ℝ), (∃ C : ℝ, ∀ x, |f x| ≤ C) →
      (∃ L : NNReal, LipschitzWith L f) →
      Tendsto (fun n => ∫ ω, f (fun i => X n ω (τ i)) ∂(P n)) atTop
        (𝓝 (∫ ω, f (fun i => X' ω (τ i)) ∂P'))

/-- Modulus-of-continuity tightness on `[0,1]` (copy of `P5.ModTight`). -/
def ModTight {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    (X : ∀ n, Ω n → ℝ → Fin K → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n, N ≤ n →
    P n {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ δ ∧
      ε ≤ ‖X n ω s - X n ω t‖} ≤ ENNReal.ofReal η

section Conv

variable {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)}
  {X : ∀ n, Ω n → ℝ → Fin K → ℝ} {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
  {X' : Ω' → ℝ → Fin K → ℝ}

lemma int_bdd {α : Type} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {g : α → ℝ}
    (hg : AEStronglyMeasurable g μ) {C : ℝ} (hC : ∀ a, |g a| ≤ C) : Integrable g μ :=
  (integrable_const C).mono' hg (Eventually.of_forall fun a => by
    rw [Real.norm_eq_abs]; exact hC a)

/-- the ModTight approximation step: `F(x) ≈ F(ipol (grid x))` in expectation. -/
lemma approx (hP : ∀ n, IsProbabilityMeasure (P n))
    (hXm : ∀ n, AEMeasurable (fun ω => onUnit (X n ω)) (P n)) (hT : ModTight P X)
    {F : (ℝ → Fin K → ℝ) → ℝ} (hFm : Measurable F) {C L : ℝ} (hFb : ∀ x, |F x| ≤ C)
    (hL : 0 ≤ L) (hFL : ∀ x y, |F x - F y| ≤ L * D1 x y) {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m, m₀ ≤ m → ∃ N : ℕ, ∀ n, N ≤ n →
      |∫ ω, F (onUnit (X n ω)) ∂(P n) - ∫ ω, F (ipol m (grid m (X n ω))) ∂(P n)| ≤ ε := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hFb 0)
  set ε₁ := ε / (2 * (L + 1)) with hε₁d
  have hε₁ : 0 < ε₁ := div_pos hε (by linarith)
  have hε₁e : ε₁ * (2 * (L + 1)) = ε := div_mul_cancel₀ ε (by linarith)
  set η := ε / (2 * (2 * C + 1)) with hηd
  have hη : 0 < η := div_pos hε (by linarith)
  have hηe : η * (2 * (2 * C + 1)) = ε := div_mul_cancel₀ ε (by linarith)
  obtain ⟨δ, hδ, N, hN⟩ := hT ε₁ hε₁ η hη
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
  refine ⟨k + 1, Nat.succ_pos k, fun m hm => ⟨N, fun n hn => ?_⟩⟩
  have hm0 : 0 < m := lt_of_lt_of_le (Nat.succ_pos k) hm
  have hm' : (1:ℝ) / m < δ := by
    have : (1:ℝ) / m ≤ 1 / (k + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast hm
    linarith
  have := hP n
  have hA : AEStronglyMeasurable (fun ω => F (onUnit (X n ω))) (P n) :=
    (hFm.comp_aemeasurable (hXm n)).aestronglyMeasurable
  have hB : AEStronglyMeasurable (fun ω => F (ipol m (grid m (X n ω)))) (P n) := by
    have := ((hFm.comp (meas_ipol_grid m)).comp_aemeasurable (hXm n)).aestronglyMeasurable
    simpa only [Function.comp_def, grid_onUnit] using this
  set S := {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ δ ∧
      ε₁ ≤ ‖X n ω s - X n ω t‖} with hSd
  set T := toMeasurable (P n) S
  have hpt : ∀ ω, |F (onUnit (X n ω)) - F (ipol m (grid m (X n ω)))| ≤
      L * ε₁ + 2 * C * T.indicator 1 ω := by
    intro ω
    by_cases hω : ω ∈ T
    · rw [indicator_of_mem hω, Pi.one_apply, mul_one]
      have := abs_sub (F (onUnit (X n ω))) (F (ipol m (grid m (X n ω))))
      linarith [hFb (onUnit (X n ω)), hFb (ipol m (grid m (X n ω))), mul_nonneg hL hε₁.le]
    · rw [indicator_of_notMem hω, mul_zero, add_zero]
      have hS : ω ∉ S := fun h => hω (subset_toMeasurable _ _ h)
      have hgood : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, |s - t| ≤ δ →
          ‖X n ω s - X n ω t‖ < ε₁ := by
        intro s hs t ht hst
        by_contra hc; push_neg at hc
        exact hS ⟨s, hs, t, ht, hst, hc⟩
      have hD : D1 (onUnit (X n ω)) (ipol m (grid m (X n ω))) ≤ ε₁ := by
        refine D1_le fun q => ?_
        rw [onUnit_of_mem _ (cq_mem q)]
        exact sub_ipol_le hm0 _ (cq_mem q) hε₁.le fun s hs hts =>
          (hgood _ (cq_mem q) s hs (by linarith)).le
      exact (hFL _ _).trans (mul_le_mul_of_nonneg_left hD hL)
  have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
  have h2 : Integrable (fun ω => 2 * C * T.indicator 1 ω) (P n) :=
    ((integrable_const (1:ℝ)).indicator hTm).const_mul (2 * C)
  have hint1 : Integrable (fun ω => L * ε₁ + 2 * C * T.indicator 1 ω) (P n) :=
    (integrable_const _).add h2
  have hTle : (P n).real T ≤ η := by
    rw [measureReal_def, measure_toMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hη.le (hN n hn)
  rw [← integral_sub (int_bdd hA fun ω => hFb _) (int_bdd hB fun ω => hFb _)]
  calc |∫ ω, F (onUnit (X n ω)) - F (ipol m (grid m (X n ω))) ∂(P n)|
      ≤ ∫ ω, |F (onUnit (X n ω)) - F (ipol m (grid m (X n ω)))| ∂(P n) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ ω, (L * ε₁ + 2 * C * T.indicator 1 ω) ∂(P n) :=
        integral_mono_of_nonneg (Eventually.of_forall fun ω => abs_nonneg _) hint1
          (Eventually.of_forall hpt)
    _ = L * ε₁ + 2 * C * (P n).real T := by
        rw [integral_add (integrable_const _) h2,
          integral_const, integral_const_mul, integral_indicator_one hTm]
        simp
    _ ≤ ε := by
        have := mul_le_mul_of_nonneg_left hTle (by linarith : (0:ℝ) ≤ 2 * C)
        nlinarith

/-- Billingsley 1999 Thm 7.5, expectation form, for `D1`-Lipschitz bounded functionals. -/
theorem conv (hP : ∀ n, IsProbabilityMeasure (P n)) (hP' : IsProbabilityMeasure P')
    (hXm : ∀ n, AEMeasurable (fun ω => onUnit (X n ω)) (P n))
    (hX'm : ∀ t, Measurable fun ω => X' ω t) (hc : ∀ ω, ContinuousOn (X' ω) (Icc 0 1))
    (hF : FddConv P X P' X') (hT : ModTight P X)
    {F : (ℝ → Fin K → ℝ) → ℝ} (hFm : Measurable F) {C L : ℝ} (hFb : ∀ x, |F x| ≤ C)
    (hL : 0 ≤ L) (hFL : ∀ x y, |F x - F y| ≤ L * D1 x y) :
    Tendsto (fun n => ∫ ω, F (onUnit (X n ω)) ∂(P n)) atTop
      (𝓝 (∫ ω, F (onUnit (X' ω)) ∂P')) := by
  have hX'u : Measurable fun ω => onUnit (X' ω) :=
    measurable_pi_lambda _ fun t => hX'm (clamp01 t)
  -- (i) fdd step at a fixed grid
  have h1 : ∀ m, Tendsto (fun n => ∫ ω, F (ipol m (grid m (X n ω))) ∂(P n)) atTop
      (𝓝 (∫ ω, F (ipol m (grid m (X' ω))) ∂P')) := by
    intro m
    refine hF (m + 1) (fun l => (l : ℝ) / m) (fun l => grid_mem l) (fun v => F (ipol m v))
      ⟨C, fun v => hFb _⟩ ⟨Real.toNNReal L, LipschitzWith.of_dist_le_mul fun v v' => ?_⟩
    rw [Real.dist_eq, Real.coe_toNNReal L hL, dist_eq_norm]
    exact (hFL _ _).trans (mul_le_mul_of_nonneg_left (D1_le fun q => ipol_sub_le m v v' _) hL)
  -- (ii) the limit is continuous, so the interpolation converges
  have h2 : Tendsto (fun m => ∫ ω, F (ipol m (grid m (X' ω))) ∂P') atTop
      (𝓝 (∫ ω, F (onUnit (X' ω)) ∂P')) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => C) (fun m => ?_)
      (integrable_const C) (fun m => Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]; exact hFb _) (Eventually.of_forall fun ω => ?_)
    · have := ((hFm.comp (meas_ipol_grid m)).comp hX'u).aestronglyMeasurable (μ := P')
      simpa only [Function.comp_def, grid_onUnit] using this
    · have huc := Metric.uniformContinuousOn_iff.1
        (isCompact_Icc.uniformContinuousOn_of_continuous (hc ω))
      refine Metric.tendsto_atTop.2 fun ε hε => ?_
      have hε₁ : 0 < ε / (2 * (L + 1)) := div_pos hε (by linarith)
      have hε₁e : ε / (2 * (L + 1)) * (2 * (L + 1)) = ε := div_mul_cancel₀ ε (by linarith)
      obtain ⟨δ, hδ, hδ'⟩ := huc _ hε₁
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
      refine ⟨k + 1, fun m hm => ?_⟩
      have hm0 : 0 < m := lt_of_lt_of_le (Nat.succ_pos k) hm
      have hm' : (1:ℝ) / m < δ := by
        have : (1:ℝ) / m ≤ 1 / (k + 1) := by
          apply one_div_le_one_div_of_le (by positivity)
          exact_mod_cast hm
        linarith
      have hD : D1 (ipol m (grid m (X' ω))) (onUnit (X' ω)) ≤ ε / (2 * (L + 1)) := by
        refine D1_le fun q => ?_
        rw [onUnit_of_mem _ (cq_mem q), norm_sub_rev]
        refine sub_ipol_le hm0 _ (cq_mem q) hε₁.le fun s hs hts => ?_
        have := hδ' _ (cq_mem q) s hs (by rw [Real.dist_eq]; linarith)
        rw [dist_eq_norm] at this
        exact this.le
      rw [Real.dist_eq]
      have := (hFL (ipol m (grid m (X' ω))) (onUnit (X' ω))).trans
        (mul_le_mul_of_nonneg_left hD hL)
      nlinarith
  -- (iii) combine
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  obtain ⟨m₀, hm₀, h3⟩ := approx hP hXm hT hFm hFb hL hFL (show 0 < ε / 3 by linarith)
  obtain ⟨m₁, hm₁⟩ := Metric.tendsto_atTop.1 h2 (ε / 3) (by linarith)
  obtain ⟨N₁, hN₁⟩ := h3 (max m₀ m₁) (le_max_left _ _)
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 (h1 (max m₀ m₁)) (ε / 3) (by linarith)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have e1 := hN₁ n (le_of_max_le_left hn)
  have e2 := hN₂ n (le_of_max_le_right hn)
  have e3 := hm₁ (max m₀ m₁) (le_max_right _ _)
  rw [Real.dist_eq] at e2 e3 ⊢
  have := abs_sub_le (∫ ω, F (onUnit (X n ω)) ∂(P n))
    (∫ ω, F (ipol (max m₀ m₁) (grid (max m₀ m₁) (X n ω))) ∂(P n))
    (∫ ω, F (ipol (max m₀ m₁) (grid (max m₀ m₁) (X' ω))) ∂P')
  have := abs_sub_le (∫ ω, F (onUnit (X n ω)) ∂(P n))
    (∫ ω, F (ipol (max m₀ m₁) (grid (max m₀ m₁) (X' ω))) ∂P') (∫ ω, F (onUnit (X' ω)) ∂P')
  linarith

end Conv

/-! ### metric facts for `D1` and the Portmanteau lower bound -/

lemma min_one_le {a b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ b + c) :
    min 1 a ≤ min 1 b + min 1 c := by
  rcases le_total b 1 with hb1 | hb1 <;> rcases le_total c 1 with hc1 | hc1
  · rw [min_eq_right hb1, min_eq_right hc1]; exact (min_le_right _ _).trans h
  · rw [min_eq_left hc1]; linarith [min_le_left 1 a, le_min (zero_le_one' ℝ) hb]
  · rw [min_eq_left hb1]; linarith [min_le_left 1 a, le_min (zero_le_one' ℝ) hc]
  · rw [min_eq_left hb1, min_eq_left hc1]; linarith [min_le_left 1 a]

lemma D1_comm (x y : ℝ → Fin K → ℝ) : D1 x y = D1 y x := by
  simp only [D1, norm_sub_rev]

lemma D1_triangle (x y z : ℝ → Fin K → ℝ) : D1 x z ≤ D1 x y + D1 y z :=
  ciSup_le fun q => (min_one_le (norm_nonneg _) (norm_nonneg _)
    (norm_sub_le_norm_sub_add_norm_sub _ _ _)).trans (add_le_add (le_D1 x y q) (le_D1 y z q))

lemma D1_lip (x y z : ℝ → Fin K → ℝ) : |D1 x z - D1 y z| ≤ D1 x y := by
  rw [abs_sub_le_iff]
  constructor
  · linarith [D1_triangle x y z]
  · linarith [D1_triangle y x z, D1_comm x y]

lemma D1_meas (z : ℝ → Fin K → ℝ) : Measurable fun x : ℝ → Fin K → ℝ => D1 x z :=
  Measurable.iSup fun q =>
    measurable_const.min (((measurable_pi_apply (cq q)).sub measurable_const).norm)

section Port

variable {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)}
  {X : ∀ n, Ω n → ℝ → Fin K → ℝ} {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
  {X' : Ω' → ℝ → Fin K → ℝ}

/-- Portmanteau lower bound for the `D1`-open set `{g > 0}`, `g` 1-Lipschitz for `D1`. -/
theorem port (hP : ∀ n, IsProbabilityMeasure (P n)) (hP' : IsProbabilityMeasure P')
    (hXm : ∀ n, AEMeasurable (fun ω => onUnit (X n ω)) (P n))
    (hX'm : ∀ t, Measurable fun ω => X' ω t) (hc : ∀ ω, ContinuousOn (X' ω) (Icc 0 1))
    (hF : FddConv P X P' X') (hT : ModTight P X)
    {g : (ℝ → Fin K → ℝ) → ℝ} (hgm : Measurable g) (hgL : ∀ x y, |g x - g y| ≤ D1 x y)
    {c : ℝ} (hcμ : c < (P'.map (fun ω => onUnit (X' ω))).real {x | 0 < g x}) :
    ∀ᶠ n in atTop, c < ((P n).map (fun ω => onUnit (X n ω))).real {x | 0 < g x} := by
  have hX'u : Measurable fun ω => onUnit (X' ω) :=
    measurable_pi_lambda _ fun t => hX'm (clamp01 t)
  set G := {x : ℝ → Fin K → ℝ | 0 < g x} with hGd
  have hGm : MeasurableSet G := measurableSet_lt measurable_const hgm
  set f : ℕ → (ℝ → Fin K → ℝ) → ℝ := fun k x => min 1 ((k:ℝ) * max 0 (g x)) with hfd
  have hf_nonneg : ∀ k x, 0 ≤ f k x := fun k x =>
    le_min zero_le_one (mul_nonneg (Nat.cast_nonneg k) (le_max_left _ _))
  have hf_le1 : ∀ k x, f k x ≤ 1 := fun k x => min_le_left _ _
  have hf_le : ∀ k x, f k x ≤ G.indicator 1 x := by
    intro k x
    by_cases hx : x ∈ G
    · rw [indicator_of_mem hx]; exact min_le_left _ _
    · rw [indicator_of_notMem hx]
      have : g x ≤ 0 := not_lt.1 hx
      simp [f, max_eq_left this]
  have hfm : ∀ k, Measurable (f k) := fun k =>
    measurable_const.min (measurable_const.mul (measurable_const.max hgm))
  have hfL : ∀ k x y, |f k x - f k y| ≤ k * D1 x y := by
    intro k x y
    calc |f k x - f k y| ≤ |(k:ℝ) * max 0 (g x) - k * max 0 (g y)| := by
          have := abs_min_sub_min_le_max 1 ((k:ℝ) * max 0 (g x)) 1 ((k:ℝ) * max 0 (g y))
          simpa using this
      _ = k * |max 0 (g x) - max 0 (g y)| := by
          rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) k)]
      _ ≤ k * D1 x y := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg k)
          have := abs_max_sub_max_le_max 0 (g x) 0 (g y)
          simp only [sub_self, abs_zero] at this
          exact (this.trans (max_le (abs_nonneg _) le_rfl)).trans (hgL x y)
  set μ' := P'.map (fun ω => onUnit (X' ω)) with hμ'd
  have : IsProbabilityMeasure μ' := Measure.isProbabilityMeasure_map hX'u.aemeasurable
  have hlim : Tendsto (fun k => ∫ x, f k x ∂μ') atTop (𝓝 (μ'.real G)) := by
    rw [← integral_indicator_one hGm]
    refine tendsto_integral_of_dominated_convergence (fun _ => 1)
      (fun k => (hfm k).aestronglyMeasurable) (integrable_const 1)
      (fun k => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (hf_nonneg k x)]; exact hf_le1 k x
    · by_cases hx : x ∈ G
      · rw [indicator_of_mem hx, Pi.one_apply]
        have hgx : 0 < g x := hx
        refine tendsto_const_nhds.congr' ?_
        obtain ⟨k₀, hk₀⟩ := exists_nat_gt (1 / g x)
        filter_upwards [eventually_ge_atTop k₀] with k hk
        have h1 : 1 ≤ (k:ℝ) * max 0 (g x) := by
          rw [max_eq_right hgx.le]
          have : (1 / g x) < k := lt_of_lt_of_le hk₀ (by exact_mod_cast hk)
          rw [div_lt_iff₀ hgx] at this; linarith
        simp only [f, min_eq_left h1]
      · rw [indicator_of_notMem hx]
        have : g x ≤ 0 := not_lt.1 hx
        exact tendsto_const_nhds.congr'
          (Eventually.of_forall fun k => by simp [f, max_eq_left this])
  obtain ⟨k, hk⟩ := (hlim.eventually (lt_mem_nhds hcμ)).exists
  have hconv := conv hP hP' hXm hX'm hc hF hT (hfm k)
    (fun x => by rw [abs_of_nonneg (hf_nonneg k x)]; exact hf_le1 k x)
    (Nat.cast_nonneg k) (hfL k)
  have hk' : c < ∫ ω, f k (onUnit (X' ω)) ∂P' := by
    rwa [← integral_map hX'u.aemeasurable (hfm k).aestronglyMeasurable]
  filter_upwards [hconv.eventually (lt_mem_nhds hk')] with n hn
  have := hP n
  have : IsProbabilityMeasure ((P n).map fun ω => onUnit (X n ω)) :=
    Measure.isProbabilityMeasure_map (hXm n)
  rw [← integral_map (hXm n) (hfm k).aestronglyMeasurable] at hn
  have h2 : ∫ x, f k x ∂((P n).map fun ω => onUnit (X n ω)) ≤
      ((P n).map fun ω => onUnit (X n ω)).real G := by
    rw [← integral_indicator_one hGm]
    exact integral_mono (int_bdd (hfm k).aestronglyMeasurable
      (fun x => by rw [abs_of_nonneg (hf_nonneg k x)]; exact hf_le1 k x))
      ((integrable_const (1:ℝ)).indicator hGm) (hf_le k)
  linarith

end Port

/-! ### centres, radii and cells -/

/-- countable family of interpolation centres (rational grid values). -/
abbrev Ctr (K : ℕ) := Σ m : ℕ, (Fin (m + 1) → Fin K → ℚ)

noncomputable def ctr (c : Ctr K) : ℝ → Fin K → ℝ := ipol c.1 (fun l k => (c.2 l k : ℝ))

lemma ipol_close {x : ℝ → Fin K → ℝ} (hx : ContinuousOn x (Icc 0 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧ D1 (onUnit x) (ipol m (grid m x)) ≤ ε := by
  have huc := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hx)
  obtain ⟨δ, hδ, hδ'⟩ := huc ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
  refine ⟨k + 1, Nat.succ_pos k, D1_le fun q => ?_⟩
  rw [onUnit_of_mem _ (cq_mem q)]
  refine sub_ipol_le (Nat.succ_pos k) _ (cq_mem q) hε.le fun s hs hts => ?_
  have h1 : (1:ℝ) / ((k + 1 : ℕ) : ℝ) = 1 / ((k:ℝ) + 1) := by push_cast; ring
  rw [h1] at hts
  have := hδ' _ (cq_mem q) s hs (by rw [Real.dist_eq]; linarith)
  rw [dist_eq_norm] at this
  exact this.le

lemma ctr_dense {x : ℝ → Fin K → ℝ} (hx : ContinuousOn x (Icc 0 1)) {r : ℝ} (hr : 0 < r) :
    ∃ c : Ctr K, D1 (onUnit x) (ctr c) < r := by
  obtain ⟨m, _, hD⟩ := ipol_close hx (show 0 < r / 2 by linarith)
  have : ∀ l : Fin (m + 1), ∀ k : Fin K, ∃ q : ℚ, |grid m x l k - q| < r / 2 := fun l k => by
    obtain ⟨q, hq1, hq2⟩ :=
      exists_rat_btwn (show grid m x l k - r / 4 < grid m x l k + r / 4 by linarith)
    exact ⟨q, abs_lt.2 ⟨by linarith, by linarith⟩⟩
  choose v hv using this
  refine ⟨⟨m, v⟩, ?_⟩
  have h2 : D1 (ipol m (grid m x)) (ctr ⟨m, v⟩) < r / 2 := by
    have hn : ‖grid m x - fun l k => ((v l k : ℚ) : ℝ)‖ < r / 2 := by
      refine (pi_norm_lt_iff (by linarith)).2 fun l => (pi_norm_lt_iff (by linarith)).2 fun k => ?_
      simpa [Real.norm_eq_abs] using hv l k
    exact lt_of_le_of_lt (D1_le fun q => ipol_sub_le m _ _ _) hn
  linarith [D1_triangle (onUnit x) (ipol m (grid m x)) (ctr ⟨m, v⟩)]

/-- a radius in `(a, b)` whose spheres around all centres are null. -/
lemma exists_radius (μ : Measure (ℝ → Fin K → ℝ)) [IsFiniteMeasure μ] (z : ℕ → ℝ → Fin K → ℝ)
    {a b : ℝ} (hab : a < b) : ∃ r, a < r ∧ r < b ∧ ∀ i, μ {x | D1 x (z i) = r} = 0 := by
  set S := ⋃ i, {t : ℝ | 0 < μ {x | D1 x (z i) = t}}
  have hS : S.Countable := Set.countable_iUnion fun i =>
    Measure.countable_meas_level_set_pos (D1_meas (z i))
  by_contra hcon
  push_neg at hcon
  have hsub : Ioo a b ⊆ S := by
    intro r hr
    obtain ⟨i, hi⟩ := hcon r hr.1 hr.2
    exact mem_iUnion.2 ⟨i, pos_iff_ne_zero.2 hi⟩
  have := Cardinal.Real.Ioo_countable_iff.1 (hS.mono hsub)
  linarith

section Cells

variable (z : ℕ → ℝ → Fin K → ℝ) (r : ℝ) (I : ℕ)

/-- the cell label: the first centre within `r`, or `I` (remainder). -/
noncomputable def lab (x : ℝ → Fin K → ℝ) : ℕ := by
  classical
  exact Nat.find (⟨I, Or.inl rfl⟩ : ∃ i, i = I ∨ D1 x (z i) < r)

lemma lab_spec (x : ℝ → Fin K → ℝ) (i : ℕ) :
    lab z r I x = i ↔ (i = I ∨ D1 x (z i) < r) ∧ ∀ i' < i, ¬ (i' = I ∨ D1 x (z i') < r) := by
  classical
  unfold lab
  exact Nat.find_eq_iff _

lemma lab_le (x : ℝ → Fin K → ℝ) : lab z r I x ≤ I := by
  classical
  unfold lab
  exact Nat.find_min' _ (Or.inl rfl)

lemma lab_meas : Measurable (lab z r I) := by
  refine measurable_to_countable' fun i => ?_
  have : lab z r I ⁻¹' {i} = {x | (i = I ∨ D1 x (z i) < r) ∧
      ∀ i' : ℕ, i' < i → ¬ (i' = I ∨ D1 x (z i') < r)} := by
    ext x; exact lab_spec z r I x i
  rw [this]
  have hlt : ∀ i', Measurable fun x : ℝ → Fin K → ℝ => D1 x (z i') < r := fun i' =>
    measurableSet_setOfPred.1 (measurableSet_lt (D1_meas (z i')) measurable_const)
  exact measurableSet_setOfPred.2 ((measurable_const.or (hlt i)).and
    (Measurable.forall fun i' => measurable_const.imp ((measurable_const.or (hlt i')).not)))

/-- two paths with the same label `< I` are `2r`-close in `D1`. -/
lemma lab_close {x y : ℝ → Fin K → ℝ} (hxy : lab z r I x = lab z r I y)
    (hI : lab z r I x < I) : D1 x y < 2 * r := by
  have hx := ((lab_spec z r I x _).1 rfl).1
  have hy := ((lab_spec z r I y _).1 rfl).1
  rw [← hxy] at hy
  have hx' : D1 x (z (lab z r I x)) < r := hx.resolve_left (ne_of_lt hI)
  have hy' : D1 y (z (lab z r I x)) < r := hy.resolve_left (ne_of_lt hI)
  linarith [D1_triangle x (z (lab z r I x)) y, D1_comm y (z (lab z r I x))]

end Cells

/-! ### open cells (for the Portmanteau bound) and the per-level choice -/

section Open

variable (z : ℕ → ℝ → Fin K → ℝ) (r : ℝ)

noncomputable def hmin : ℕ → (ℝ → Fin K → ℝ) → ℝ
  | 0 => fun _ => 1
  | i + 1 => fun x => min (hmin i x) (D1 x (z i) - r)

noncomputable def cellf (i : ℕ) (x : ℝ → Fin K → ℝ) : ℝ := min (r - D1 x (z i)) (hmin z r i x)

lemma hmin_pos (i : ℕ) (x : ℝ → Fin K → ℝ) : 0 < hmin z r i x ↔ ∀ i' < i, r < D1 x (z i') := by
  induction i with
  | zero => simp [hmin]
  | succ i ih =>
    simp only [hmin, lt_min_iff, ih, sub_pos]
    constructor
    · rintro ⟨h1, h2⟩ i' hi'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with h | rfl
      · exact h1 i' h
      · exact h2
    · intro h; exact ⟨fun i' hi' => h i' (Nat.lt_succ_of_lt hi'), h i (Nat.lt_succ_self i)⟩

lemma hmin_lip (i : ℕ) (x y : ℝ → Fin K → ℝ) : |hmin z r i x - hmin z r i y| ≤ D1 x y := by
  induction i with
  | zero => simp [hmin, D1_nonneg]
  | succ i ih =>
    simp only [hmin]
    refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le ih ?_)
    have := D1_lip x y (z i)
    rwa [show D1 x (z i) - r - (D1 y (z i) - r) = D1 x (z i) - D1 y (z i) by ring]

lemma hmin_meas (i : ℕ) : Measurable (hmin z r i) := by
  induction i with
  | zero => exact measurable_const
  | succ i ih => exact ih.min ((D1_meas (z i)).sub measurable_const)

lemma cellf_lip (i : ℕ) (x y : ℝ → Fin K → ℝ) : |cellf z r i x - cellf z r i y| ≤ D1 x y := by
  unfold cellf
  refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ (hmin_lip z r i x y))
  have := D1_lip x y (z i)
  rw [show r - D1 x (z i) - (r - D1 y (z i)) = -(D1 x (z i) - D1 y (z i)) by ring, abs_neg]
  exact this

lemma cellf_meas (i : ℕ) : Measurable (cellf z r i) :=
  (measurable_const.sub (D1_meas (z i))).min (hmin_meas z r i)

lemma cellf_sub_lab {i I : ℕ} (hi : i < I) {x : ℝ → Fin K → ℝ} (hx : 0 < cellf z r i x) :
    lab z r I x = i := by
  unfold cellf at hx
  rw [lt_min_iff, sub_pos, hmin_pos] at hx
  refine (lab_spec z r I x i).2 ⟨Or.inr hx.1, fun i' hi' h => ?_⟩
  rcases h with h | h
  · omega
  · exact absurd h (not_lt.2 (hx.2 i' hi').le)

lemma lab_sub_cellf {i I : ℕ} (hi : i < I) {x : ℝ → Fin K → ℝ} (hx : lab z r I x = i) :
    0 < cellf z r i x ∨ ∃ i' < i, D1 x (z i') = r := by
  have h := (lab_spec z r I x i).1 hx
  have h1 : D1 x (z i) < r := h.1.resolve_left (ne_of_lt hi)
  by_cases hall : ∀ i' < i, r < D1 x (z i')
  · left
    unfold cellf
    exact lt_min (sub_pos.2 h1) ((hmin_pos z r i x).2 hall)
  · right
    push_neg at hall
    obtain ⟨i', hi', hle⟩ := hall
    have : ¬ D1 x (z i') < r := fun hc => h.2 i' hi' (Or.inr hc)
    exact ⟨i', hi', le_antisymm hle (not_lt.1 this)⟩

lemma lab_eq_I_iff {I : ℕ} (x : ℝ → Fin K → ℝ) : lab z r I x = I ↔ ∀ i < I, r ≤ D1 x (z i) := by
  rw [lab_spec]
  constructor
  · rintro ⟨_, h⟩ i hi
    exact not_lt.1 fun hc => h i hi (Or.inr hc)
  · intro h
    exact ⟨Or.inl rfl, fun i hi hc => hc.elim (fun h' => (ne_of_lt hi) h')
      (fun h' => absurd h' (not_lt.2 (h i hi)))⟩

end Open

/-- one level of the construction: a radius in `(ρ/2, ρ)`, a number `I` of cells whose
remainder has small limit mass, and eventually `μₙ(cell i) ≥ (1-ε) μ(cell i)`. -/
lemma level (μ' : Measure (ℝ → Fin K → ℝ)) [IsProbabilityMeasure μ']
    (μn : ℕ → Measure (ℝ → Fin K → ℝ)) [∀ n, IsProbabilityMeasure (μn n)]
    (hport : ∀ g : (ℝ → Fin K → ℝ) → ℝ, Measurable g → (∀ x y, |g x - g y| ≤ D1 x y) →
      ∀ c, c < μ'.real {x | 0 < g x} → ∀ᶠ n in atTop, c < (μn n).real {x | 0 < g x})
    (z : ℕ → ℝ → Fin K → ℝ) (hz : ∀ᵐ x ∂μ', ∀ r > 0, ∃ i, D1 x (z i) < r)
    {ε ρ τ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) (hτ : 0 < τ) :
    ∃ r, ρ / 2 < r ∧ r < ρ ∧ ∃ I : ℕ, μ'.real {x | lab z r I x = I} ≤ τ ∧
      ∀ᶠ n in atTop, ∀ i < I,
        (1 - ε) * μ'.real {x | lab z r I x = i} ≤ (μn n).real {x | lab z r I x = i} := by
  obtain ⟨r, hr1, hr2, hnull⟩ := exists_radius μ' z (show ρ / 2 < ρ by linarith)
  have hr0 : 0 < r := by linarith
  -- remainder masses decrease to zero
  set R : ℕ → Set (ℝ → Fin K → ℝ) := fun I => {x | ∀ i < I, r ≤ D1 x (z i)} with hRd
  have hRanti : Antitone R := fun I J hIJ x hx i hi => hx i (lt_of_lt_of_le hi hIJ)
  have hRm : ∀ I, MeasurableSet (R I) := fun I => by
    have : R I = ⋂ i ∈ Finset.range I, {x | r ≤ D1 x (z i)} := by
      ext x; simp [hRd]
    rw [this]
    exact Finset.measurableSet_biInter _ fun i _ => measurableSet_le measurable_const (D1_meas _)
  have hRinf : μ' (⋂ I, R I) = 0 := by
    refine measure_mono_null (t := {x | ¬ ∀ r > 0, ∃ i, D1 x (z i) < r}) (fun x hx h => ?_)
      (measure_eq_zero_iff_ae_notMem.2 ?_)
    · obtain ⟨i, hi⟩ := h r hr0
      exact absurd (mem_iInter.1 hx (i + 1) i (Nat.lt_succ_self i)) (not_le.2 hi)
    · filter_upwards [hz] with x hx h using h hx
  have htend := tendsto_measure_iInter_atTop (μ := μ') (fun I => (hRm I).nullMeasurableSet)
    hRanti ⟨0, measure_ne_top _ _⟩
  rw [hRinf] at htend
  obtain ⟨I, hI⟩ := (htend.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hτ))).exists
  refine ⟨r, hr1, hr2, I, ?_, ?_⟩
  · have : {x | lab z r I x = I} = R I := by ext x; exact lab_eq_I_iff z r x
    rw [this, measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal hτ.le hI.le
  · have key : ∀ i ∈ {i : ℕ | i < I}, ∀ᶠ n in atTop,
        (1 - ε) * μ'.real {x | lab z r I x = i} ≤ (μn n).real {x | lab z r I x = i} := by
      intro i hi
      have hμeq : μ'.real {x | lab z r I x = i} ≤ μ'.real {x | 0 < cellf z r i x} := by
        have hsub : {x | lab z r I x = i} ⊆
            {x | 0 < cellf z r i x} ∪ ⋃ i' ∈ Finset.range i, {x | D1 x (z i') = r} := by
          intro x hx
          rcases lab_sub_cellf z r hi hx with h | ⟨i', hi', h⟩
          · exact Or.inl h
          · exact Or.inr (mem_biUnion (Finset.mem_range.2 hi') h)
        have h0 : μ' (⋃ i' ∈ Finset.range i, {x | D1 x (z i') = r}) = 0 :=
          (measure_biUnion_null_iff (Finset.range i).countable_toSet).2 fun i' _ => hnull i'
        rw [measureReal_def, measureReal_def]
        refine ENNReal.toReal_mono (measure_ne_top _ _) ?_
        exact (measure_mono hsub).trans ((measure_union_le _ _).trans (by rw [h0, add_zero]))
      rcases (measureReal_nonneg (μ := μ') (s := {x | lab z r I x = i})).eq_or_lt with h0 | hpos
      · exact Eventually.of_forall fun n => by rw [← h0, mul_zero]; exact measureReal_nonneg
      · have hc : (1 - ε) * μ'.real {x | lab z r I x = i} < μ'.real {x | 0 < cellf z r i x} := by
          nlinarith
        filter_upwards [hport _ (cellf_meas z r i) (cellf_lip z r i) _ hc] with n hn
        refine hn.le.trans (measureReal_mono (fun x hx => cellf_sub_lab z r hi hx)
          (measure_ne_top _ _))
    exact ((Filter.eventually_all_finite (Set.finite_lt_nat I)).2 key).mono fun n hn i hi => hn i hi

/-! ### cadlag versions and sup-closeness -/

lemma cadlag_onUnit {x : ℝ → Fin K → ℝ} (h : IsCadlag01 x) : IsCadlag01 (onUnit x) := by
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · exact (h.1 t ht).congr (fun s hs => onUnit_of_mem x ⟨ht.1.trans hs.1, hs.2⟩)
      (onUnit_of_mem x ⟨ht.1, ht.2.le⟩)
  · obtain ⟨l, hl⟩ := h.2 t ht
    exact ⟨l, hl.congr' (eventually_nhdsWithin_of_forall fun s hs =>
      (onUnit_of_mem x ⟨hs.1, hs.2.le.trans ht.2⟩).symm)⟩

lemma cadlag_zero : IsCadlag01 (fun _ : ℝ => (0 : Fin K → ℝ)) :=
  ⟨fun _ _ => continuousWithinAt_const, fun _ _ => ⟨0, tendsto_const_nhds⟩⟩

/-- a measurable version of `onUnit ∘ x` all of whose paths are cadlag. -/
lemma good_version {α : Type} [MeasurableSpace α] {μ : Measure α} {x : α → ℝ → Fin K → ℝ}
    (hm : AEMeasurable (fun a => onUnit (x a)) μ) (hc : ∀ᵐ a ∂μ, IsCadlag01 (x a)) :
    ∃ g : α → ℝ → Fin K → ℝ, Measurable g ∧ (∀ a, IsCadlag01 (g a)) ∧
      (fun a => onUnit (x a)) =ᵐ[μ] g := by
  classical
  set h := hm.mk _ with hhd
  have hh : Measurable h := hm.measurable_mk
  have he := hm.ae_eq_mk
  set B := {a | ¬ (IsCadlag01 (x a) ∧ onUnit (x a) = h a)} with hBd
  have hB : μ B = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hc, he] with a h1 h2 hb
    exact hb ⟨h1, h2⟩
  set T := toMeasurable μ B
  refine ⟨fun a => if a ∈ T then (fun _ => 0) else h a,
    Measurable.ite (measurableSet_toMeasurable _ _) measurable_const hh, fun a => ?_, ?_⟩
  · by_cases ha : a ∈ T
    · simp only [ha, if_true]; exact cadlag_zero
    · simp only [ha, if_false]
      have hb : a ∉ B := fun hb => ha (subset_toMeasurable _ _ hb)
      simp only [hBd, Set.mem_ofPred_eq, not_not] at hb
      rw [← hb.2]; exact cadlag_onUnit hb.1
  · have hT : μ T = 0 := by rw [measure_toMeasurable]; exact hB
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hT] with a ha
    have hb : a ∉ B := fun hb => ha (subset_toMeasurable _ _ hb)
    simp only [hBd, Set.mem_ofPred_eq, not_not] at hb
    simp only [ha, if_false]
    exact hb.2

/-- `D1`-closeness below `1` of a cadlag and a continuous path gives uniform closeness on
`[0,1]`. -/
lemma sup_close {x y : ℝ → Fin K → ℝ} (hx : IsCadlag01 x) (hy : ContinuousOn y (Icc 0 1))
    {d : ℝ} (hd : d ≤ 1) (hD : D1 x y < d) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖x t - y t‖ ≤ d := by
  have hq : ∀ q : ℚ, ‖x (cq q) - y (cq q)‖ ≤ d := by
    intro q
    have h1 := (le_D1 x y q).trans_lt hD
    by_contra hc; push_neg at hc
    rcases le_total 1 ‖x (cq q) - y (cq q)‖ with h | h
    · rw [min_eq_left h] at h1; linarith
    · rw [min_eq_right h] at h1; linarith
  rcases ht.2.lt_or_eq with ht1 | ht1
  · -- approach `t` from the right through rationals
    have hseq : ∀ k : ℕ, ∃ q : ℚ, t < q ∧ (q : ℝ) < min (t + 1 / (k + 1)) 1 := fun k =>
      exists_rat_btwn (lt_min (by have : (0:ℝ) < 1 / (k + 1) := by positivity
                                  linarith) ht1)
    choose q hq1 hq2 using hseq
    have hqmem : ∀ k, (q k : ℝ) ∈ Icc t 1 := fun k => ⟨(hq1 k).le, ((hq2 k).trans_le (min_le_right _ _)).le⟩
    have hcq : ∀ k, cq (q k) = q k := fun k =>
      clamp01_of_mem ⟨ht.1.trans (hqmem k).1, (hqmem k).2⟩
    have hlim : Tendsto (fun k => (q k : ℝ)) atTop (𝓝[Icc t 1] t) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hqmem⟩
      have hup : Tendsto (fun k : ℕ => t + 1 / ((k:ℝ) + 1)) atTop (𝓝 t) := by
        have h0 := (tendsto_const_nhds (x := t)).add
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        rwa [add_zero] at h0
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
        (fun k => (hq1 k).le) (fun k => ((hq2 k).trans_le (min_le_left _ _)).le)
    have hxl := (hx.1 t ⟨ht.1, ht1⟩).tendsto.comp hlim
    have hyl := ((hy t ht).mono (Icc_subset_Icc_left ht.1)).tendsto.comp hlim
    refine le_of_tendsto' ((hxl.sub hyl).norm) fun k => ?_
    have := hq (q k)
    rwa [hcq k] at this
  · have := hq 1
    rw [show cq 1 = 1 by unfold cq; rw [Rat.cast_one]; exact clamp01_of_mem ⟨zero_le_one, le_rfl⟩]
      at this
    rwa [ht1]

end RepP

namespace RepC

open Filter Topology MeasureTheory Set Reiman84.QueueLength ProbabilityTheory

variable {K : ℕ}

/-- partition of a finite measure by a bounded label. -/
lemma psum {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν] (f : α → ℕ)
    (hf : Measurable f) (I : ℕ) (hfI : ∀ a, f a ≤ I) {S : Set α} :
    ∑ k ∈ Finset.range (I + 1), ν.real (f ⁻¹' {k} ∩ S) = ν.real S := by
  have h := sum_measure_preimage_singleton (μ := ν.restrict S) (Finset.range (I + 1))
    (f := f) (fun y _ => hf (measurableSet_singleton y))
  have hu : f ⁻¹' ↑(Finset.range (I + 1)) = univ := by
    ext a; simp [Nat.lt_succ_iff, hfI a]
  rw [hu, Measure.restrict_apply_univ] at h
  have h2 : ∀ k, (ν.restrict S) (f ⁻¹' {k}) = ν (f ⁻¹' {k} ∩ S) := fun k =>
    Measure.restrict_apply (hf (measurableSet_singleton k))
  simp only [h2] at h
  simp only [measureReal_def]
  rw [← h, ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)]

/-- a Bernoulli measure on `Bool` (`true` with probability `1 - e`). -/
noncomputable def bern (e : ℝ) : Measure Bool :=
  ENNReal.ofReal (1 - e) • Measure.dirac true + ENNReal.ofReal e • Measure.dirac false

lemma bern_prob {e : ℝ} (h0 : 0 ≤ e) (h1 : e ≤ 1) : IsProbabilityMeasure (bern e) := by
  constructor
  simp only [bern, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by linarith) h0]; simp

lemma bern_true (e : ℝ) : bern e {true} = ENNReal.ofReal (1 - e) := by
  simp [bern]

lemma bern_false (e : ℝ) : bern e {false} = ENNReal.ofReal e := by
  simp [bern]

/-- `m` if it is a probability measure, else the fallback `p`. -/
noncomputable def fixP {α : Type*} [MeasurableSpace α] (m p : Measure α) : Measure α := by
  classical exact if IsProbabilityMeasure m then m else p

lemma fixP_prob {α : Type*} [MeasurableSpace α] (m p : Measure α) [IsProbabilityMeasure p] :
    IsProbabilityMeasure (fixP m p) := by
  classical
  unfold fixP
  split_ifs with h
  · exact h
  · infer_instance

lemma fixP_eq {α : Type*} [MeasurableSpace α] {m : Measure α} (p : Measure α)
    (h : IsProbabilityMeasure m) : fixP m p = m := by
  classical
  unfold fixP; rw [if_pos h]

/-- mixing weight of cell `i` in the residual law. -/
noncomputable def wgt (pp p : ℕ → ℝ) (e : ℝ) (I i : ℕ) : ℝ :=
  (p i - (if i < I then (1 - e) * pp i else 0)) / (1 - (1 - e) * ∑ i' ∈ Finset.range I, pp i')

section Mix

variable {β : Type} [MeasurableSpace β]

noncomputable def cellLaw (μ : Measure β) (f : β → ℕ) (i : ℕ) : Measure β :=
  fixP (μ[|f ⁻¹' {i}]) μ

noncomputable def resLaw (μ : Measure β) (f : β → ℕ) (I : ℕ) (pp : ℕ → ℝ) (e : ℝ) : Measure β :=
  fixP (∑ i ∈ Finset.range (I + 1),
    ENNReal.ofReal (wgt pp (fun i => μ.real (f ⁻¹' {i})) e I i) • cellLaw μ f i) μ

noncomputable def mixLaw (μ : Measure β) (f : β → ℕ) (I : ℕ) (pp : ℕ → ℝ) (e : ℝ) :
    ℕ → Measure β
  | 0 => resLaw μ f I pp e
  | k + 1 => cellLaw μ f k

lemma mixLaw_prob (μ : Measure β) [IsProbabilityMeasure μ] (f : β → ℕ) (I : ℕ) (pp : ℕ → ℝ)
    (e : ℝ) (k : ℕ) : IsProbabilityMeasure (mixLaw μ f I pp e k) := by
  cases k
  · exact fixP_prob _ _
  · exact fixP_prob _ _

lemma cell_mul (μ : Measure β) [IsProbabilityMeasure μ] {f : β → ℕ} (hf : Measurable f) (i : ℕ)
    (S : Set β) : μ.real (f ⁻¹' {i}) * (cellLaw μ f i).real S = μ.real (f ⁻¹' {i} ∩ S) := by
  have hs : MeasurableSet (f ⁻¹' {i}) := hf (measurableSet_singleton i)
  by_cases h : μ (f ⁻¹' {i}) = 0
  · have h0 : μ (f ⁻¹' {i} ∩ S) = 0 := measure_mono_null inter_subset_left h
    simp only [measureReal_def, h, h0, ENNReal.toReal_zero, zero_mul]
  · have hc : cellLaw μ f i = μ[|f ⁻¹' {i}] := fixP_eq _ (cond_isProbabilityMeasure h)
    rw [hc, measureReal_def, measureReal_def, measureReal_def, cond_apply hs μ S,
      ENNReal.toReal_mul, ENNReal.toReal_inv]
    have hne : (μ (f ⁻¹' {i})).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.2 ⟨h, measure_ne_top _ _⟩
    field_simp

/-- the law identity of one level of the coupling. -/
lemma mix_law (μ : Measure β) [IsProbabilityMeasure μ] {f : β → ℕ} (hf : Measurable f) (I : ℕ)
    (hfI : ∀ a, f a ≤ I) (pp : ℕ → ℝ) (hpp0 : ∀ i, 0 ≤ pp i)
    (hpp1 : ∑ i ∈ Finset.range I, pp i ≤ 1) {e : ℝ} (he0 : 0 < e) (he1 : e < 1)
    (hlev : ∀ i < I, (1 - e) * pp i ≤ μ.real (f ⁻¹' {i})) (S : Set β) :
    (1 - (1 - e) * ∑ i ∈ Finset.range I, pp i) * (mixLaw μ f I pp e 0).real S +
      ∑ i ∈ Finset.range I, (1 - e) * pp i * (mixLaw μ f I pp e (i + 1)).real S =
      μ.real S := by
  set d := 1 - (1 - e) * ∑ i ∈ Finset.range I, pp i with hd
  set p : ℕ → ℝ := fun i => μ.real (f ⁻¹' {i}) with hp
  set c : ℕ → ℝ := fun i => if i < I then (1 - e) * pp i else 0 with hc
  have hdpos : 0 < d := by
    have : (1 - e) * ∑ i ∈ Finset.range I, pp i ≤ (1 - e) * 1 :=
      mul_le_mul_of_nonneg_left hpp1 (by linarith)
    linarith
  have hw : ∀ i, d * wgt pp p e I i = p i - c i := by
    intro i; show d * ((p i - c i) / d) = _; field_simp
  have hcsum : ∀ g : ℕ → ℝ, ∑ i ∈ Finset.range (I + 1), c i * g i =
      ∑ i ∈ Finset.range I, (1 - e) * pp i * g i := by
    intro g
    rw [Finset.sum_range_succ]
    simp only [hc, lt_irrefl, if_false, zero_mul, add_zero]
    exact Finset.sum_congr rfl fun i hi => by rw [if_pos (Finset.mem_range.1 hi)]
  have hpsum : ∑ i ∈ Finset.range (I + 1), p i = 1 := by
    have := psum μ f hf I hfI (S := univ)
    simpa [hp] using this
  have hw0 : ∀ i ∈ Finset.range (I + 1), 0 ≤ wgt pp p e I i := by
    intro i hi
    have : 0 ≤ p i - c i := by
      simp only [hc]
      split_ifs with h
      · simpa [hp] using sub_nonneg.2 (hlev i h)
      · simp only [sub_zero, hp]; exact measureReal_nonneg
    show 0 ≤ (p i - c i) / d
    exact div_nonneg this hdpos.le
  have hwsum : ∑ i ∈ Finset.range (I + 1), wgt pp p e I i = 1 := by
    have h1 : d * ∑ i ∈ Finset.range (I + 1), wgt pp p e I i = d := by
      rw [Finset.mul_sum]
      simp only [hw]
      rw [Finset.sum_sub_distrib, hpsum]
      have := hcsum (fun _ => 1)
      simp only [mul_one] at this
      rw [this, ← Finset.mul_sum]
    field_simp at h1
    nlinarith [h1]
  -- the residual law is a probability measure
  set R := ∑ i ∈ Finset.range (I + 1), ENNReal.ofReal (wgt pp p e I i) • cellLaw μ f i with hR
  have hcl : ∀ i, IsProbabilityMeasure (cellLaw μ f i) := fun i => fixP_prob _ _
  have hRapp : ∀ T, R T = ∑ i ∈ Finset.range (I + 1),
      ENNReal.ofReal (wgt pp p e I i) * cellLaw μ f i T := by
    intro T
    rw [hR, Measure.coe_finsetSum, Finset.sum_apply]
    rfl
  have hRprob : IsProbabilityMeasure R := by
    constructor
    rw [hRapp]
    simp only [measure_univ, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg hw0, hwsum, ENNReal.ofReal_one]
  have h0 : mixLaw μ f I pp e 0 = R := fixP_eq _ hRprob
  have hRreal : R.real S = ∑ i ∈ Finset.range (I + 1), wgt pp p e I i * (cellLaw μ f i).real S := by
    rw [measureReal_def, hRapp, ENNReal.toReal_sum (fun i _ =>
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hw0 i hi), measureReal_def]
  have hmix : ∀ i, mixLaw μ f I pp e (i + 1) = cellLaw μ f i := fun i => rfl
  rw [h0, hRreal]
  simp only [hmix]
  rw [Finset.mul_sum]
  have e1 : ∀ i, d * (wgt pp p e I i * (cellLaw μ f i).real S) =
      p i * (cellLaw μ f i).real S - c i * (cellLaw μ f i).real S := by
    intro i; rw [← mul_assoc, hw i]; ring
  simp only [e1]
  rw [Finset.sum_sub_distrib, hcsum (fun i => (cellLaw μ f i).real S)]
  have e2 : ∑ i ∈ Finset.range (I + 1), p i * (cellLaw μ f i).real S = μ.real S := by
    rw [← psum μ f hf I hfI (S := S)]
    exact Finset.sum_congr rfl fun i _ => cell_mul μ hf i S
  rw [e2]; ring

end Mix

lemma cadlag_of_cont {x : ℝ → Fin K → ℝ} (h : ContinuousOn x (Icc 0 1)) : IsCadlag01 x := by
  refine ⟨fun t ht => (h t ⟨ht.1, ht.2.le⟩).mono (Icc_subset_Icc ht.1 le_rfl),
    fun t ht => ⟨x t, ?_⟩⟩
  exact ((h t ⟨ht.1.le, ht.2⟩).mono (fun s hs => ⟨hs.1, hs.2.le.trans ht.2⟩)).tendsto

/-- the abstract coupling (Billingsley Thm 6.7 partition construction). -/
theorem coupling {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [hP : ∀ n, IsProbabilityMeasure (P n)]
    (g : ∀ n, Ω n → ℝ → Fin K → ℝ) (hg : ∀ n, Measurable (g n))
    (hgc : ∀ n a, IsCadlag01 (g n a))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (y : Ω' → ℝ → Fin K → ℝ) (hy : Measurable y) (hyc : ∀ ω, ContinuousOn (y ω) (Icc 0 1))
    (L : ℕ → (ℝ → Fin K → ℝ) → ℕ) (hL : ∀ j, Measurable (L j)) (I : ℕ → ℕ)
    (hLI : ∀ j x, L j x ≤ I j) (e b : ℕ → ℝ) (he0 : ∀ j, 0 < e j) (he1 : ∀ j, e j < 1)
    (hes : Summable e) (hb : Tendsto b atTop (𝓝 0))
    (hclose : ∀ j x x', IsCadlag01 x → ContinuousOn x' (Icc 0 1) → L j x = L j x' →
      L j x < I j → ∀ t ∈ Icc (0:ℝ) 1, ‖x t - x' t‖ ≤ b j)
    (hrem : ∀ j, P'.real {ω | L j (y ω) = I j} ≤ e j)
    (N : ℕ → ℕ)
    (hlev : ∀ j n, N j ≤ n → ∀ i < I j,
      (1 - e j) * P'.real {ω | L j (y ω) = i} ≤ (P n).real {a | L j (g n a) = i}) :
    ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (Q : Measure Ω₀) (Y : ℕ → Ω₀ → ℝ → Fin K → ℝ)
      (Y' : Ω₀ → ℝ → Fin K → ℝ),
      IsProbabilityMeasure Q ∧ (∀ n, Measurable (Y n)) ∧ Measurable Y' ∧
      (∀ᶠ n in atTop, Q.map (Y n) = (P n).map (g n)) ∧
      Q.map Y' = P'.map y ∧ ∀ᵐ ω ∂Q, SkorohodTendsto (fun n => Y n ω) (Y' ω) := by
  classical
  obtain ⟨jn, hjn1, hjn2⟩ : ∃ jn : ℕ → ℕ, (∀ n, N 0 ≤ n → N (jn n) ≤ n) ∧
      ∀ J n, N J + J ≤ n → J ≤ jn n := by
    refine ⟨fun n => Nat.findGreatest (fun j => N j + j ≤ n) n, fun n hn => ?_,
      fun J n hJ => Nat.le_findGreatest (by omega) hJ⟩
    have := Nat.findGreatest_spec (P := fun j => N j + j ≤ n) (m := 0) (Nat.zero_le n)
      (by simpa using hn)
    show N (Nat.findGreatest (fun j => N j + j ≤ n) n) ≤ n
    omega
  set pp : ℕ → ℕ → ℝ := fun j i => P'.real {ω | L j (y ω) = i} with hpp
  set f : ∀ n, Ω n → ℕ := fun n a => L (jn n) (g n a) with hfd
  have hfm : ∀ n, Measurable (f n) := fun n => (hL _).comp (hg n)
  have hfI : ∀ n a, f n a ≤ I (jn n) := fun n a => hLI _ _
  set law : ∀ p : ℕ × ℕ, Measure (Ω p.1) := fun p =>
    mixLaw (P p.1) (f p.1) (I (jn p.1)) (pp (jn p.1)) (e (jn p.1)) p.2 with hlaw
  haveI hlawp : ∀ p, IsProbabilityMeasure (law p) := fun p => mixLaw_prob _ _ _ _ _ _
  haveI hbp : ∀ j, IsProbabilityMeasure (bern (e j)) := fun j =>
    bern_prob (he0 j).le (he1 j).le
  set Qβ : Measure (ℕ → Bool) := Measure.infinitePi fun j => bern (e j) with hQβ
  set Qξ : Measure (Π p : ℕ × ℕ, Ω p.1) := Measure.infinitePi law with hQξ
  set Q₁ : Measure (Ω' × (ℕ → Bool)) := P'.prod Qβ with hQ₁
  set Q : Measure ((Ω' × (ℕ → Bool)) × (Π p : ℕ × ℕ, Ω p.1)) := Q₁.prod Qξ with hQ
  haveI : IsProbabilityMeasure Qβ := by rw [hQβ]; infer_instance
  haveI : IsProbabilityMeasure Qξ := by rw [hQξ]; infer_instance
  haveI : IsProbabilityMeasure Q₁ := by rw [hQ₁]; infer_instance
  haveI hQp : IsProbabilityMeasure Q := by rw [hQ]; infer_instance
  set F : ℕ → Bool × ℕ → ℕ := fun n q => if q.1 = true ∧ q.2 < I (jn n) then q.2 + 1 else 0
    with hF
  set κ : ℕ → Ω' × (ℕ → Bool) → ℕ := fun n ω₁ => F n (ω₁.2 (jn n), L (jn n) (y ω₁.1)) with hκ
  have hκm : ∀ n, Measurable (κ n) := fun n =>
    (measurable_of_countable (F n)).comp (((measurable_pi_apply _).comp measurable_snd).prodMk
      ((hL _).comp (hy.comp measurable_fst)))
  have hκI : ∀ n ω₁, κ n ω₁ ≤ I (jn n) := by
    intro n ω₁
    simp only [hκ, hF]
    split_ifs with h
    · exact h.2
    · exact Nat.zero_le _
  set Y : ℕ → (Ω' × (ℕ → Bool)) × (Π p : ℕ × ℕ, Ω p.1) → ℝ → Fin K → ℝ :=
    fun n ω₀ => g n (ω₀.2 (n, κ n ω₀.1)) with hY
  have hYm : ∀ n, Measurable (Y n) := by
    intro n
    have h1 : Measurable fun q : ℕ × (Π p : ℕ × ℕ, Ω p.1) => g n (q.2 (n, q.1)) :=
      measurable_from_prod_countable_right fun k => (hg n).comp (measurable_pi_apply (n, k))
    exact h1.comp (((hκm n).comp measurable_fst).prodMk measurable_snd)
  have hY'm : Measurable fun ω₀ : (Ω' × (ℕ → Bool)) × (Π p : ℕ × ℕ, Ω p.1) => y ω₀.1.1 :=
    hy.comp (measurable_fst.comp measurable_fst)
  have hξ : ∀ p (S : Set (Ω p.1)), MeasurableSet S → Qξ {ξ | ξ p ∈ S} = law p S := by
    intro p S hS
    rw [← Measure.infinitePi_map_eval law p, Measure.map_apply (measurable_pi_apply p) hS]
    rfl
  have hβ : ∀ j (s : Set Bool), Qβ {b | b j ∈ s} = bern (e j) s := by
    intro j s
    rw [← Measure.infinitePi_map_eval (fun j => bern (e j)) j,
      Measure.map_apply (measurable_pi_apply j) (Set.toFinite s).measurableSet]
    rfl
  refine ⟨_, inferInstance, Q, Y, fun ω₀ => y ω₀.1.1, hQp, hYm, hY'm, ?_, ?_, ?_⟩
  · -- laws of `Y n`
    filter_upwards [eventually_ge_atTop (N 0)] with n hn
    have hN := hjn1 n hn
    refine Measure.ext fun A hA => ?_
    rw [Measure.map_apply (hYm n) hA, Measure.map_apply (hg n) hA]
    set S := g n ⁻¹' A with hS
    have hSm : MeasurableSet S := hg n hA
    suffices hreal : Q.real (Y n ⁻¹' A) = (P n).real S by
      rw [measureReal_def, measureReal_def] at hreal
      exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 hreal
    have hsplit := psum Q (fun ω₀ => κ n ω₀.1) ((hκm n).comp measurable_fst) (I (jn n))
      (fun ω₀ => hκI n ω₀.1) (S := Y n ⁻¹' A)
    have hrect : ∀ k, (fun ω₀ : (Ω' × (ℕ → Bool)) × (Π p : ℕ × ℕ, Ω p.1) => κ n ω₀.1) ⁻¹' {k}
        ∩ Y n ⁻¹' A = (κ n ⁻¹' {k}) ×ˢ {ξ : Π p : ℕ × ℕ, Ω p.1 | ξ (n, k) ∈ S} := by
      intro k
      ext ⟨ω₁, ξ⟩
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_prod, mem_setOf_eq, hY, hS]
      constructor
      · rintro ⟨h1, h2⟩; rw [h1] at h2; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; rw [h1]; exact ⟨rfl, h2⟩
    have hterm : ∀ k, Q.real ((fun ω₀ : (Ω' × (ℕ → Bool)) × (Π p : ℕ × ℕ, Ω p.1) =>
        κ n ω₀.1) ⁻¹' {k} ∩ Y n ⁻¹' A) = Q₁.real (κ n ⁻¹' {k}) * (law (n, k)).real S := by
      intro k
      rw [hrect k, hQ, measureReal_prod_prod, measureReal_def (μ := Qξ), hξ (n, k) S hSm]
      rfl
    have hk1 : ∀ i < I (jn n), Q₁.real (κ n ⁻¹' {i + 1}) = (1 - e (jn n)) * pp (jn n) i := by
      intro i hi
      have : κ n ⁻¹' {i + 1} =
          {ω | L (jn n) (y ω) = i} ×ˢ {b : ℕ → Bool | b (jn n) ∈ ({true} : Set Bool)} := by
        ext ⟨ω, b⟩
        show F n (b (jn n), L (jn n) (y ω)) = i + 1 ↔
          L (jn n) (y ω) = i ∧ b (jn n) ∈ ({true} : Set Bool)
        rw [mem_singleton_iff]
        by_cases hc : b (jn n) = true ∧ L (jn n) (y ω) < I (jn n)
        · have hF1 : F n (b (jn n), L (jn n) (y ω)) = L (jn n) (y ω) + 1 := by
            simp only [hF]; exact if_pos hc
          rw [hF1]; constructor
          · intro h'; exact ⟨by omega, hc.1⟩
          · rintro ⟨h1, -⟩; omega
        · have hF0 : F n (b (jn n), L (jn n) (y ω)) = 0 := by
            simp only [hF]; exact if_neg hc
          rw [hF0]; constructor
          · intro h'; exact absurd h' (by omega)
          · rintro ⟨h1, h2⟩
            have h3 : L (jn n) (y ω) < I (jn n) := by rw [h1]; exact hi
            exact (hc ⟨h2, h3⟩).elim
      rw [this, hQ₁, measureReal_prod_prod, measureReal_def (μ := Qβ), hβ, bern_true,
        ENNReal.toReal_ofReal (by linarith [he1 (jn n)])]
      simp only [hpp]; ring
    have hk0 : Q₁.real (κ n ⁻¹' {0}) =
        1 - (1 - e (jn n)) * ∑ i ∈ Finset.range (I (jn n)), pp (jn n) i := by
      have h := psum Q₁ (κ n) (hκm n) (I (jn n)) (hκI n) (S := univ)
      rw [Finset.sum_range_succ'] at h
      simp only [inter_univ, probReal_univ] at h
      rw [Finset.mul_sum]
      have : ∑ i ∈ Finset.range (I (jn n)), Q₁.real (κ n ⁻¹' {i + 1}) =
          ∑ i ∈ Finset.range (I (jn n)), (1 - e (jn n)) * pp (jn n) i :=
        Finset.sum_congr rfl fun i hi => hk1 i (Finset.mem_range.1 hi)
      linarith
    rw [← hsplit]
    simp only [hterm]
    rw [Finset.sum_range_succ', hk0]
    have hsum2 : ∑ i ∈ Finset.range (I (jn n)), Q₁.real (κ n ⁻¹' {i + 1}) *
        (law (n, i + 1)).real S =
        ∑ i ∈ Finset.range (I (jn n)), (1 - e (jn n)) * pp (jn n) i * (law (n, i + 1)).real S :=
      Finset.sum_congr rfl fun i hi => by rw [hk1 i (Finset.mem_range.1 hi)]
    rw [hsum2]
    have hpp1 : ∑ i ∈ Finset.range (I (jn n)), pp (jn n) i ≤ 1 := by
      have h := psum P' (fun ω => L (jn n) (y ω)) ((hL _).comp hy) (I (jn n))
        (fun ω => hLI _ _) (S := univ)
      rw [Finset.sum_range_succ] at h
      simp only [inter_univ, probReal_univ] at h
      have h0 : 0 ≤ P'.real ((fun ω => L (jn n) (y ω)) ⁻¹' {I (jn n)}) := measureReal_nonneg
      have h1 : ∑ i ∈ Finset.range (I (jn n)), pp (jn n) i =
          ∑ i ∈ Finset.range (I (jn n)), P'.real ((fun ω => L (jn n) (y ω)) ⁻¹' {i}) := rfl
      linarith
    have hml : (1 - (1 - e (jn n)) * ∑ i ∈ Finset.range (I (jn n)), pp (jn n) i) *
        (law (n, 0)).real S +
        ∑ i ∈ Finset.range (I (jn n)), (1 - e (jn n)) * pp (jn n) i * (law (n, i + 1)).real S =
        (P n).real S :=
      mix_law (P n) (hfm n) (I (jn n)) (hfI n) (pp (jn n)) (fun i => measureReal_nonneg) hpp1
        (he0 _) (he1 _) (fun i hi => hlev (jn n) n hN i hi) S
    linarith
  · -- law of `Y'`
    refine Measure.ext fun A hA => ?_
    rw [Measure.map_apply hY'm hA, Measure.map_apply hy hA]
    have : (fun ω₀ : (Ω' × (ℕ → Bool)) × (Π p : ℕ × ℕ, Ω p.1) => y ω₀.1.1) ⁻¹' A =
        ((y ⁻¹' A) ×ˢ univ) ×ˢ univ := by ext; simp
    rw [this, hQ, Measure.prod_prod, hQ₁, Measure.prod_prod]; simp
  · -- almost sure convergence
    set B : ℕ → Set ((Ω' × (ℕ → Bool)) × (Π p : ℕ × ℕ, Ω p.1)) := fun j =>
      {ω₀ | ω₀.1.2 j = false} ∪ {ω₀ | L j (y ω₀.1.1) = I j} with hB
    have hBle : ∀ j, Q (B j) ≤ ENNReal.ofReal (2 * e j) := by
      intro j
      have h1 : Q {ω₀ | ω₀.1.2 j = false} = ENNReal.ofReal (e j) := by
        have : {ω₀ : (Ω' × (ℕ → Bool)) × (Π p : ℕ × ℕ, Ω p.1) | ω₀.1.2 j = false} =
            (univ ×ˢ {b : ℕ → Bool | b j ∈ ({false} : Set Bool)}) ×ˢ univ := by ext; simp
        rw [this, hQ, Measure.prod_prod, hQ₁, Measure.prod_prod, hβ, bern_false]; simp
      have h2 : Q {ω₀ | L j (y ω₀.1.1) = I j} ≤ ENNReal.ofReal (e j) := by
        have : {ω₀ : (Ω' × (ℕ → Bool)) × (Π p : ℕ × ℕ, Ω p.1) | L j (y ω₀.1.1) = I j} =
            ({ω | L j (y ω) = I j} ×ˢ univ) ×ˢ univ := by ext; simp
        rw [this, hQ, Measure.prod_prod, hQ₁, Measure.prod_prod]
        simp only [measure_univ, mul_one]
        exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (he0 j).le).2 (hrem j)
      calc Q (B j) ≤ Q {ω₀ | ω₀.1.2 j = false} + Q {ω₀ | L j (y ω₀.1.1) = I j} :=
            measure_union_le _ _
        _ ≤ ENNReal.ofReal (e j) + ENNReal.ofReal (e j) := add_le_add h1.le h2
        _ = ENNReal.ofReal (2 * e j) := by
            rw [← ENNReal.ofReal_add (he0 j).le (he0 j).le]; ring_nf
    have hBC : ∀ᵐ ω₀ ∂Q, ∀ᶠ j in atTop, ω₀ ∉ B j := by
      refine ae_eventually_notMem (ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hBle))
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by linarith [he0 j]) (hes.mul_left 2)]
      exact ENNReal.ofReal_ne_top
    have hA0 : ∀ᵐ ω₀ ∂Q, ∀ j i, L j (y ω₀.1.1) = i → pp j i ≠ 0 := by
      rw [ae_all_iff]; intro j; rw [ae_all_iff]; intro i
      by_cases h : pp j i = 0
      · have hz : Q {ω₀ | L j (y ω₀.1.1) = i} = 0 := by
          have : {ω₀ : (Ω' × (ℕ → Bool)) × (Π p : ℕ × ℕ, Ω p.1) | L j (y ω₀.1.1) = i} =
              ({ω | L j (y ω) = i} ×ˢ univ) ×ˢ univ := by ext; simp
          rw [this, hQ, Measure.prod_prod, hQ₁, Measure.prod_prod]
          simp only [measure_univ, mul_one]
          exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 h
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 hz] with ω₀ hω₀ h' _
        exact hω₀ h'
      · exact Eventually.of_forall fun _ _ => h
    have hB0 : ∀ᵐ ω₀ ∂Q, ∀ n i, P n (f n ⁻¹' {i}) ≠ 0 → f n (ω₀.2 (n, i + 1)) = i := by
      rw [ae_all_iff]; intro n; rw [ae_all_iff]; intro i
      by_cases h : P n (f n ⁻¹' {i}) = 0
      · exact Eventually.of_forall fun _ h' => absurd h h'
      · have hs : MeasurableSet (f n ⁻¹' {i}) := hfm n (measurableSet_singleton i)
        have hz : Q {ω₀ | ω₀.2 (n, i + 1) ∈ (f n ⁻¹' {i})ᶜ} = 0 := by
          have : {ω₀ : (Ω' × (ℕ → Bool)) × (Π p : ℕ × ℕ, Ω p.1) |
              ω₀.2 (n, i + 1) ∈ (f n ⁻¹' {i})ᶜ} =
              univ ×ˢ {ξ : Π p : ℕ × ℕ, Ω p.1 | ξ (n, i + 1) ∈ (f n ⁻¹' {i})ᶜ} := by
            ext; simp
          rw [this, hQ, Measure.prod_prod, hξ (n, i + 1) _ hs.compl]
          have hc : law (n, i + 1) = (P n)[|f n ⁻¹' {i}] :=
            fixP_eq _ (cond_isProbabilityMeasure h)
          rw [hc, cond_apply hs, inter_compl_self, measure_empty, mul_zero, mul_zero]
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 hz] with ω₀ hω₀ _
        by_contra hne
        exact hω₀ hne
    filter_upwards [hBC, hA0, hB0] with ω₀ h1 h2 h3
    refine ⟨fun n => hgc n _, cadlag_of_cont (hyc _), fun _ t => t,
      fun _ => ⟨continuousOn_id, strictMonoOn_id, rfl, rfl⟩, fun ε hε => ?_⟩
    obtain ⟨J0, hJ0⟩ := eventually_atTop.1 (hb.eventually (gt_mem_nhds hε))
    obtain ⟨J1, hJ1⟩ := eventually_atTop.1 h1
    filter_upwards [eventually_ge_atTop (max (N 0) (N (max J0 J1) + max J0 J1))] with n hn t ht
    have hjJ : max J0 J1 ≤ jn n := hjn2 _ n (le_of_max_le_right hn)
    have hN : N (jn n) ≤ n := hjn1 n (le_of_max_le_left hn)
    have hnotB := hJ1 (jn n) (le_trans (le_max_right _ _) hjJ)
    simp only [hB, mem_union, mem_setOf_eq, not_or] at hnotB
    obtain ⟨hβj, hLne⟩ := hnotB
    have hβj' : ω₀.1.2 (jn n) = true := by simpa using hβj
    have hiI : L (jn n) (y ω₀.1.1) < I (jn n) := lt_of_le_of_ne (hLI _ _) hLne
    have hκn : κ n ω₀.1 = L (jn n) (y ω₀.1.1) + 1 := by
      simp only [hκ, hF]; rw [if_pos ⟨hβj', hiI⟩]
    have hpp0 : pp (jn n) (L (jn n) (y ω₀.1.1)) ≠ 0 := h2 (jn n) _ rfl
    have hPn : P n (f n ⁻¹' {L (jn n) (y ω₀.1.1)}) ≠ 0 := by
      have hlv := hlev (jn n) n hN _ hiI
      have hpos : 0 < pp (jn n) (L (jn n) (y ω₀.1.1)) :=
        lt_of_le_of_ne measureReal_nonneg (Ne.symm hpp0)
      have : 0 < (P n).real (f n ⁻¹' {L (jn n) (y ω₀.1.1)}) :=
        lt_of_lt_of_le (mul_pos (by linarith [he1 (jn n)]) hpos) hlv
      intro h0
      rw [measureReal_def, h0] at this
      simp at this
    have hlab : L (jn n) (g n (ω₀.2 (n, L (jn n) (y ω₀.1.1) + 1))) = L (jn n) (y ω₀.1.1) :=
      h3 n _ hPn
    have hYn : Y n ω₀ = g n (ω₀.2 (n, L (jn n) (y ω₀.1.1) + 1)) := by
      simp only [hY]; rw [hκn]
    refine ⟨by simp [hε], ?_⟩
    rw [hYn]
    have := hclose (jn n) (g n (ω₀.2 (n, L (jn n) (y ω₀.1.1) + 1))) (y ω₀.1.1) (hgc _ _)
      (hyc _) hlab (by rw [hlab]; exact hiI) t ht
    exact lt_of_le_of_lt this (hJ0 (jn n) (le_trans (le_max_left _ _) hjJ))

end RepC

namespace RepP

open Filter Topology MeasureTheory Set Reiman84.QueueLength

/-- RepThm (Billingsley 1999 Thm 7.5 + 6.7, continuous limit). -/
theorem rep_main {K : ℕ} {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    (X : ∀ n, Ω n → ℝ → Fin K → ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    (X' : Ω' → ℝ → Fin K → ℝ)
    (hP : ∀ n, IsProbabilityMeasure (P n)) (hP' : IsProbabilityMeasure P')
    (hXa : ∀ n, AEMeasurable (fun ω => onUnit (X n ω)) (P n) ∧
      ∀ᵐ ω ∂(P n), IsCadlag01 (X n ω))
    (hX'm : ∀ t, Measurable fun ω => X' ω t) (hc : ∀ ω, ContinuousOn (X' ω) (Icc 0 1))
    (hF : FddConv P X P' X') (hT : ModTight P X) : WeakConvD P X P' X' := by
  have hXm : ∀ n, AEMeasurable (fun ω => onUnit (X n ω)) (P n) := fun n => (hXa n).1
  have hy : Measurable fun ω => onUnit (X' ω) :=
    measurable_pi_lambda _ fun t => hX'm (clamp01 t)
  set μ' := P'.map (fun ω => onUnit (X' ω)) with hμ'
  set μn : ℕ → Measure (ℝ → Fin K → ℝ) := fun n => (P n).map (fun ω => onUnit (X n ω))
    with hμn
  haveI : IsProbabilityMeasure μ' := Measure.isProbabilityMeasure_map hy.aemeasurable
  haveI : ∀ n, IsProbabilityMeasure (μn n) := fun n => Measure.isProbabilityMeasure_map (hXm n)
  have hport : ∀ g : (ℝ → Fin K → ℝ) → ℝ, Measurable g → (∀ x y, |g x - g y| ≤ D1 x y) →
      ∀ c, c < μ'.real {x | 0 < g x} → ∀ᶠ n in atTop, c < (μn n).real {x | 0 < g x} :=
    fun g hgm hgL c hcμ => port hP hP' hXm hX'm hc hF hT hgm hgL hcμ
  haveI : Nonempty (Ctr K) := ⟨⟨0, fun _ _ => 0⟩⟩
  obtain ⟨ec, hec⟩ := exists_surjective_nat (Ctr K)
  set z : ℕ → ℝ → Fin K → ℝ := fun i => ctr (ec i) with hzd
  have hdense : ∀ ω, ∀ r > 0, ∃ i, D1 (onUnit (X' ω)) (z i) < r := by
    intro ω r hr
    obtain ⟨c, hcr⟩ := ctr_dense (hc ω) hr
    obtain ⟨i, rfl⟩ := hec c
    exact ⟨i, hcr⟩
  have hset : MeasurableSet {x : ℝ → Fin K → ℝ | ∀ r > 0, ∃ i, D1 x (z i) < r} := by
    have : {x : ℝ → Fin K → ℝ | ∀ r > 0, ∃ i, D1 x (z i) < r} =
        ⋂ k : ℕ, ⋃ i : ℕ, {x | D1 x (z i) < 1 / ((k:ℝ) + 1)} := by
      ext x
      simp only [mem_setOf_eq, mem_iInter, mem_iUnion]
      constructor
      · intro h k; exact h _ (by positivity)
      · intro h r hr
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt hr
        obtain ⟨i, hi⟩ := h k
        exact ⟨i, hi.trans hk⟩
    rw [this]
    exact MeasurableSet.iInter fun k => MeasurableSet.iUnion fun i =>
      measurableSet_lt (D1_meas _) measurable_const
  have hz : ∀ᵐ x ∂μ', ∀ r > 0, ∃ i, D1 x (z i) < r :=
    (ae_map_iff hy.aemeasurable hset).2 (ae_of_all _ hdense)
  have hlevel := fun j : ℕ => level μ' μn hport z hz (ε := (1/2:ℝ)^(j+1))
    (ρ := (1/2:ℝ)^(j+1)) (τ := (1/2:ℝ)^(j+1)) (by positivity) (by positivity) (by positivity)
  choose r hr1 hr2 I hrem hev using hlevel
  choose N hN using fun j => eventually_atTop.1 (hev j)
  choose g hgm hgc hge using fun n => good_version (hXa n).1 (hXa n).2
  haveI := hP
  have hmapg : ∀ n, μn n = (P n).map (g n) := fun n => Measure.map_congr (hge n)
  have hreal' : ∀ j i, P'.real {ω | lab z (r j) (I j) (onUnit (X' ω)) = i} =
      μ'.real {x | lab z (r j) (I j) x = i} := by
    intro j i
    have hs : MeasurableSet {x : ℝ → Fin K → ℝ | lab z (r j) (I j) x = i} :=
      lab_meas z (r j) (I j) (measurableSet_singleton i)
    simp only [measureReal_def]
    rw [hμ', Measure.map_apply hy hs]
    rfl
  have hrealn : ∀ n j i, (P n).real {a | lab z (r j) (I j) (g n a) = i} =
      (μn n).real {x | lab z (r j) (I j) x = i} := by
    intro n j i
    have hs : MeasurableSet {x : ℝ → Fin K → ℝ | lab z (r j) (I j) x = i} :=
      lab_meas z (r j) (I j) (measurableSet_singleton i)
    simp only [measureReal_def]
    rw [hmapg n, Measure.map_apply (hgm n) hs]
    rfl
  have hes : Summable (fun j : ℕ => (1/2:ℝ)^(j+1)) := by
    have := (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num)).mul_right (1/2)
    exact this.congr fun j => by ring
  obtain ⟨Ω₀, m₀, Q, Y, Y', hQ, hYm, hY'm, hlaw, hlaw', has⟩ :=
    RepC.coupling P g hgm hgc P' (fun ω => onUnit (X' ω)) hy
      (fun ω => (hc ω).congr fun t ht => onUnit_of_mem _ ht)
      (fun j => lab z (r j) (I j)) (fun j => lab_meas z (r j) (I j)) I
      (fun j x => lab_le z (r j) (I j) x) (fun j => (1/2:ℝ)^(j+1)) (fun j => (1/2:ℝ)^j)
      (fun j => by positivity)
      (fun j => pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero j))
      hes (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
      (fun j x x' hx hx' heq hlt t ht => by
        have h1 := lab_close z (r j) (I j) heq hlt
        have h2 : 2 * r j < (1/2:ℝ)^j := by
          have := hr2 j; rw [pow_succ] at this; linarith
        exact sup_close hx hx' (pow_le_one₀ (by norm_num) (by norm_num)) (h1.trans h2) ht)
      (fun j => by have := hrem j; rw [← hreal'] at this; exact this)
      N
      (fun j n hn i hi => by
        have := hN j n hn i hi; rw [← hreal', ← hrealn] at this; exact this)
  refine ⟨Ω₀, m₀, Q, Y, Y', hQ, hYm, hY'm, ?_, hlaw', has⟩
  filter_upwards [hlaw] with n hn
  rw [hn]; exact (hmapg n).symm

end RepP


open Filter Topology MeasureTheory Reiman84.QueueLength in
theorem solution {K : ℕ} {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) (X : ∀ n, Ω n → ℝ → Fin K → ℝ) {Ω' : Type} [MeasurableSpace Ω']
    (P' : Measure Ω') (X' : Ω' → ℝ → Fin K → ℝ)
    (hP : ∀ n, IsProbabilityMeasure (P n)) (hP' : IsProbabilityMeasure P')
    (hXa : ∀ n, AEMeasurable (fun ω => onUnit (X n ω)) (P n) ∧
      ∀ᵐ ω ∂(P n), IsCadlag01 (X n ω))
    (hX'm : ∀ t, Measurable fun ω => X' ω t) (hc : ∀ ω, ContinuousOn (X' ω) (Set.Icc 0 1))
    (hF : ∀ (m : ℕ) (τ : Fin m → ℝ), (∀ i, τ i ∈ Set.Icc (0:ℝ) 1) →
      ∀ (f : (Fin m → Fin K → ℝ) → ℝ), (∃ C : ℝ, ∀ x, |f x| ≤ C) →
        (∃ L : NNReal, LipschitzWith L f) →
        Tendsto (fun n => ∫ ω, f (fun i => X n ω (τ i)) ∂(P n)) atTop
          (𝓝 (∫ ω, f (fun i => X' ω (τ i)) ∂P')))
    (hT : ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      P n {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ δ ∧
        ε ≤ ‖X n ω s - X n ω t‖} ≤ ENNReal.ofReal η) :
    WeakConvD P X P' X' := by
  exact RepP.rep_main P X P' X' hP hP' hXa hX'm hc hF hT
