-- Prove2me | solution 1 for PathoSubgrad.Circle.nonconvergent_subgradient_sequence
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-09T21:36:10.067441+00:00
-- url     : https://prove2.me/submissions/eb053739-e0c3-4369-95cc-640f92c1f2b4

import Mathlib
import Definitions.Def_PathoSubgrad_Circle_Setting
import Definitions.Def_PathoSubgrad_Circle_Construction

set_option autoImplicit false

open Filter Topology
open scoped InnerProductSpace ContDiff

/-! Construction (our own, simpler than the paper's circle): critical set = the line `y 0 = 0`.
`f y = |y 0| + Σ' i, B i y`, `B i` a small bump that is linear `t i * (y 1 - b i)` near `x i`.
Sequence `x i = ((-1)^i c i, sin (κ H i))`, `c i = 1/√(i+1)`, `ε i = c i + c (i+1)`. -/

namespace CE1D

noncomputable section

/-- horizontal amplitude `c i = 1/√(i+1)` -/
def c (i : ℕ) : ℝ := 1 / Real.sqrt ((i : ℝ) + 1)

/-- step sizes -/
def eps (i : ℕ) : ℝ := c i + c (i + 1)

/-- harmonic partial sums `H i = Σ_{k<i} 1/(k+1)` -/
def H (i : ℕ) : ℝ := ∑ k ∈ Finset.range i, (1 : ℝ) / ((k : ℝ) + 1)

lemma c_pos (i : ℕ) : 0 < c i := by unfold c; positivity

lemma eps_pos (i : ℕ) : 0 < eps i := by unfold eps; linarith [c_pos i, c_pos (i + 1)]

lemma c_sq (i : ℕ) : c i ^ 2 = 1 / ((i : ℝ) + 1) := by
  unfold c; rw [div_pow, Real.sq_sqrt (by positivity)]; ring

lemma one_le_sqrt_succ (i : ℕ) : (1 : ℝ) ≤ Real.sqrt ((i : ℝ) + 1) := by
  have h : Real.sqrt 1 ≤ Real.sqrt ((i : ℝ) + 1) :=
    Real.sqrt_le_sqrt (by have := (Nat.cast_nonneg i : (0 : ℝ) ≤ i); linarith)
  rw [Real.sqrt_one] at h; exact h

lemma c_le_one (i : ℕ) : c i ≤ 1 := by
  unfold c; rw [div_le_one (by positivity)]; exact one_le_sqrt_succ i

lemma inv_succ_le_c (i : ℕ) : 1 / ((i : ℝ) + 1) ≤ c i := by
  rw [← c_sq]; have := c_pos i; have := c_le_one i; nlinarith

lemma tendsto_c : Tendsto c atTop (𝓝 0) := by
  have h1 : Tendsto (fun i : ℕ => (i : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have h2 := (Real.tendsto_sqrt_atTop.comp h1).inv_tendsto_atTop
  refine h2.congr (fun i => ?_)
  simp [c, Function.comp]

lemma tendsto_eps : Tendsto eps atTop (𝓝 0) := by
  have h := tendsto_c.add (tendsto_c.comp (tendsto_add_atTop_nat 1))
  rw [add_zero] at h
  exact h

lemma tendsto_sum_eps : Tendsto (fun N => ∑ i ∈ Finset.range N, eps i) atTop atTop := by
  refine tendsto_atTop_mono (fun N => ?_) Real.tendsto_sum_range_one_div_nat_succ_atTop
  refine Finset.sum_le_sum (fun i _ => ?_)
  have := inv_succ_le_c i; have := c_pos (i + 1); unfold eps; linarith

lemma H_succ (i : ℕ) : H (i + 1) = H i + 1 / ((i : ℝ) + 1) := by
  unfold H; rw [Finset.sum_range_succ]

/-- vertical coordinate `b i = sin (κ H i)` -/
def b (κ : ℝ) (i : ℕ) : ℝ := Real.sin (κ * H i)

/-- horizontal coordinate `a i = (-1)^i c i` -/
def a (i : ℕ) : ℝ := (-1 : ℝ) ^ i * c i

def x (κ : ℝ) (i : ℕ) : EuclideanSpace ℝ (Fin 2) := !₂[a i, b κ i]

def t (κ : ℝ) (i : ℕ) : ℝ := (b κ i - b κ (i + 1)) / eps i

def v (κ : ℝ) (i : ℕ) : EuclideanSpace ℝ (Fin 2) := !₂[(-1 : ℝ) ^ i, t κ i]

lemma abs_b_sub (κ : ℝ) (hκ : 0 ≤ κ) (i : ℕ) : |b κ i - b κ (i + 1)| ≤ κ * c i ^ 2 := by
  unfold b
  refine (Real.abs_sin_sub_sin_le _ _).trans (le_of_eq ?_)
  rw [H_succ, c_sq, show κ * H i - κ * (H i + 1 / ((i : ℝ) + 1)) = -(κ * (1 / ((i : ℝ) + 1))) by ring,
    abs_neg, abs_of_nonneg (by positivity)]

lemma c_le_eps (i : ℕ) : c i ≤ eps i := by have := c_pos (i + 1); unfold eps; linarith

lemma abs_t_le (κ : ℝ) (hκ : 0 ≤ κ) (i : ℕ) : |t κ i| ≤ κ * c i := by
  unfold t
  rw [abs_div, abs_of_pos (eps_pos i), div_le_iff₀ (eps_pos i)]
  have h1 := abs_b_sub κ hκ i
  have h2 := c_le_eps i
  have h3 := c_pos i
  calc |b κ i - b κ (i + 1)| ≤ κ * c i ^ 2 := h1
    _ = κ * c i * c i := by ring
    _ ≤ κ * c i * eps i := by gcongr

lemma x_succ (κ : ℝ) (i : ℕ) : x κ (i + 1) = x κ i - eps i • v κ i := by
  have he := (eps_pos i).ne'
  ext j
  fin_cases j
  · simp [x, v, a, eps, pow_succ]; ring
  · simp [x, v, t]; field_simp; ring


/-! ### C1 rest: bounded range and non-convergence -/

lemma tendsto_H : Tendsto H atTop atTop := by
  show Tendsto (fun i : ℕ => ∑ k ∈ Finset.range i, (1 : ℝ) / ((k : ℝ) + 1)) atTop atTop
  exact Real.tendsto_sum_range_one_div_nat_succ_atTop

lemma exists_cross (s : ℕ → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (hs : ∀ i, s (i + 1) ≤ s i + δ)
    (htop : Tendsto s atTop atTop) (N : ℕ) (T : ℝ) (hT : s N ≤ T) :
    ∃ i ≥ N, T ≤ s i ∧ s i ≤ T + δ := by
  classical
  obtain ⟨M, hM⟩ := eventually_atTop.1 (htop.eventually_ge_atTop T)
  have ex : ∃ k, T ≤ s (N + k) := ⟨M, hM _ (by omega)⟩
  obtain ⟨k, hk⟩ : ∃ k, Nat.find ex = k := ⟨_, rfl⟩
  have hspec := Nat.find_spec ex
  rw [hk] at hspec
  cases k with
  | zero => exact ⟨N, le_rfl, by simpa using hspec, by linarith⟩
  | succ k =>
    have hmin := Nat.find_min ex (show k < Nat.find ex by omega)
    rw [not_le] at hmin
    refine ⟨N + (k + 1), by omega, hspec, ?_⟩
    have := hs (N + k)
    rw [show N + (k + 1) = N + k + 1 by omega]
    linarith

lemma sin_ge_half (φ : ℝ) (h1 : Real.pi / 6 ≤ φ) (h2 : φ ≤ Real.pi / 6 + 1) :
    1 / 2 ≤ Real.sin φ := by
  have hpi := Real.pi_gt_three
  rw [← Real.sin_pi_div_six]
  exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) h1

lemma sin_le_neg_half (φ : ℝ) (h1 : -(Real.pi / 2) ≤ φ) (h2 : φ ≤ -(Real.pi / 2) + 1) :
    Real.sin φ ≤ -(1 / 2) := by
  have hpi := Real.pi_gt_three
  have h6 : Real.sin (-(Real.pi / 6)) = -(1 / 2) := by rw [Real.sin_neg, Real.sin_pi_div_six]
  rw [← h6]
  exact Real.sin_le_sin_of_le_of_le_pi_div_two h1 (by linarith) (by linarith)

lemma frequently_sin_mem (κ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (φ0 : ℝ) :
    ∃ᶠ i in atTop, ∃ (m : ℕ) (φ : ℝ), φ0 ≤ φ ∧ φ ≤ φ0 + 1 ∧
      κ * H i = φ + (m : ℝ) * (2 * Real.pi) := by
  rw [frequently_atTop]
  intro N
  have hs : ∀ i, κ * H (i + 1) ≤ κ * H i + κ := by
    intro i
    rw [H_succ, mul_add]
    have h1 : 1 / ((i : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
    have := mul_le_of_le_one_right hκ0.le h1
    linarith
  have htop : Tendsto (fun i => κ * H i) atTop atTop := tendsto_H.const_mul_atTop hκ0
  have hpi := Real.pi_pos
  obtain ⟨m, hm⟩ := exists_nat_ge ((κ * H N - φ0) / (2 * Real.pi))
  have hT : κ * H N ≤ φ0 + (m : ℝ) * (2 * Real.pi) := by
    rw [div_le_iff₀ (by positivity)] at hm; linarith
  obtain ⟨i, hiN, h1, h2⟩ := exists_cross (fun i => κ * H i) κ hκ0.le hs htop N _ hT
  have h1' : φ0 + (m : ℝ) * (2 * Real.pi) ≤ κ * H i := h1
  have h2' : κ * H i ≤ φ0 + (m : ℝ) * (2 * Real.pi) + κ := h2
  exact ⟨i, hiN, m, κ * H i - (m : ℝ) * (2 * Real.pi), by linarith, by linarith, by ring⟩

lemma not_tendsto_b (κ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (L : ℝ) :
    ¬ Tendsto (b κ) atTop (𝓝 L) := by
  intro hL
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hL (1 / 4) (by norm_num)
  obtain ⟨i, hiN, m, φ, h1, h2, he⟩ :=
    frequently_atTop.1 (frequently_sin_mem κ hκ0 hκ1 (Real.pi / 6)) N
  obtain ⟨j, hjN, m', φ', h1', h2', he'⟩ :=
    frequently_atTop.1 (frequently_sin_mem κ hκ0 hκ1 (-(Real.pi / 2))) N
  have hb : 1 / 2 ≤ b κ i := by
    unfold b; rw [he, Real.sin_add_nat_mul_two_pi]; exact sin_ge_half φ h1 h2
  have hb' : b κ j ≤ -(1 / 2) := by
    unfold b; rw [he', Real.sin_add_nat_mul_two_pi]; exact sin_le_neg_half φ' h1' h2'
  have hi2 := hN i hiN
  have hj2 := hN j hjN
  rw [Real.dist_eq, abs_lt] at hi2 hj2
  linarith [hi2.1, hi2.2, hj2.1, hj2.2]

lemma proj_one_x (κ : ℝ) (i : ℕ) : EuclideanSpace.proj (1 : Fin 2) (x κ i) = b κ i := by
  simp [x]

lemma not_tendsto_x (κ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) :
    ¬ ∃ p, Tendsto (x κ) atTop (𝓝 p) := by
  rintro ⟨p, hp⟩
  have h1 := ((EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).continuous.tendsto p).comp hp
  refine not_tendsto_b κ hκ0 hκ1 _ (h1.congr (fun i => ?_))
  simp only [Function.comp]
  exact proj_one_x κ i

lemma abs_a_le (i : ℕ) : |a i| ≤ 1 := by
  unfold a
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos (c_pos i)]
  exact c_le_one i

lemma bounded_x (κ : ℝ) : Bornology.IsBounded (Set.range (x κ)) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨2, ?_⟩
  rintro _ ⟨i, rfl⟩
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.2 ⟨by norm_num, ?_⟩
  have ha := (sq_le_one_iff_abs_le_one (a i)).2 (abs_a_le i)
  have hb := (sq_le_one_iff_abs_le_one (b κ i)).2 (Real.abs_sin_le_one _)
  simp [Fin.sum_univ_two, x]
  nlinarith


/-! ### C2: the bump layer -/

/-- the fixed smooth bump on `E2`: `1` on `closedBall 0 (1/2)`, support `ball 0 1` -/
def χ : ContDiffBump (0 : EuclideanSpace ℝ (Fin 2)) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

lemma exists_M : ∃ M : ℝ, 0 ≤ M ∧ ∀ u, ‖fderiv ℝ χ u‖ ≤ M := by
  obtain ⟨C, hC⟩ := (χ.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    ((χ.contDiff : ContDiff ℝ 1 χ).continuous_fderiv one_ne_zero)
  exact ⟨max C 0, le_max_right _ _, fun u => (hC u).trans (le_max_left _ _)⟩

/-- consecutive gaps of `c` -/
def δ (i : ℕ) : ℝ := c i - c (i + 1)

/-- bump radii: half the smallest gap so far (antitone by construction) -/
def ρ (i : ℕ) : ℝ := (Finset.range (i + 1)).inf'
  (show (Finset.range (i + 1)).Nonempty from ⟨i, Finset.self_mem_range_succ i⟩) δ / 2

lemma c_succ_lt (i : ℕ) : c (i + 1) < c i := by
  unfold c
  apply one_div_lt_one_div_of_lt (by positivity)
  apply Real.sqrt_lt_sqrt (by positivity)
  push_cast; linarith

lemma ρ_pos (i : ℕ) : 0 < ρ i := by
  unfold ρ
  apply div_pos _ two_pos
  rw [Finset.lt_inf'_iff]
  intro k _
  unfold δ; linarith [c_succ_lt k]

lemma ρ_le_δ (i : ℕ) : ρ i ≤ (c i - c (i + 1)) / 2 := by
  unfold ρ
  exact div_le_div_of_nonneg_right (Finset.inf'_le _ (Finset.self_mem_range_succ i)) two_pos.le

lemma ρ_lt (i : ℕ) : ρ i < c i / 2 := by linarith [ρ_le_δ i, c_pos (i + 1)]

lemma ρ_anti {i j : ℕ} (h : i ≤ j) : ρ j ≤ ρ i := by
  unfold ρ
  apply div_le_div_of_nonneg_right _ two_pos.le
  exact Finset.inf'_mono δ (Finset.range_subset_range.2 (by omega)) _

lemma c_anti {i j : ℕ} (h : i ≤ j) : c j ≤ c i :=
  (antitone_nat_of_succ_le (fun n => (c_succ_lt n).le)) h

/-- the `i`-th bump: equals `t i * (y 1 - b i)` near `x i` -/
def B (κ : ℝ) (i : ℕ) (y : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  χ ((ρ i)⁻¹ • (y - x κ i)) * (t κ i * (EuclideanSpace.proj (1 : Fin 2) y - b κ i))

lemma B_contDiff (κ : ℝ) (i : ℕ) {n : ℕ∞} : ContDiff ℝ n (B κ i) := by
  unfold B
  exact (χ.contDiff.comp ((contDiff_id.sub contDiff_const).const_smul (ρ i)⁻¹)).mul
    (contDiff_const.mul
      ((EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.sub
        contDiff_const))

lemma B_eq_zero (κ : ℝ) (i : ℕ) (y : EuclideanSpace ℝ (Fin 2)) (h : ρ i ≤ ‖y - x κ i‖) :
    B κ i y = 0 := by
  unfold B
  have hz : χ ((ρ i)⁻¹ • (y - x κ i)) = 0 := by
    apply χ.zero_of_le_dist
    show (1 : ℝ) ≤ dist ((ρ i)⁻¹ • (y - x κ i)) 0
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (ρ_pos i),
      le_inv_mul_iff₀ (ρ_pos i), mul_one]
    exact h
  rw [hz, zero_mul]

lemma B_local (κ : ℝ) (i : ℕ) (y : EuclideanSpace ℝ (Fin 2)) (h : ‖y - x κ i‖ ≤ ρ i / 2) :
    B κ i y = t κ i * (EuclideanSpace.proj (1 : Fin 2) y - b κ i) := by
  unfold B
  have h1 : χ ((ρ i)⁻¹ • (y - x κ i)) = 1 := by
    apply χ.one_of_mem_closedBall
    show (ρ i)⁻¹ • (y - x κ i) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2)
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos (ρ_pos i), inv_mul_le_iff₀ (ρ_pos i)]
    linarith
  rw [h1, one_mul]

lemma abs_proj_sub_le (κ : ℝ) (i : ℕ) (y : EuclideanSpace ℝ (Fin 2)) :
    |EuclideanSpace.proj (1 : Fin 2) y - b κ i| ≤ ‖y - x κ i‖ := by
  have h := PiLp.norm_apply_le (y - x κ i) (1 : Fin 2)
  have he : EuclideanSpace.proj (1 : Fin 2) y - b κ i = (y - x κ i) 1 := by
    rw [← proj_one_x κ i]; simp
  rw [he, ← Real.norm_eq_abs]
  exact h

lemma norm_proj_le : ‖(EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun z => ?_)
  rw [one_mul]
  have h := PiLp.norm_apply_le z (1 : Fin 2)
  simpa using h

lemma B_hasFDerivAt (κ : ℝ) (i : ℕ) (y : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt (B κ i)
      (χ ((ρ i)⁻¹ • (y - x κ i)) •
          (t κ i • (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)) +
        (t κ i * (EuclideanSpace.proj (1 : Fin 2) y - b κ i)) •
          ((fderiv ℝ χ ((ρ i)⁻¹ • (y - x κ i))).comp
            ((ρ i)⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))))) y := by
  have hin : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 2) => (ρ i)⁻¹ • (y - x κ i))
      ((ρ i)⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))) y :=
    ((hasFDerivAt_id y).sub_const (x κ i)).const_smul (ρ i)⁻¹
  have hg := (((χ.contDiff : ContDiff ℝ 1 χ).differentiable one_ne_zero)
    ((ρ i)⁻¹ • (y - x κ i))).hasFDerivAt.comp y hin
  have hl : HasFDerivAt
      (fun y : EuclideanSpace ℝ (Fin 2) => t κ i * (EuclideanSpace.proj (1 : Fin 2) y - b κ i))
      (t κ i • (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)) y :=
    ((EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt.sub_const
      (b κ i)).const_mul (t κ i)
  exact hg.mul hl

lemma norm_fderiv_B_le (κ : ℝ) (M : ℝ) (hM : ∀ u, ‖fderiv ℝ χ u‖ ≤ M) (i : ℕ)
    (y : EuclideanSpace ℝ (Fin 2)) : ‖fderiv ℝ (B κ i) y‖ ≤ (1 + M) * |t κ i| := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  by_cases hy : ρ i < ‖y - x κ i‖
  · have hev : B κ i =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_const
        (continuous_id.sub continuous_const).norm).mem_nhds hy] with z hz
      exact B_eq_zero κ i z hz.le
    rw [hev.fderiv_eq]
    simp only [fderiv_const_apply, norm_zero]
    positivity
  · rw [not_lt] at hy
    rw [(B_hasFDerivAt κ i y).fderiv]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 : |χ ((ρ i)⁻¹ • (y - x κ i))| ≤ 1 := by
      rw [abs_of_nonneg χ.nonneg]; exact χ.le_one
    have hP := norm_proj_le
    have hℓ : |t κ i * (EuclideanSpace.proj (1 : Fin 2) y - b κ i)| ≤ |t κ i| * ρ i := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left ((abs_proj_sub_le κ i y).trans hy) (abs_nonneg _)
    have hD : ‖(fderiv ℝ χ ((ρ i)⁻¹ • (y - x κ i))).comp
        ((ρ i)⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)))‖ ≤ M * (ρ i)⁻¹ := by
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      refine mul_le_mul (hM _) ?_ (norm_nonneg _) hM0
      refine (norm_smul_le ((ρ i)⁻¹) (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)))).trans ?_
      rw [Real.norm_eq_abs, abs_inv, abs_of_pos (ρ_pos i)]
      calc (ρ i)⁻¹ * ‖ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))‖ ≤ (ρ i)⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le) (by have := ρ_pos i; positivity)
        _ = (ρ i)⁻¹ := mul_one _
    have hA : |χ ((ρ i)⁻¹ • (y - x κ i))| *
        (|t κ i| * ‖(EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)‖)
        ≤ 1 * (|t κ i| * 1) := by
      gcongr
    have hB := mul_le_mul hℓ hD (norm_nonneg _) (mul_nonneg (abs_nonneg _) (ρ_pos i).le)
    have hρ : |t κ i| * ρ i * (M * (ρ i)⁻¹) = M * |t κ i| := by
      field_simp [(ρ_pos i).ne']
    nlinarith

lemma abs_B_le (κ : ℝ) (i : ℕ) (y : EuclideanSpace ℝ (Fin 2)) : |B κ i y| ≤ |t κ i| * ρ i := by
  by_cases hy : ρ i ≤ ‖y - x κ i‖
  · rw [B_eq_zero κ i y hy, abs_zero]; exact mul_nonneg (abs_nonneg _) (ρ_pos i).le
  · rw [not_le] at hy
    unfold B
    rw [abs_mul, abs_mul, abs_of_nonneg χ.nonneg]
    have h1 := (abs_proj_sub_le κ i y).trans hy.le
    have h2 : χ ((ρ i)⁻¹ • (y - x κ i)) ≤ 1 := χ.le_one
    have h3 : 0 ≤ χ ((ρ i)⁻¹ • (y - x κ i)) := χ.nonneg
    have h4 := abs_nonneg (t κ i)
    have h5 := abs_nonneg (EuclideanSpace.proj (1 : Fin 2) y - b κ i)
    calc χ ((ρ i)⁻¹ • (y - x κ i)) * (|t κ i| * |EuclideanSpace.proj (1 : Fin 2) y - b κ i|)
        ≤ 1 * (|t κ i| * |EuclideanSpace.proj (1 : Fin 2) y - b κ i|) :=
          mul_le_mul_of_nonneg_right h2 (mul_nonneg h4 h5)
      _ ≤ |t κ i| * ρ i := by rw [one_mul]; exact mul_le_mul_of_nonneg_left h1 h4


/-! ### C2 rest: separation of the bumps, support localisation -/

lemma abs_proj_le (j : Fin 2) (w : EuclideanSpace ℝ (Fin 2)) :
    |EuclideanSpace.proj j w| ≤ ‖w‖ := by
  have h := PiLp.norm_apply_le w j
  simpa using h

lemma proj_zero_x (κ : ℝ) (i : ℕ) : EuclideanSpace.proj (0 : Fin 2) (x κ i) = a i := by
  simp [x]

lemma abs_proj0_sub_le (κ : ℝ) (i : ℕ) (y : EuclideanSpace ℝ (Fin 2)) :
    |EuclideanSpace.proj (0 : Fin 2) y - a i| ≤ ‖y - x κ i‖ := by
  have h := abs_proj_le 0 (y - x κ i)
  rwa [map_sub, proj_zero_x] at h

lemma abs_a (i : ℕ) : |a i| = c i := by
  unfold a
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos (c_pos i)]

lemma a_sep_lt {i j : ℕ} (hij : i < j) : ρ i + ρ j ≤ |a i - a j| := by
  have hρj := ρ_anti hij.le
  have hci := ρ_le_δ i
  have hcj : c j ≤ c (i + 1) := c_anti (by omega)
  have h1 := ρ_lt i
  have h2 := ρ_lt j
  have h3 := c_pos i
  have h4 := c_pos j
  unfold a
  rcases Nat.even_or_odd i with hi | hi <;> rcases Nat.even_or_odd j with hj | hj <;>
    simp only [hi.neg_one_pow, hj.neg_one_pow, one_mul, neg_one_mul] <;> rw [le_abs] <;>
    first | (left; linarith) | (right; linarith)

lemma a_sep {i j : ℕ} (hij : i ≠ j) : ρ i + ρ j ≤ |a i - a j| := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact a_sep_lt h
  · rw [add_comm, abs_sub_comm]; exact a_sep_lt h

lemma mem_supp {κ : ℝ} {i : ℕ} {y : EuclideanSpace ℝ (Fin 2)} (h : B κ i y ≠ 0) :
    ‖y - x κ i‖ < ρ i := by
  by_contra h'
  exact h (B_eq_zero κ i y (not_lt.1 h'))

lemma B_disjoint (κ : ℝ) {i j : ℕ} (hij : i ≠ j) (y : EuclideanSpace ℝ (Fin 2)) :
    B κ i y = 0 ∨ B κ j y = 0 := by
  by_contra hcon
  rw [not_or] at hcon
  have h1 := (abs_proj0_sub_le κ i y).trans_lt (mem_supp hcon.1)
  have h2 := (abs_proj0_sub_le κ j y).trans_lt (mem_supp hcon.2)
  have h3 := a_sep hij
  have h4 := abs_sub_le (a i) (EuclideanSpace.proj (0 : Fin 2) y) (a j)
  rw [abs_sub_comm (a i) (EuclideanSpace.proj (0 : Fin 2) y)] at h4
  linarith

lemma B_ne_zero_bounds {κ : ℝ} {i : ℕ} {y : EuclideanSpace ℝ (Fin 2)} (h : B κ i y ≠ 0) :
    c i / 2 < |EuclideanSpace.proj (0 : Fin 2) y| ∧
      |EuclideanSpace.proj (0 : Fin 2) y| < 3 * c i / 2 := by
  have h1 := (abs_proj0_sub_le κ i y).trans_lt (mem_supp h)
  have h3 := ρ_lt i
  have ha := abs_a i
  have e1 := abs_sub_abs_le_abs_sub (a i) (EuclideanSpace.proj (0 : Fin 2) y)
  have e2 := abs_sub_abs_le_abs_sub (EuclideanSpace.proj (0 : Fin 2) y) (a i)
  rw [abs_sub_comm (a i) (EuclideanSpace.proj (0 : Fin 2) y)] at e1
  constructor <;> linarith

/-! ### C3: the perturbation `F = ∑ᶠ i, B i` -/

def F (κ : ℝ) (y : EuclideanSpace ℝ (Fin 2)) : ℝ := ∑ᶠ i, B κ i y

lemma F_exists (κ : ℝ) (y : EuclideanSpace ℝ (Fin 2)) :
    ∃ i, F κ y = B κ i y ∧ ∀ j ≠ i, B κ j y = 0 := by
  by_cases h : ∃ i, B κ i y ≠ 0
  · obtain ⟨i, hi⟩ := h
    have hj : ∀ j ≠ i, B κ j y = 0 := by
      intro j hji
      rcases B_disjoint κ hji y with h' | h'
      · exact h'
      · exact absurd h' hi
    exact ⟨i, finsum_eq_single (fun j => B κ j y) i hj, hj⟩
  · push Not at h
    refine ⟨0, ?_, fun j _ => h j⟩
    unfold F
    rw [h 0]
    exact finsum_eq_zero_of_forall_eq_zero h

lemma abs_t_le_kappa (κ : ℝ) (hκ : 0 ≤ κ) (i : ℕ) : |t κ i| ≤ κ :=
  (abs_t_le κ hκ i).trans (by have := c_le_one i; nlinarith)

lemma B_lip (κ : ℝ) (hκ : 0 ≤ κ) (M : ℝ) (hM : ∀ u, ‖fderiv ℝ χ u‖ ≤ M) (i : ℕ)
    (y z : EuclideanSpace ℝ (Fin 2)) : |B κ i y - B κ i z| ≤ (1 + M) * κ * ‖y - z‖ := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hd : ContDiff ℝ 1 (B κ i) := B_contDiff κ i
  have h := convex_univ.norm_image_sub_le_of_norm_fderiv_le
    (fun w _ => hd.differentiable one_ne_zero w)
    (fun w _ => (norm_fderiv_B_le κ M hM i w).trans
      (mul_le_mul_of_nonneg_left (abs_t_le_kappa κ hκ i) (by linarith)))
    (Set.mem_univ z) (Set.mem_univ y)
  rwa [Real.norm_eq_abs] at h

lemma F_lip (κ : ℝ) (hκ : 0 ≤ κ) (M : ℝ) (hM : ∀ u, ‖fderiv ℝ χ u‖ ≤ M)
    (y z : EuclideanSpace ℝ (Fin 2)) : |F κ y - F κ z| ≤ 2 * ((1 + M) * κ) * ‖y - z‖ := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  obtain ⟨i, hi, hi'⟩ := F_exists κ y
  obtain ⟨j, hj, hj'⟩ := F_exists κ z
  have l1 := B_lip κ hκ M hM i y z
  have l2 := B_lip κ hκ M hM j y z
  have hn : 0 ≤ (1 + M) * κ * ‖y - z‖ := by positivity
  rw [hi, hj]
  by_cases hij : i = j
  · subst hij; linarith
  · have e1 : B κ i z = 0 := hj' i hij
    have e2 : B κ j y = 0 := hi' j (Ne.symm hij)
    have : B κ i y - B κ j z = (B κ i y - B κ i z) + (B κ j y - B κ j z) := by
      rw [e1, e2]; ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    linarith

lemma F_eq_sum (κ : ℝ) (y : EuclideanSpace ℝ (Fin 2)) (hy : EuclideanSpace.proj (0 : Fin 2) y ≠ 0) :
    ∃ N : ℕ, ∀ z ∈ Metric.ball y (|EuclideanSpace.proj (0 : Fin 2) y| / 2),
      F κ z = ∑ i ∈ Finset.range N, B κ i z := by
  have hpos : 0 < |EuclideanSpace.proj (0 : Fin 2) y| := abs_pos.2 hy
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (tendsto_c.eventually (gt_mem_nhds (show (0 : ℝ) < |EuclideanSpace.proj (0 : Fin 2) y| / 3 by
      positivity)))
  refine ⟨N, fun z hz => ?_⟩
  unfold F
  apply finsum_eq_sum_of_support_subset
  intro i hi
  rw [Function.mem_support] at hi
  rw [Finset.mem_coe, Finset.mem_range]
  by_contra hiN
  rw [not_lt] at hiN
  have hc := hN i hiN
  obtain ⟨h1, h2⟩ := B_ne_zero_bounds hi
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have e := abs_proj_le 0 (z - y)
  rw [map_sub] at e
  have e2 := abs_sub_abs_le_abs_sub (EuclideanSpace.proj (0 : Fin 2) y) (EuclideanSpace.proj (0 : Fin 2) z)
  rw [abs_sub_comm (EuclideanSpace.proj (0 : Fin 2) y)] at e2
  linarith

lemma F_contDiffOn (κ : ℝ) :
    ContDiffOn ℝ ∞ (F κ) {y | EuclideanSpace.proj (0 : Fin 2) y ≠ 0} := by
  intro y hy
  obtain ⟨N, hN⟩ := F_eq_sum κ y hy
  have hpos : 0 < |EuclideanSpace.proj (0 : Fin 2) y| := abs_pos.2 hy
  have hball : Metric.ball y (|EuclideanSpace.proj (0 : Fin 2) y| / 2) ∈ 𝓝 y :=
    Metric.ball_mem_nhds y (by positivity)
  have hsum : ContDiff ℝ ∞ (fun z => ∑ i ∈ Finset.range N, B κ i z) :=
    ContDiff.sum (fun i _ => B_contDiff κ i)
  exact (hsum.contDiffAt.congr_of_eventuallyEq
    (Filter.eventually_of_mem hball (fun z hz => hN z hz))).contDiffWithinAt


/-! ### C4: the function `f = |y 0| + F` -/

lemma F_lipschitzWith (κ : ℝ) (hκ : 0 ≤ κ) (M : ℝ) (hM : ∀ u, ‖fderiv ℝ χ u‖ ≤ M) :
    LipschitzWith (Real.toNNReal (2 * ((1 + M) * κ))) (F κ) :=
  LipschitzWith.of_dist_le' (fun y z => by
    rw [Real.dist_eq, dist_eq_norm]; exact F_lip κ hκ M hM y z)

def f (κ : ℝ) (y : EuclideanSpace ℝ (Fin 2)) : ℝ := |EuclideanSpace.proj (0 : Fin 2) y| + F κ y

lemma f_lip (κ : ℝ) (hκ : 0 ≤ κ) (M : ℝ) (hM : ∀ u, ‖fderiv ℝ χ u‖ ≤ M)
    (y z : EuclideanSpace ℝ (Fin 2)) :
    |f κ y - f κ z| ≤ (1 + 2 * ((1 + M) * κ)) * ‖y - z‖ := by
  unfold f
  have h1 := F_lip κ hκ M hM y z
  have h2 : abs (|EuclideanSpace.proj (0 : Fin 2) y| - |EuclideanSpace.proj (0 : Fin 2) z|) ≤ ‖y - z‖ := by
    refine (abs_abs_sub_abs_le_abs_sub _ _).trans ?_
    have := abs_proj_le 0 (y - z)
    rwa [map_sub] at this
  rw [show |EuclideanSpace.proj (0 : Fin 2) y| + F κ y - (|EuclideanSpace.proj (0 : Fin 2) z| + F κ z)
      = (|EuclideanSpace.proj (0 : Fin 2) y| - |EuclideanSpace.proj (0 : Fin 2) z|) + (F κ y - F κ z) by ring]
  refine (abs_add_le _ _).trans ?_
  linarith

lemma f_lipschitzWith (κ : ℝ) (hκ : 0 ≤ κ) (M : ℝ) (hM : ∀ u, ‖fderiv ℝ χ u‖ ≤ M) :
    LipschitzWith (Real.toNNReal (1 + 2 * ((1 + M) * κ))) (f κ) :=
  LipschitzWith.of_dist_le' (fun y z => by
    rw [Real.dist_eq, dist_eq_norm]; exact f_lip κ hκ M hM y z)

lemma isOpen_line_compl :
    IsOpen {y : EuclideanSpace ℝ (Fin 2) | EuclideanSpace.proj (0 : Fin 2) y ≠ 0} :=
  isOpen_ne_fun (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).continuous
    continuous_const

lemma f_contDiffOn (κ : ℝ) :
    ContDiffOn ℝ ∞ (f κ) {y | EuclideanSpace.proj (0 : Fin 2) y ≠ 0} := by
  intro y hy
  have h1 : ContDiffAt ℝ ∞ (fun y : EuclideanSpace ℝ (Fin 2) => |EuclideanSpace.proj (0 : Fin 2) y|) y :=
    (contDiffAt_abs hy).comp y
      (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.contDiffAt
  show ContDiffWithinAt ℝ ∞
    (fun y => |EuclideanSpace.proj (0 : Fin 2) y| + F κ y) {y | EuclideanSpace.proj (0 : Fin 2) y ≠ 0} y
  exact h1.contDiffWithinAt.add (F_contDiffOn κ y hy)

lemma ball_sub (κ : ℝ) (i : ℕ) :
    Metric.ball (x κ i) (c i / 2) ⊆ {y | EuclideanSpace.proj (0 : Fin 2) y ≠ 0} := by
  intro y hy
  rw [Metric.mem_ball, dist_eq_norm] at hy
  show EuclideanSpace.proj (0 : Fin 2) y ≠ 0
  intro h0
  have := abs_proj0_sub_le κ i y
  rw [h0, zero_sub, abs_neg, abs_a] at this
  linarith [c_pos i]

lemma f_contDiffOn_ball (κ : ℝ) (i : ℕ) : ContDiffOn ℝ ∞ (f κ) (Metric.ball (x κ i) (c i / 2)) :=
  (f_contDiffOn κ).mono (ball_sub κ i)

lemma norm_proj0_ge : 1 ≤ ‖(EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)‖ := by
  have h := ContinuousLinearMap.le_opNorm
    (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) (EuclideanSpace.single 0 1)
  simpa using h

lemma hasFDerivAt_abs_proj0 (y : EuclideanSpace ℝ (Fin 2)) (hy : EuclideanSpace.proj (0 : Fin 2) y ≠ 0) :
    HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 2) => |EuclideanSpace.proj (0 : Fin 2) y|)
      ((SignType.sign (EuclideanSpace.proj (0 : Fin 2) y) : ℝ) •
        (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)) y :=
  (hasDerivAt_abs hy).comp_hasFDerivAt y
    (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt

lemma fderiv_f_bound (κ : ℝ) (hκ : 0 ≤ κ) (M : ℝ) (hM : ∀ u, ‖fderiv ℝ χ u‖ ≤ M)
    (hK : 2 * ((1 + M) * κ) ≤ 1 / 2) (y : EuclideanSpace ℝ (Fin 2))
    (hy : EuclideanSpace.proj (0 : Fin 2) y ≠ 0) :
    DifferentiableAt ℝ (f κ) y ∧ 1 / 2 ≤ ‖fderiv ℝ (f κ) y‖ := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hFd : DifferentiableAt ℝ (F κ) y :=
    ((F_contDiffOn κ).contDiffAt (isOpen_line_compl.mem_nhds hy)).differentiableAt (by simp)
  have hA := hasFDerivAt_abs_proj0 y hy
  have hf : HasFDerivAt (f κ) (((SignType.sign (EuclideanSpace.proj (0 : Fin 2) y) : ℝ) •
        (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)) + fderiv ℝ (F κ) y) y :=
    hA.add hFd.hasFDerivAt
  refine ⟨hf.differentiableAt, ?_⟩
  rw [hf.fderiv]
  have hD : ‖fderiv ℝ (F κ) y‖ ≤ 2 * ((1 + M) * κ) := by
    have := norm_fderiv_le_of_lipschitz ℝ (x₀ := y) (F_lipschitzWith κ hκ M hM)
    rwa [Real.coe_toNNReal _ (by positivity)] at this
  have hAn : 1 ≤ ‖(SignType.sign (EuclideanSpace.proj (0 : Fin 2) y) : ℝ) •
      (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)‖ := by
    have hs : ‖(SignType.sign (EuclideanSpace.proj (0 : Fin 2) y) : ℝ)‖ = 1 := by
      rcases lt_or_gt_of_ne hy with h | h
      · rw [sign_neg h]; simp
      · rw [sign_pos h]; simp
    rw [norm_smul, hs, one_mul]
    exact norm_proj0_ge
  have h3 := norm_sub_le ((SignType.sign (EuclideanSpace.proj (0 : Fin 2) y) : ℝ) •
      (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) + fderiv ℝ (F κ) y)
    (fderiv ℝ (F κ) y)
  rw [add_sub_cancel_right] at h3
  linarith

lemma B_other_zero (κ : ℝ) {i j : ℕ} (hji : j ≠ i) (y : EuclideanSpace ℝ (Fin 2))
    (h : ‖y - x κ i‖ < ρ i) : B κ j y = 0 := by
  by_contra hne
  have h1 := (abs_proj0_sub_le κ i y).trans_lt h
  have h2 := (abs_proj0_sub_le κ j y).trans_lt (mem_supp hne)
  have h3 := a_sep hji
  have h4 := abs_sub_le (a j) (EuclideanSpace.proj (0 : Fin 2) y) (a i)
  rw [abs_sub_comm (a j) (EuclideanSpace.proj (0 : Fin 2) y)] at h4
  linarith

lemma f_local (κ : ℝ) (i : ℕ) (y : EuclideanSpace ℝ (Fin 2)) (h : ‖y - x κ i‖ < ρ i / 2) :
    f κ y = (-1 : ℝ) ^ i * EuclideanSpace.proj (0 : Fin 2) y +
      t κ i * (EuclideanSpace.proj (1 : Fin 2) y - b κ i) := by
  unfold f
  have hρ := ρ_pos i
  have hF : F κ y = B κ i y :=
    finsum_eq_single (fun j => B κ j y) i (fun j hj => B_other_zero κ hj y (by linarith))
  rw [hF, B_local κ i y h.le]
  congr 1
  have h1 := (abs_proj0_sub_le κ i y).trans_lt (show ‖y - x κ i‖ < ρ i by linarith)
  have h2 := ρ_lt i
  have h3 := c_pos i
  unfold a at h1
  rcases Nat.even_or_odd i with hi | hi <;> simp only [hi.neg_one_pow, one_mul, neg_one_mul] at h1 ⊢ <;>
    rw [abs_lt] at h1
  · rw [abs_of_pos (by linarith)]
  · rw [abs_of_neg (by linarith)]

/-! ### C4 end: gradients -/

lemma toDual_symm_apply' (L : StrongDual ℝ (EuclideanSpace ℝ (Fin 2))) (j : Fin 2) :
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 2))).symm L j =
      L (EuclideanSpace.single j (1 : ℝ)) := by
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 2))
    (x := EuclideanSpace.single j (1 : ℝ)) (y := L)
  rw [← h, real_inner_comm, EuclideanSpace.inner_single_left]
  simp

lemma gradient_apply' (g : EuclideanSpace ℝ (Fin 2) → ℝ) (z : EuclideanSpace ℝ (Fin 2)) (j : Fin 2) :
    gradient g z j = fderiv ℝ g z (EuclideanSpace.single j (1 : ℝ)) :=
  toDual_symm_apply' _ j

lemma norm_gradient' (g : EuclideanSpace ℝ (Fin 2) → ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    ‖gradient g z‖ = ‖fderiv ℝ g z‖ := by
  simp [gradient]

lemma hasFDerivAt_f_x (κ : ℝ) (i : ℕ) :
    HasFDerivAt (f κ) ((-1 : ℝ) ^ i • (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) +
      t κ i • (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)) (x κ i) := by
  have hL : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 2) => (-1 : ℝ) ^ i * EuclideanSpace.proj (0 : Fin 2) y +
      t κ i * (EuclideanSpace.proj (1 : Fin 2) y - b κ i))
      ((-1 : ℝ) ^ i • (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) +
      t κ i • (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)) (x κ i) :=
    ((EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt.const_mul _).add
      (((EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt.sub_const
        (b κ i)).const_mul (t κ i))
  refine hL.congr_of_eventuallyEq ?_
  filter_upwards [Metric.ball_mem_nhds (x κ i) (half_pos (ρ_pos i))] with y hy
  exact f_local κ i y (by rwa [Metric.mem_ball, dist_eq_norm] at hy)

lemma gradient_f_x (κ : ℝ) (i : ℕ) : gradient (f κ) (x κ i) = v κ i := by
  ext j
  rw [gradient_apply', (hasFDerivAt_f_x κ i).fderiv]
  fin_cases j <;> simp [v]

/-! ### C5: Clarke subdifferential -/

lemma F_line (κ : ℝ) (y : EuclideanSpace ℝ (Fin 2)) (hy : EuclideanSpace.proj (0 : Fin 2) y = 0) :
    F κ y = 0 := by
  obtain ⟨i, hi, -⟩ := F_exists κ y
  rw [hi]
  by_contra h
  have h1 := (B_ne_zero_bounds h).1
  rw [hy, abs_zero] at h1
  linarith [c_pos i]

lemma f_line (κ : ℝ) (y : EuclideanSpace ℝ (Fin 2)) (hy : EuclideanSpace.proj (0 : Fin 2) y = 0) :
    f κ y = 0 := by
  unfold f; rw [hy, F_line κ y hy]; simp

lemma B_lip_t (κ : ℝ) (M : ℝ) (hM : ∀ u, ‖fderiv ℝ χ u‖ ≤ M) (i : ℕ)
    (y z : EuclideanSpace ℝ (Fin 2)) : |B κ i y - B κ i z| ≤ (1 + M) * |t κ i| * ‖y - z‖ := by
  have hd : ContDiff ℝ 1 (B κ i) := B_contDiff κ i
  have h := convex_univ.norm_image_sub_le_of_norm_fderiv_le
    (fun w _ => hd.differentiable one_ne_zero w)
    (fun w _ => norm_fderiv_B_le κ M hM i w) (Set.mem_univ z) (Set.mem_univ y)
  rwa [Real.norm_eq_abs] at h

lemma B_lip_near (κ : ℝ) (hκ : 0 ≤ κ) (M : ℝ) (hM : ∀ u, ‖fderiv ℝ χ u‖ ≤ M) (i : ℕ)
    (y z : EuclideanSpace ℝ (Fin 2)) : |B κ i y - B κ i z| ≤
      (1 + M) * (2 * κ * (|EuclideanSpace.proj (0 : Fin 2) y| + |EuclideanSpace.proj (0 : Fin 2) z|)) *
        ‖y - z‖ := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hy0 := abs_nonneg (EuclideanSpace.proj (0 : Fin 2) y)
  have hz0 := abs_nonneg (EuclideanSpace.proj (0 : Fin 2) z)
  by_cases h : B κ i y = 0 ∧ B κ i z = 0
  · rw [h.1, h.2, sub_zero, abs_zero]
    exact mul_nonneg (mul_nonneg (by linarith) (by positivity)) (norm_nonneg _)
  · have hc : c i ≤ 2 * (|EuclideanSpace.proj (0 : Fin 2) y| + |EuclideanSpace.proj (0 : Fin 2) z|) := by
      rcases not_and_or.1 h with h' | h'
      · have := (B_ne_zero_bounds h').1; linarith
      · have := (B_ne_zero_bounds h').1; linarith
    have ht : |t κ i| ≤ 2 * κ * (|EuclideanSpace.proj (0 : Fin 2) y| +
        |EuclideanSpace.proj (0 : Fin 2) z|) := by
      have := abs_t_le κ hκ i
      nlinarith
    refine (B_lip_t κ M hM i y z).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (by linarith)) (norm_nonneg _)

lemma F_lip_near (κ : ℝ) (hκ : 0 ≤ κ) (M : ℝ) (hM : ∀ u, ‖fderiv ℝ χ u‖ ≤ M)
    (y z : EuclideanSpace ℝ (Fin 2)) : |F κ y - F κ z| ≤
      2 * ((1 + M) * (2 * κ * (|EuclideanSpace.proj (0 : Fin 2) y| + |EuclideanSpace.proj (0 : Fin 2) z|))) *
        ‖y - z‖ := by
  obtain ⟨i, hi, hi'⟩ := F_exists κ y
  obtain ⟨j, hj, hj'⟩ := F_exists κ z
  have l1 := B_lip_near κ hκ M hM i y z
  have l2 := B_lip_near κ hκ M hM j y z
  have hn := (abs_nonneg _).trans l1
  rw [hi, hj]
  by_cases hij : i = j
  · subst hij; linarith
  · have e1 : B κ i z = 0 := hj' i hij
    have e2 : B κ j y = 0 := hi' j (Ne.symm hij)
    have : B κ i y - B κ j z = (B κ i y - B κ i z) + (B κ j y - B κ j z) := by
      rw [e1, e2]; ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    linarith

lemma norm_fderiv_F_near (κ : ℝ) (hκ : 0 ≤ κ) (M : ℝ) (hM : ∀ u, ‖fderiv ℝ χ u‖ ≤ M)
    (z : EuclideanSpace ℝ (Fin 2)) (hz : EuclideanSpace.proj (0 : Fin 2) z ≠ 0) :
    ‖fderiv ℝ (F κ) z‖ ≤ 12 * ((1 + M) * κ) * |EuclideanSpace.proj (0 : Fin 2) z| := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hk : 0 ≤ (1 + M) * κ := mul_nonneg (by linarith) hκ
  have hFd : DifferentiableAt ℝ (F κ) z :=
    ((F_contDiffOn κ).contDiffAt (isOpen_line_compl.mem_nhds hz)).differentiableAt (by simp)
  refine hFd.hasFDerivAt.le_of_lip' (mul_nonneg (by linarith) (abs_nonneg _)) ?_
  filter_upwards [Metric.ball_mem_nhds z (abs_pos.2 hz)] with w hw
  rw [Metric.mem_ball, dist_eq_norm] at hw
  have h2 := abs_proj_le 0 (w - z)
  rw [map_sub] at h2
  have h3 := abs_sub_abs_le_abs_sub (EuclideanSpace.proj (0 : Fin 2) w) (EuclideanSpace.proj (0 : Fin 2) z)
  have h1 : |EuclideanSpace.proj (0 : Fin 2) w| ≤ 2 * |EuclideanSpace.proj (0 : Fin 2) z| := by linarith
  rw [Real.norm_eq_abs]
  refine (F_lip_near κ hκ M hM w z).trans ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  nlinarith [mul_nonneg hk (sub_nonneg.2 h1)]

lemma grad_f_sub (κ : ℝ) (z : EuclideanSpace ℝ (Fin 2)) (hz : EuclideanSpace.proj (0 : Fin 2) z ≠ 0) :
    gradient (f κ) z - (SignType.sign (EuclideanSpace.proj (0 : Fin 2) z) : ℝ) •
      EuclideanSpace.single (0 : Fin 2) (1 : ℝ) = gradient (F κ) z := by
  have hFd : DifferentiableAt ℝ (F κ) z :=
    ((F_contDiffOn κ).contDiffAt (isOpen_line_compl.mem_nhds hz)).differentiableAt (by simp)
  have hf : HasFDerivAt (f κ) (((SignType.sign (EuclideanSpace.proj (0 : Fin 2) z) : ℝ) •
        (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)) + fderiv ℝ (F κ) z) z :=
    (hasFDerivAt_abs_proj0 z hz).add hFd.hasFDerivAt
  ext j
  rw [PiLp.sub_apply, gradient_apply', gradient_apply', hf.fderiv]
  fin_cases j <;> simp

lemma grad_f_close (κ : ℝ) (hκ : 0 ≤ κ) (M : ℝ) (hM : ∀ u, ‖fderiv ℝ χ u‖ ≤ M)
    (z : EuclideanSpace ℝ (Fin 2)) (hz : EuclideanSpace.proj (0 : Fin 2) z ≠ 0) :
    ‖gradient (f κ) z - (SignType.sign (EuclideanSpace.proj (0 : Fin 2) z) : ℝ) •
      EuclideanSpace.single (0 : Fin 2) (1 : ℝ)‖ ≤
        12 * ((1 + M) * κ) * |EuclideanSpace.proj (0 : Fin 2) z| := by
  rw [grad_f_sub κ z hz, norm_gradient']
  exact norm_fderiv_F_near κ hκ M hM z hz

lemma grad_f_one (κ : ℝ) (hκ : 0 ≤ κ) (M : ℝ) (hM : ∀ u, ‖fderiv ℝ χ u‖ ≤ M)
    (z : EuclideanSpace ℝ (Fin 2)) (hz : EuclideanSpace.proj (0 : Fin 2) z ≠ 0) :
    |gradient (f κ) z 1| ≤ 12 * ((1 + M) * κ) * |EuclideanSpace.proj (0 : Fin 2) z| := by
  have h1 := abs_proj_le 1 (gradient (f κ) z - (SignType.sign (EuclideanSpace.proj (0 : Fin 2) z) : ℝ) •
      EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
  have h2 := grad_f_close κ hκ M hM z hz
  have h3 : EuclideanSpace.proj (1 : Fin 2) (gradient (f κ) z - (SignType.sign
      (EuclideanSpace.proj (0 : Fin 2) z) : ℝ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) =
      gradient (f κ) z 1 := by simp
  rw [h3] at h1
  linarith

lemma f_ge_line (κ : ℝ) (hκ : 0 ≤ κ) (M : ℝ) (hM : ∀ u, ‖fderiv ℝ χ u‖ ≤ M)
    (hK : 2 * ((1 + M) * κ) ≤ 1 / 2) (y : EuclideanSpace ℝ (Fin 2))
    (hy : EuclideanSpace.proj (0 : Fin 2) y = 0) (s : ℝ) :
    |s| / 2 ≤ f κ (y + s • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) := by
  have h1 := F_lip κ hκ M hM (y + s • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) y
  rw [F_line κ y hy, add_sub_cancel_left, norm_smul, PiLp.norm_single, norm_one, mul_one,
    Real.norm_eq_abs, sub_zero] at h1
  have h2 : EuclideanSpace.proj (0 : Fin 2) (y + s • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) = s := by
    rw [map_add, map_smul, hy]; simp
  unfold f; rw [h2]
  have h3 := (abs_le.1 h1).1
  have h4 := mul_le_mul_of_nonneg_right hK (abs_nonneg s)
  linarith

lemma not_diff_line (κ : ℝ) (hκ : 0 ≤ κ) (M : ℝ) (hM : ∀ u, ‖fderiv ℝ χ u‖ ≤ M)
    (hK : 2 * ((1 + M) * κ) ≤ 1 / 2) (y : EuclideanSpace ℝ (Fin 2))
    (hy : EuclideanSpace.proj (0 : Fin 2) y = 0) : ¬ DifferentiableAt ℝ (f κ) y := by
  intro hd
  have hγ : HasDerivAt (fun s : ℝ => y + s • EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
      (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))).const_add y
  have hg : HasDerivAt (fun s : ℝ => f κ (y + s • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)))
      (fderiv ℝ (f κ) y (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))) 0 :=
    hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ (by simp)
  have hf0 := f_line κ y hy
  have hmin1 : IsLocalMin (fun s : ℝ => f κ (y + s • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) - s / 2) 0 :=
    Filter.Eventually.of_forall (fun s => by
      have h1 := f_ge_line κ hκ M hM hK y hy s
      have h2 := le_abs_self s
      show f κ (y + (0 : ℝ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) - 0 / 2 ≤ _
      rw [zero_smul, add_zero, hf0]
      linarith)
  have hmin2 : IsLocalMin (fun s : ℝ => f κ (y + s • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) + s / 2) 0 :=
    Filter.Eventually.of_forall (fun s => by
      have h1 := f_ge_line κ hκ M hM hK y hy s
      have h2 := neg_abs_le s
      show f κ (y + (0 : ℝ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) + 0 / 2 ≤ _
      rw [zero_smul, add_zero, hf0]
      linarith)
  have d1 := hmin1.hasDerivAt_eq_zero (hg.sub ((hasDerivAt_id' (0 : ℝ)).div_const 2))
  have d2 := hmin2.hasDerivAt_eq_zero (hg.add ((hasDerivAt_id' (0 : ℝ)).div_const 2))
  linarith

lemma eq_of_clusterPt_nhds {a b : ℝ} (h : ClusterPt a (𝓝 b)) : a = b := by
  by_contra hne
  exact Filter.NeBot.ne h (disjoint_iff.1 (disjoint_nhds_nhds.2 hne))

lemma grad_continuousAt (κ : ℝ) (z : EuclideanSpace ℝ (Fin 2)) (hz : EuclideanSpace.proj (0 : Fin 2) z ≠ 0) :
    ContinuousAt (gradient (f κ)) z := by
  have hc : ContDiffAt ℝ ∞ (f κ) z := (f_contDiffOn κ).contDiffAt (isOpen_line_compl.mem_nhds hz)
  have h2 : ContinuousAt (fderiv ℝ (f κ)) z := (hc.fderiv_right (m := 0) (by simp)).continuousAt
  show ContinuousAt (fun w => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 2))).symm
    (fderiv ℝ (f κ) w)) z
  exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 2))).symm.continuous.continuousAt.comp h2

lemma diff_off (κ : ℝ) (z : EuclideanSpace ℝ (Fin 2)) (hz : EuclideanSpace.proj (0 : Fin 2) z ≠ 0) :
    DifferentiableAt ℝ (f κ) z :=
  ((f_contDiffOn κ).contDiffAt (isOpen_line_compl.mem_nhds hz)).differentiableAt (by simp)

lemma clarke_off (κ : ℝ) (z : EuclideanSpace ℝ (Fin 2)) (hz : EuclideanSpace.proj (0 : Fin 2) z ≠ 0) :
    PathoSubgrad.Circle.clarkeSubdiff (f κ) z = {gradient (f κ) z} := by
  have hAG : ShorNonsmooth.AlmostDiff.almostGradients (f κ) z = {gradient (f κ) z} := by
    ext g
    constructor
    · rintro ⟨xs, hxs, -, hcl⟩
      have ht : Tendsto (fun k => gradient (f κ) (xs k)) atTop (𝓝 (gradient (f κ) z)) :=
        (grad_continuousAt κ z hz).tendsto.comp hxs
      by_contra hne
      exact Filter.NeBot.ne hcl (eq_bot_mono (inf_le_inf_left _ ht)
        (disjoint_iff.1 (disjoint_nhds_nhds.2 hne)))
    · rintro rfl
      exact ⟨fun _ => z, tendsto_const_nhds, fun _ => diff_off κ z hz, tendsto_const_nhds.mapClusterPt⟩
  unfold PathoSubgrad.Circle.clarkeSubdiff
  rw [hAG, convexHull_singleton]

lemma AG_line_sub (κ : ℝ) (hκ : 0 ≤ κ) (M : ℝ) (hM : ∀ u, ‖fderiv ℝ χ u‖ ≤ M)
    (hK : 2 * ((1 + M) * κ) ≤ 1 / 2) (y : EuclideanSpace ℝ (Fin 2))
    (hy : EuclideanSpace.proj (0 : Fin 2) y = 0) :
    ShorNonsmooth.AlmostDiff.almostGradients (f κ) y ⊆ {w | w 1 = 0} := by
  rintro g ⟨xs, hxs, hd, hcl⟩
  have hoff : ∀ k, EuclideanSpace.proj (0 : Fin 2) (xs k) ≠ 0 := fun k h0 =>
    not_diff_line κ hκ M hM hK (xs k) h0 (hd k)
  have hp : Tendsto (fun k => EuclideanSpace.proj (0 : Fin 2) (xs k)) atTop (𝓝 0) := by
    have := ((EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).continuous.tendsto y).comp hxs
    rwa [hy] at this
  have hu : Tendsto (fun k => gradient (f κ) (xs k) 1) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun k =>
      12 * ((1 + M) * κ) * |EuclideanSpace.proj (0 : Fin 2) (xs k)|) (fun k => ?_) ?_
    · rw [Real.norm_eq_abs]; exact grad_f_one κ hκ M hM (xs k) (hoff k)
    · simpa using (hp.abs.const_mul (12 * ((1 + M) * κ)))
  have hc := ClusterPt.map hcl
    (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).continuous.continuousAt
    (tendsto_map'_iff.2 hu)
  exact eq_of_clusterPt_nhds hc

lemma AG_line_mem (κ : ℝ) (hκ : 0 ≤ κ) (M : ℝ) (hM : ∀ u, ‖fderiv ℝ χ u‖ ≤ M)
    (y : EuclideanSpace ℝ (Fin 2)) (hy : EuclideanSpace.proj (0 : Fin 2) y = 0) (σ : ℝ)
    (hσ0 : σ ≠ 0) (hσ : ∀ k : ℕ, (SignType.sign (σ * (1 / ((k : ℝ) + 1))) : ℝ) = σ) :
    σ • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) ∈ ShorNonsmooth.AlmostDiff.almostGradients (f κ) y := by
  set xs : ℕ → EuclideanSpace ℝ (Fin 2) := fun k =>
    y + (σ * (1 / ((k : ℝ) + 1))) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) with hxs_def
  have hp : ∀ k, EuclideanSpace.proj (0 : Fin 2) (xs k) = σ * (1 / ((k : ℝ) + 1)) := by
    intro k
    simp only [hxs_def]
    rw [map_add, map_smul, hy]; simp
  have hne : ∀ k, EuclideanSpace.proj (0 : Fin 2) (xs k) ≠ 0 := by
    intro k; rw [hp k]; positivity
  have h0 : Tendsto (fun k : ℕ => σ * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul σ
  refine ⟨xs, ?_, fun k => diff_off κ (xs k) (hne k), ?_⟩
  · simpa [hxs_def] using (tendsto_const_nhds (x := y)).add (h0.smul_const
      (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)))
  · refine Filter.Tendsto.mapClusterPt ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (g := fun k : ℕ =>
      12 * ((1 + M) * κ) * |σ * (1 / ((k : ℝ) + 1))|) (fun k => ?_) (fun k => ?_) ?_
    · exact norm_nonneg _
    · have := grad_f_close κ hκ M hM (xs k) (hne k)
      rwa [hp k, hσ k] at this
    · simpa using (h0.abs.const_mul (12 * ((1 + M) * κ)))

lemma critSet_iff (κ : ℝ) (hκ : 0 ≤ κ) (M : ℝ) (hM : ∀ u, ‖fderiv ℝ χ u‖ ≤ M)
    (hK : 2 * ((1 + M) * κ) ≤ 1 / 2) (y : EuclideanSpace ℝ (Fin 2)) :
    y ∈ PathoSubgrad.Circle.critSet (f κ) ↔ EuclideanSpace.proj (0 : Fin 2) y = 0 := by
  constructor
  · intro hc
    by_contra hy
    unfold PathoSubgrad.Circle.critSet at hc
    rw [Set.mem_ofPred_eq, clarke_off κ y hy, Set.mem_singleton_iff] at hc
    have h := (fderiv_f_bound κ hκ M hM hK y hy).2
    rw [← norm_gradient', ← hc, norm_zero] at h
    linarith
  · intro hy
    have h1 := AG_line_mem κ hκ M hM y hy 1 one_ne_zero (fun k => by
      rw [one_mul, sign_pos (by positivity)]; simp)
    have h2 := AG_line_mem κ hκ M hM y hy (-1) (by norm_num) (fun k => by
      rw [sign_neg (by
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith)]; simp)
    have h3 := convex_convexHull ℝ (ShorNonsmooth.AlmostDiff.almostGradients (f κ) y)
      (subset_convexHull ℝ _ h1) (subset_convexHull ℝ _ h2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    unfold PathoSubgrad.Circle.critSet PathoSubgrad.Circle.clarkeSubdiff
    rw [Set.mem_ofPred_eq]
    convert h3 using 1
    rw [neg_smul, one_smul, smul_neg, add_neg_cancel]

lemma clarke_line_sub (κ : ℝ) (hκ : 0 ≤ κ) (M : ℝ) (hM : ∀ u, ‖fderiv ℝ χ u‖ ≤ M)
    (hK : 2 * ((1 + M) * κ) ≤ 1 / 2) (y : EuclideanSpace ℝ (Fin 2))
    (hy : EuclideanSpace.proj (0 : Fin 2) y = 0) :
    PathoSubgrad.Circle.clarkeSubdiff (f κ) y ⊆ {w | w 1 = 0} := by
  refine convexHull_min (AG_line_sub κ hκ M hM hK y hy) ?_
  have : {w : EuclideanSpace ℝ (Fin 2) | w 1 = 0} =
      (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) ⁻¹' {0} := by
    ext w; simp
  rw [this]
  exact (convex_singleton 0).linear_preimage (EuclideanSpace.proj (1 : Fin 2)).toLinearMap

lemma v_mem_clarke (κ : ℝ) (i : ℕ) : v κ i ∈ PathoSubgrad.Circle.clarkeSubdiff (f κ) (x κ i) := by
  rw [← gradient_f_x]
  exact subset_convexHull ℝ _ ⟨fun _ => x κ i, tendsto_const_nhds,
    fun _ => (hasFDerivAt_f_x κ i).differentiableAt, tendsto_const_nhds.mapClusterPt⟩

/-! ### C6: path differentiability, weak Sard, subgradient sequence -/

lemma deriv_zero_of_acc {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {g : ℝ → E'} {g' : E'}
    {t : ℝ} {T : Set ℝ} (hg : HasDerivAt g g' t) (hT : ∀ s ∈ T, g s = g t)
    (hne : (𝓝[T ∩ Set.Ioi t] t).NeBot) : g' = 0 := by
  have h1 := (hasDerivAt_iff_tendsto_slope.1 hg).mono_left
    (nhdsWithin_mono t (fun s (hs : s ∈ T ∩ Set.Ioi t) => Set.mem_compl_singleton_iff.2 (ne_of_gt hs.2)))
  have h2 : Tendsto (slope g t) (𝓝[T ∩ Set.Ioi t] t) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    show (0 : E') = slope g t s
    rw [slope_def_module, hT s hs.1, sub_self, smul_zero]
  exact tendsto_nhds_unique h1 h2

lemma pathDiff (κ : ℝ) (hκ : 0 ≤ κ) (M : ℝ) (hM : ∀ u, ‖fderiv ℝ χ u‖ ≤ M)
    (hK : 2 * ((1 + M) * κ) ≤ 1 / 2) : PathoSubgrad.Circle.IsPathDifferentiable (f κ) := by
  have hL := f_lipschitzWith κ hκ M hM
  refine ⟨hL.locallyLipschitz, ?_⟩
  rintro γ ⟨K, hγ⟩
  set T : Set ℝ := {s : ℝ | EuclideanSpace.proj (0 : Fin 2) (γ s) = 0} with hT
  have hN : ({s ∈ T | 𝓝[T ∩ Set.Ioi s] s = ⊥} : Set ℝ).Countable :=
    countable_setOfPred_isolated_right_within
  have h1 : ∀ᵐ s ∂MeasureTheory.volume, DifferentiableAt ℝ (f κ ∘ γ) s :=
    (hL.comp hγ).ae_differentiableAt
  have h2 : ∀ᵐ s ∂MeasureTheory.volume, DifferentiableAt ℝ γ s := hγ.ae_differentiableAt
  have h3 := hN.ae_notMem MeasureTheory.volume
  filter_upwards [h1, h2, h3] with s hs1 hs2 hs3
  refine ⟨hs1, hs2, fun w hw => ?_⟩
  by_cases hs : EuclideanSpace.proj (0 : Fin 2) (γ s) = 0
  · have hne : (𝓝[T ∩ Set.Ioi s] s).NeBot := ⟨fun h => hs3 ⟨hs, h⟩⟩
    have d1 : deriv (f κ ∘ γ) s = 0 := deriv_zero_of_acc hs1.hasDerivAt (fun r hr => by
      have hr' : EuclideanSpace.proj (0 : Fin 2) (γ r) = 0 := hr
      simp only [Function.comp_apply]
      rw [f_line κ _ hr', f_line κ _ hs]) hne
    have d2 : EuclideanSpace.proj (0 : Fin 2) (deriv γ s) = 0 := by
      have hp := (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt
        s hs2.hasDerivAt
      exact deriv_zero_of_acc hp (fun r hr => by
        have hr' : EuclideanSpace.proj (0 : Fin 2) (γ r) = 0 := hr
        simp only [Function.comp_apply]
        rw [hr', hs]) hne
    have hw1 : w 1 = 0 := clarke_line_sub κ hκ M hM hK (γ s) hs hw
    simp at d2
    rw [d1]
    simp [PiLp.inner_apply, Fin.sum_univ_two, d2, hw1]
  · rw [clarke_off κ (γ s) hs, Set.mem_singleton_iff] at hw
    subst hw
    rw [((diff_off κ (γ s) hs).hasFDerivAt.comp_hasDerivAt s hs2.hasDerivAt).deriv]
    exact InnerProductSpace.toDual_symm_apply.symm

lemma weakSard (κ : ℝ) (hκ : 0 ≤ κ) (M : ℝ) (hM : ∀ u, ‖fderiv ℝ χ u‖ ≤ M)
    (hK : 2 * ((1 + M) * κ) ≤ 1 / 2) : PathoSubgrad.Circle.WeakSard (f κ) := by
  intro y hy z hz
  have hz' := connectedComponentIn_subset _ _ hz
  rw [f_line κ z ((critSet_iff κ hκ M hM hK z).1 hz'), f_line κ y ((critSet_iff κ hκ M hM hK y).1 hy)]

lemma off_crit (κ : ℝ) (hκ : 0 ≤ κ) (M : ℝ) (hM : ∀ u, ‖fderiv ℝ χ u‖ ≤ M)
    (hK : 2 * ((1 + M) * κ) ≤ 1 / 2) :
    ∀ y ∉ PathoSubgrad.Circle.critSet (f κ), DifferentiableAt ℝ (f κ) y ∧ 1 / 2 ≤ ‖gradient (f κ) y‖ := by
  intro y hy
  have hy' : EuclideanSpace.proj (0 : Fin 2) y ≠ 0 := fun h => hy ((critSet_iff κ hκ M hM hK y).2 h)
  obtain ⟨h1, h2⟩ := fderiv_f_bound κ hκ M hM hK y hy'
  exact ⟨h1, by rw [norm_gradient']; exact h2⟩

lemma subgradSeq (κ : ℝ) (hκ : 0 ≤ κ) (M : ℝ) (hM : ∀ u, ‖fderiv ℝ χ u‖ ≤ M) :
    PathoSubgrad.Circle.IsSubgradientSeq (f κ) eps (x κ) :=
  ⟨(f_lipschitzWith κ hκ M hM).locallyLipschitz, eps_pos, tendsto_sum_eps, tendsto_eps,
    fun i => ⟨v κ i, v_mem_clarke κ i, x_succ κ i⟩⟩

/-! ### Assembly (all but the generic Whitney child C7) -/

/-- hypotheses of the generic Whitney-stratification child (C7) -/
def WhitneyHyp (g : EuclideanSpace ℝ (Fin 2) → ℝ) : Prop :=
  Continuous g ∧ ContDiffOn ℝ ∞ g {y | EuclideanSpace.proj (0 : Fin 2) y ≠ 0} ∧
  (∀ y, EuclideanSpace.proj (0 : Fin 2) y = 0 → g y = 0) ∧
  ∀ ε > 0, ∃ δ > 0, ∀ y, EuclideanSpace.proj (0 : Fin 2) y ≠ 0 → |EuclideanSpace.proj (0 : Fin 2) y| < δ →
    |fderiv ℝ g y (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))| < ε

lemma whitneyHyp_f (κ : ℝ) (hκ : 0 ≤ κ) (M : ℝ) (hM : ∀ u, ‖fderiv ℝ χ u‖ ≤ M) :
    WhitneyHyp (f κ) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  refine ⟨(f_lipschitzWith κ hκ M hM).continuous, f_contDiffOn κ, f_line κ, fun ε hε => ?_⟩
  have hK : 0 ≤ 12 * ((1 + M) * κ) := by
    have : 0 ≤ (1 + M) * κ := mul_nonneg (by linarith) hκ
    linarith
  refine ⟨ε / (12 * ((1 + M) * κ) + 1), by positivity, fun y hy hyδ => ?_⟩
  rw [← gradient_apply']
  refine (grad_f_one κ hκ M hM y hy).trans_lt ?_
  calc 12 * ((1 + M) * κ) * |EuclideanSpace.proj (0 : Fin 2) y|
      ≤ 12 * ((1 + M) * κ) * (ε / (12 * ((1 + M) * κ) + 1)) :=
        mul_le_mul_of_nonneg_left hyδ.le hK
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

lemma assembly (hW : ∀ g : EuclideanSpace ℝ (Fin 2) → ℝ, WhitneyHyp g →
      PathoSubgrad.Circle.IsWhitneyCInfStratifiable g) :
    ∃ (f : EuclideanSpace ℝ (Fin 2) → ℝ) (ε : ℕ → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin 2)),
      PathoSubgrad.Circle.IsSubgradientSeq f ε x ∧ Bornology.IsBounded (Set.range x) ∧
      (¬ ∃ p, Tendsto x atTop (𝓝 p)) ∧
      (∃ K, LipschitzWith K f) ∧ PathoSubgrad.Circle.IsPathDifferentiable f ∧
      PathoSubgrad.Circle.WeakSard f ∧
      PathoSubgrad.Circle.IsWhitneyCInfStratifiable f ∧
      (∀ y ∉ PathoSubgrad.Circle.critSet f, DifferentiableAt ℝ f y ∧ 1 / 2 ≤ ‖gradient f y‖) ∧
      (∀ i, ∃ r > 0, ContDiffOn ℝ ∞ f (Metric.ball (x i) r)) := by
  obtain ⟨M, hM0, hM⟩ := exists_M
  have hpos : 0 < 1 + M := by linarith
  set κ : ℝ := 1 / (4 * (1 + M)) with hκdef
  have hκ0 : 0 < κ := by positivity
  have hκ1 : κ ≤ 1 := by
    rw [hκdef, div_le_one (by positivity)]; linarith
  have hprod : (1 + M) * κ = 1 / 4 := by
    rw [hκdef, mul_one_div, div_eq_iff (by positivity)]; ring
  have hK : 2 * ((1 + M) * κ) ≤ 1 / 2 := by rw [hprod]; norm_num
  exact ⟨f κ, eps, x κ, subgradSeq κ hκ0.le M hM, bounded_x κ, not_tendsto_x κ hκ0 hκ1,
    ⟨_, f_lipschitzWith κ hκ0.le M hM⟩, pathDiff κ hκ0.le M hM hK, weakSard κ hκ0.le M hM hK,
    hW _ (whitneyHyp_f κ hκ0.le M hM), off_crit κ hκ0.le M hM hK,
    fun i => ⟨c i / 2, half_pos (c_pos i), f_contDiffOn_ball κ i⟩⟩

namespace W7

abbrev W2 := EuclideanSpace ℝ (Fin 2)
abbrev W3 := EuclideanSpace ℝ (Fin 3)

lemma ext3 {z w : W3} (h0 : z 0 = w 0) (h1 : z 1 = w 1) (h2 : z 2 = w 2) : z = w := by
  ext i
  fin_cases i
  exacts [h0, h1, h2]

lemma ext2 {z w : W2} (h0 : z 0 = w 0) (h1 : z 1 = w 1) : z = w := by
  ext i
  fin_cases i
  exacts [h0, h1]

lemma fin3 : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide

lemma cc3 (i : Fin 3) : Continuous (fun z : W3 => z i) := (EuclideanSpace.proj i).continuous
lemma cc2 (i : Fin 2) : Continuous (fun z : W2 => z i) := (EuclideanSpace.proj i).continuous

def Pl : W3 →ₗ[ℝ] W2 where
  toFun z := WithLp.toLp 2 (fun i : Fin 2 => z i.castSucc)
  map_add' a b := by ext i; simp
  map_smul' r a := by ext i; simp

def P : W3 →L[ℝ] W2 := LinearMap.toContinuousLinearMap Pl

lemma P0 (z : W3) : P z 0 = z 0 := rfl
lemma P1 (z : W3) : P z 1 = z 1 := rfl
lemma pr0 (y : W2) : EuclideanSpace.proj (0 : Fin 2) y = y 0 := rfl

def Ll : W2 →ₗ[ℝ] W3 where
  toFun y := WithLp.toLp 2 ![y 0, y 1, 0]
  map_add' a b := ext3 (by simp) (by simp) (by simp)
  map_smul' r a := ext3 (by simp) (by simp) (by simp)

def L : W2 →L[ℝ] W3 := LinearMap.toContinuousLinearMap Ll

lemma L0 (y : W2) : L y 0 = y 0 := rfl
lemma L1 (y : W2) : L y 1 = y 1 := rfl
lemma L2 (y : W2) : L y 2 = 0 := rfl

def e1 : W3 := EuclideanSpace.single 1 1
def e2 : W3 := EuclideanSpace.single 2 1
def f0 : W2 := EuclideanSpace.single 0 1
def f1 : W2 := EuclideanSpace.single 1 1

@[simp] lemma e1_0 : e1 0 = 0 := by simp [e1]
@[simp] lemma e1_1 : e1 1 = 1 := by simp [e1]
@[simp] lemma e1_2 : e1 2 = 0 := by simp [e1]
@[simp] lemma e2_0 : e2 0 = 0 := by simp [e2]
@[simp] lemma e2_1 : e2 1 = 0 := by simp [e2]
@[simp] lemma e2_2 : e2 2 = 1 := by simp [e2]
@[simp] lemma f0_0 : f0 0 = 1 := by simp [f0]
@[simp] lemma f1_0 : f1 0 = 0 := by simp [f1]
@[simp] lemma f1_1 : f1 1 = 1 := by simp [f1]

def Lift (g : W2 → ℝ) (y : W2) : W3 := L y + g y • e2

section
variable {g : W2 → ℝ}

lemma Lift0 (y : W2) : Lift g y 0 = y 0 := by simp [Lift, L0]
lemma Lift1 (y : W2) : Lift g y 1 = y 1 := by simp [Lift, L1]
lemma Lift2 (y : W2) : Lift g y 2 = g y := by simp [Lift, L2]

lemma P_Lift (y : W2) : P (Lift g y) = y :=
  ext2 (by rw [P0, Lift0]) (by rw [P1, Lift1])

lemma P_e2 : P e2 = 0 := ext2 (by rw [P0]; simp) (by rw [P1]; simp)

lemma P_add_e2 (z : W3) (t : ℝ) : P (z + t • e2) = P z := by
  rw [map_add, map_smul, P_e2, smul_zero, add_zero]

lemma P_sub_e2 (z : W3) (t : ℝ) : P (z - t • e2) = P z := by
  rw [map_sub, map_smul, P_e2, smul_zero, sub_zero]

lemma mem_graph (g : W2 → ℝ) (z : W3) :
    z ∈ PathoSubgrad.Circle.graphSet g ↔ g (P z) = z 2 := Iff.rfl

lemma Lift_P (z : W3) (h : g (P z) = z 2) : Lift g (P z) = z :=
  ext3 (by rw [Lift0, P0]) (by rw [Lift1, P1]) (by rw [Lift2, h])

lemma Lift_cont (hg : Continuous g) : Continuous (Lift g) :=
  L.continuous.add (hg.smul continuous_const)

def S0 : Set W3 := {z | z 0 = 0 ∧ z 2 = 0}
def Sp (g : W2 → ℝ) (s : ℝ) : Set W3 := {z | g (P z) = z 2 ∧ 0 < s * z 0}
def HH (s : ℝ) : Set W2 := {y | 0 < s * y 0}
def U (s : ℝ) : Set W3 := {z | 0 < s * z 0}

lemma isOpen_H (s : ℝ) : IsOpen (HH s) := isOpen_lt continuous_const (continuous_const.mul (cc2 0))
lemma isOpen_U (s : ℝ) : IsOpen (U s) := isOpen_lt continuous_const (continuous_const.mul (cc3 0))
lemma isClosed_S0 : IsClosed S0 :=
  (isClosed_eq (cc3 0) continuous_const).inter (isClosed_eq (cc3 2) continuous_const)

lemma image_H (s : ℝ) : Lift g '' HH s = Sp g s := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨by rw [P_Lift, Lift2], by rw [Lift0]; exact hy⟩
  · rintro ⟨h2, h0⟩
    refine ⟨P z, ?_, Lift_P z h2⟩
    show 0 < s * P z 0
    rw [P0]; exact h0

lemma S0_graph (hg : WhitneyHyp g) {z : W3} (hz : z ∈ S0) : g (P z) = z 2 := by
  rw [hz.2]; exact hg.2.2.1 _ (by rw [pr0, P0]; exact hz.1)

def S (g : W2 → ℝ) : Fin 3 → Set W3
  | 0 => S0
  | 1 => Sp g 1
  | 2 => Sp g (-1)

lemma iUnion_S (hg : WhitneyHyp g) : (⋃ i, S g i) = PathoSubgrad.Circle.graphSet g := by
  ext z
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    rw [mem_graph]
    rcases fin3 i with rfl | rfl | rfl
    · exact S0_graph hg hi
    · exact hi.1
    · exact hi.1
  · intro hz
    rw [mem_graph] at hz
    rcases lt_trichotomy (z 0) 0 with h | h | h
    · exact ⟨2, show z ∈ Sp g (-1) from ⟨hz, by linarith⟩⟩
    · exact ⟨0, show z ∈ S0 from ⟨h, by rw [← hz]; exact hg.2.2.1 _ (by rw [pr0, P0]; exact h)⟩⟩
    · exact ⟨1, show z ∈ Sp g 1 from ⟨hz, by linarith⟩⟩

lemma disj_0p (s : ℝ) : Disjoint S0 (Sp g s) := by
  rw [Set.disjoint_left]
  rintro z ⟨h0, -⟩ ⟨-, hp⟩
  rw [h0, mul_zero] at hp
  exact lt_irrefl _ hp

lemma disj_pm : Disjoint (Sp g 1) (Sp g (-1)) := by
  rw [Set.disjoint_left]
  rintro z ⟨-, h1⟩ ⟨-, h2⟩
  linarith

lemma pairwise_S : Pairwise (fun i j => Disjoint (S g i) (S g j)) := by
  intro i j hij
  rcases fin3 i with rfl | rfl | rfl <;> rcases fin3 j with rfl | rfl | rfl
  exacts [absurd rfl hij, disj_0p 1, disj_0p (-1), (disj_0p 1).symm, absurd rfl hij, disj_pm,
    (disj_0p (-1)).symm, disj_pm.symm, absurd rfl hij]

lemma S0_eq : S0 = Set.range (fun t : ℝ => t • e1) := by
  ext z
  constructor
  · rintro ⟨h0, h2⟩
    exact ⟨z 1, ext3 (by simp [h0]) (by simp) (by simp [h2])⟩
  · rintro ⟨t, rfl⟩
    exact ⟨by simp, by simp⟩

lemma conn_S0 : IsConnected S0 := by
  rw [S0_eq]
  exact isConnected_range (continuous_id.smul continuous_const)

lemma convex_H (s : ℝ) : Convex ℝ (HH s) :=
  convex_halfSpace_gt (f := fun y : W2 => s * y 0)
    ⟨fun a b => by simp only [PiLp.add_apply]; ring,
     fun c a => by simp only [PiLp.smul_apply, smul_eq_mul]; ring⟩ 0

lemma conn_Sp (hg : WhitneyHyp g) (s : ℝ) (hs : s ≠ 0) : IsConnected (Sp g s) := by
  rw [← image_H]
  refine IsConnected.image ⟨⟨s • f0, ?_⟩, (convex_H s).isPreconnected⟩ _
    (Lift_cont hg.1).continuousOn
  show 0 < s * (s • f0) 0
  rw [PiLp.smul_apply, f0_0, smul_eq_mul, mul_one]
  exact mul_self_pos.2 hs

lemma subAt_of {k d : ℕ} {M : Set W3} {x : W3} (ψ : OpenPartialHomeomorph W3 W3) (hd : d ≤ 3)
    (hxM : x ∈ M) (hx : x ∈ ψ.source) (h1 : ContDiffOn ℝ (k : WithTop ℕ∞) ψ ψ.source)
    (h2 : ContDiffOn ℝ (k : WithTop ℕ∞) ψ.symm ψ.target)
    (hM : M ∩ ψ.source = {z | z ∈ ψ.source ∧ ∀ i : Fin 3, d ≤ i.val → ψ z i = 0}) :
    ProjLikeRetr.Retractor.IsSubmanifoldAt k d M x := by
  unfold ProjLikeRetr.Retractor.IsSubmanifoldAt
  have h3 : Module.finrank ℝ W3 = 3 := finrank_euclideanSpace_fin
  revert h3
  generalize Module.finrank ℝ W3 = n
  rintro rfl
  exact ⟨hd, hxM, ψ, hx, h1, h2, hM⟩

def swl : W3 →ₗ[ℝ] W3 where
  toFun z := WithLp.toLp 2 ![z 1, z 0, z 2]
  map_add' a b := ext3 (by simp) (by simp) (by simp)
  map_smul' r a := ext3 (by simp) (by simp) (by simp)

def sw : W3 →L[ℝ] W3 := LinearMap.toContinuousLinearMap swl

lemma sw0 (z : W3) : sw z 0 = z 1 := rfl
lemma sw1 (z : W3) : sw z 1 = z 0 := rfl
lemma sw2 (z : W3) : sw z 2 = z 2 := rfl

lemma sw_sw (z : W3) : sw (sw z) = z :=
  ext3 (by rw [sw0, sw1]) (by rw [sw1, sw0]) (by rw [sw2, sw2])

def ψ0 : OpenPartialHomeomorph W3 W3 where
  toFun := sw
  invFun := sw
  source := Set.univ
  target := Set.univ
  map_source' _ _ := trivial
  map_target' _ _ := trivial
  left_inv' z _ := sw_sw z
  right_inv' z _ := sw_sw z
  open_source := isOpen_univ
  open_target := isOpen_univ
  continuousOn_toFun := sw.continuous.continuousOn
  continuousOn_invFun := sw.continuous.continuousOn

lemma sub_S0 (k : ℕ) : ProjLikeRetr.Retractor.IsSubmanifold k 1 S0 := by
  intro x hx
  refine subAt_of ψ0 (by norm_num) hx trivial sw.contDiff.contDiffOn sw.contDiff.contDiffOn ?_
  ext z
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨h0, h2⟩, -⟩
    refine ⟨trivial, fun i hi => ?_⟩
    rcases fin3 i with rfl | rfl | rfl
    · exact absurd hi (by decide)
    · exact h0
    · exact h2
  · rintro ⟨-, h⟩
    exact ⟨⟨h 1 (by decide), h 2 (by decide)⟩, trivial⟩

def ψp (hg : Continuous g) (s : ℝ) : OpenPartialHomeomorph W3 W3 where
  toFun z := z - g (P z) • e2
  invFun z := z + g (P z) • e2
  source := U s
  target := U s
  map_source' z hz := by
    have hz' : 0 < s * z 0 := hz
    show 0 < s * (z - g (P z) • e2) 0
    simpa using hz'
  map_target' z hz := by
    have hz' : 0 < s * z 0 := hz
    show 0 < s * (z + g (P z) • e2) 0
    simpa using hz'
  left_inv' z _ := by simp only [P_sub_e2, sub_add_cancel]
  right_inv' z _ := by simp only [P_add_e2, add_sub_cancel_right]
  open_source := isOpen_U s
  open_target := isOpen_U s
  continuousOn_toFun :=
    (continuous_id.sub ((hg.comp P.continuous).smul continuous_const)).continuousOn
  continuousOn_invFun :=
    (continuous_id.add ((hg.comp P.continuous).smul continuous_const)).continuousOn

lemma gP_smooth (hg : WhitneyHyp g) (s : ℝ) : ContDiffOn ℝ ∞ (fun z => g (P z)) (U s) :=
  hg.2.1.comp P.contDiff.contDiffOn (fun z hz => by
    have hz' : 0 < s * z 0 := hz
    show EuclideanSpace.proj (0 : Fin 2) (P z) ≠ 0
    rw [pr0, P0]; exact right_ne_zero_of_mul (ne_of_gt hz'))

lemma sub_Sp (hg : WhitneyHyp g) (s : ℝ) (k : ℕ) :
    ProjLikeRetr.Retractor.IsSubmanifold k 2 (Sp g s) := by
  intro x hx
  have hsm := gP_smooth hg s
  refine subAt_of (ψp hg.1 s) (by norm_num) hx hx.2 ?_ ?_ ?_
  · exact contDiffOn_infty.1 (contDiffOn_id.sub (hsm.smul contDiffOn_const)) k
  · exact contDiffOn_infty.1 (contDiffOn_id.add (hsm.smul contDiffOn_const)) k
  · ext z
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨h2, -⟩, hU⟩
      refine ⟨hU, fun i hi => ?_⟩
      rcases fin3 i with rfl | rfl | rfl
      · exact absurd hi (by decide)
      · exact absurd hi (by decide)
      · show (z - g (P z) • e2) 2 = 0
        simp [h2]
    · rintro ⟨hU, h⟩
      have hU' : 0 < s * z 0 := hU
      have h2 := h 2 (by decide)
      change (z - g (P z) • e2) 2 = 0 at h2
      simp at h2
      exact ⟨⟨by linarith, hU'⟩, hU⟩

lemma closure_Sp_sub (s : ℝ) : closure (Sp g s) ⊆ {z | 0 ≤ s * z 0} :=
  closure_minimal (fun z hz => le_of_lt hz.2)
    (isClosed_le continuous_const (continuous_const.mul (cc3 0)))

lemma S0_sub_closure (hg : WhitneyHyp g) (s : ℝ) (hs : s ≠ 0) : S0 ⊆ closure (Sp g s) := by
  intro z hz
  have hz2 := S0_graph hg hz
  have ht : Tendsto (fun n : ℕ => P z + (s / (n : ℝ)) • f0) atTop (𝓝 (P z)) := by
    simpa using tendsto_const_nhds.add ((tendsto_const_div_atTop_nhds_zero_nat s).smul_const f0)
  have hl := ((Lift_cont hg.1).tendsto (P z)).comp ht
  rw [Lift_P z hz2] at hl
  refine mem_closure_of_tendsto hl (Filter.eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  rw [← image_H]
  refine ⟨P z + (s / (n : ℝ)) • f0, ?_, rfl⟩
  show 0 < s * (P z + (s / (n : ℝ)) • f0) 0
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have e : (P z + (s / (n : ℝ)) • f0) 0 = s / n := by simp [P0, hz.1]
  rw [e, ← mul_div_assoc]
  exact div_pos (mul_self_pos.2 hs) hn'

lemma no0p (s : ℝ) : ¬ (closure S0 ∩ Sp g s).Nonempty := by
  rintro ⟨z, hz1, hz2⟩
  rw [isClosed_S0.closure_eq] at hz1
  exact Set.disjoint_left.1 (disj_0p s) hz1 hz2

lemma nopm : ¬ (closure (Sp g 1) ∩ Sp g (-1)).Nonempty := by
  rintro ⟨z, hz1, hz2⟩
  have h1 : 0 ≤ 1 * z 0 := closure_Sp_sub 1 hz1
  have h2 : 0 < -1 * z 0 := hz2.2
  linarith

lemma nomp : ¬ (closure (Sp g (-1)) ∩ Sp g 1).Nonempty := by
  rintro ⟨z, hz1, hz2⟩
  have h1 : 0 ≤ -1 * z 0 := closure_Sp_sub (-1) hz1
  have h2 : 0 < 1 * z 0 := hz2.2
  linarith

lemma frontier_S (hg : WhitneyHyp g) : ∀ i j, i ≠ j → (closure (S g i) ∩ S g j).Nonempty →
    S g j ⊆ closure (S g i) \ S g i := by
  have hp0 : ∀ s : ℝ, s ≠ 0 → S0 ⊆ closure (Sp g s) \ Sp g s := fun s hs z hz =>
    ⟨S0_sub_closure hg s hs hz, fun h => Set.disjoint_left.1 (disj_0p s) hz h⟩
  intro i j hij hne
  rcases fin3 i with rfl | rfl | rfl <;> rcases fin3 j with rfl | rfl | rfl
  · exact absurd rfl hij
  · exact absurd hne (no0p 1)
  · exact absurd hne (no0p (-1))
  · exact hp0 1 one_ne_zero
  · exact absurd rfl hij
  · exact absurd hne nopm
  · exact hp0 (-1) (by norm_num)
  · exact absurd hne nomp
  · exact absurd rfl hij

lemma cone_S0 {x : W3} (hx : x ∈ S0) : tangentConeAt ℝ S0 x ⊆ S0 := by
  intro v hv
  rw [tangentConeAt_eq_biInter_closure] at hv
  have hv' := Set.mem_iInter₂.1 hv Set.univ Filter.univ_mem
  refine closure_minimal ?_ isClosed_S0 hv'
  rintro _ ⟨c, -, w, ⟨-, hw⟩, rfl⟩
  have hw' : (x + w) 0 = 0 ∧ (x + w) 2 = 0 := hw
  rw [PiLp.add_apply, PiLp.add_apply, hx.1, hx.2, zero_add, zero_add] at hw'
  exact ⟨by rw [PiLp.smul_apply, hw'.1, smul_zero], by rw [PiLp.smul_apply, hw'.2, smul_zero]⟩

lemma S0_le (V : Submodule ℝ W3) (he : e1 ∈ V) {v : W3} (hv : v ∈ S0) : v ∈ V := by
  have : v = v 1 • e1 := ext3 (by simp [hv.1]) (by simp) (by simp [hv.2])
  rw [this]
  exact V.smul_mem _ he

lemma lift_deriv (hg : WhitneyHyp g) {y : W2} (hy : y 0 ≠ 0) :
    HasFDerivAt (Lift g) (L + (fderiv ℝ g y).smulRight e2) y := by
  have ho : IsOpen {y : W2 | EuclideanSpace.proj (0 : Fin 2) y ≠ 0} :=
    isOpen_ne_fun (EuclideanSpace.proj 0).continuous continuous_const
  have hd : DifferentiableAt ℝ g y :=
    (hg.2.1.contDiffAt (ho.mem_nhds (by rw [Set.mem_setOf_eq, pr0]; exact hy))).differentiableAt
      (by simp)
  exact L.hasFDerivAt.add (hd.hasFDerivAt.smul_const e2)

def uu (g : W2 → ℝ) (z : W3) : W3 := e1 + (fderiv ℝ g (P z) f1) • e2

lemma u_mem (hg : WhitneyHyp g) (s : ℝ) {z : W3} (hz : z ∈ Sp g s) :
    uu g z ∈ ProjLikeRetr.Retractor.tangentSpace (Sp g s) z := by
  have hz2 : 0 < s * z 0 := hz.2
  have hy : (P z) 0 ≠ 0 := by rw [P0]; exact right_ne_zero_of_mul (ne_of_gt hz2)
  have hyH : P z ∈ HH s := by show 0 < s * P z 0; rw [P0]; exact hz2
  have hf1 : f1 ∈ tangentConeAt ℝ (HH s) (P z) := by
    rw [tangentConeAt_of_mem_nhds ((isOpen_H s).mem_nhds hyH)]; trivial
  have hm := ((lift_deriv hg hy).hasFDerivWithinAt (s := HH s)).mapsTo_tangent_cone hf1
  rw [image_H, Lift_P z hz.1] at hm
  have hval : (L + (fderiv ℝ g (P z)).smulRight e2) f1 = uu g z := by
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply, uu]
    congr 1
    exact ext3 (by rw [L0]; simp) (by rw [L1]; simp) (by rw [L2]; simp)
  rw [hval] at hm
  exact Submodule.subset_span hm

lemma uu_ne (z : W3) : uu g z ≠ 0 := fun h => by
  have := congrArg (fun w : W3 => w 1) h
  simp [uu] at this

lemma e1_mem (hg : WhitneyHyp g) (s : ℝ) {x : W3} (hx : x ∈ S0) (xs : ℕ → W3)
    (V : Submodule ℝ W3) (hxs : ∀ k, xs k ∈ Sp g s) (hlim : Tendsto xs atTop (𝓝 x))
    (hgap : Tendsto (fun k => PathoSubgrad.Circle.subspaceGap
      (ProjLikeRetr.Retractor.tangentSpace (Sp g s) (xs k)) V) atTop (𝓝 0)) :
    e1 ∈ V := by
  have hc : Tendsto (fun k => xs k 0) atTop (𝓝 0) := by
    have := ((cc3 0).tendsto x).comp hlim
    simp only [Function.comp_def, hx.1] at this
    exact this
  have ha : Tendsto (fun k => fderiv ℝ g (P (xs k)) f1) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hg.2.2.2 ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hc δ hδ
    refine ⟨N, fun n hn => ?_⟩
    have h1 := hN n hn
    rw [Real.dist_eq, sub_zero] at h1
    rw [Real.dist_eq, sub_zero]
    have hxn : 0 < s * xs n 0 := (hxs n).2
    have hne : EuclideanSpace.proj (0 : Fin 2) (P (xs n)) ≠ 0 := by
      rw [pr0, P0]; exact right_ne_zero_of_mul (ne_of_gt hxn)
    exact hδ' _ hne (by rw [pr0, P0]; exact h1)
  have hu : Tendsto (fun k => uu g (xs k)) atTop (𝓝 e1) := by
    simpa [uu] using (tendsto_const_nhds (x := e1)).add (ha.smul_const e2)
  have h1 : ‖e1‖ = 1 := by simp [e1]
  have hw : Tendsto (fun k => ‖uu g (xs k)‖⁻¹ • uu g (xs k)) atTop (𝓝 e1) := by
    have := (hu.norm.inv₀ (by rw [h1]; exact one_ne_zero)).smul hu
    rwa [h1, inv_one, one_smul] at this
  have hb : ∀ k, Metric.infDist (‖uu g (xs k)‖⁻¹ • uu g (xs k)) (V : Set W3) ≤
      PathoSubgrad.Circle.subspaceGap (ProjLikeRetr.Retractor.tangentSpace (Sp g s) (xs k)) V := by
    intro k
    refine le_trans ?_ (le_max_left _ _)
    have hn : ‖‖uu g (xs k)‖⁻¹ • uu g (xs k)‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 (uu_ne _))]
    refine le_csSup ⟨1, ?_⟩ ⟨_, ⟨Submodule.smul_mem _ _ (u_mem hg s (hxs k)), hn⟩, rfl⟩
    rintro _ ⟨v, ⟨-, hv⟩, rfl⟩
    calc Metric.infDist v (V : Set W3) ≤ dist v 0 := Metric.infDist_le_dist_of_mem V.zero_mem
      _ = 1 := by rw [dist_zero_right, hv]
  have hd0 : Tendsto (fun k => Metric.infDist (‖uu g (xs k)‖⁻¹ • uu g (xs k)) (V : Set W3))
      atTop (𝓝 0) := squeeze_zero (fun k => Metric.infDist_nonneg) hb hgap
  have hd1 := ((Metric.continuous_infDist_pt (V : Set W3)).tendsto e1).comp hw
  have heq : Metric.infDist e1 (V : Set W3) = 0 := tendsto_nhds_unique hd1 hd0
  have hcl : e1 ∈ closure (V : Set W3) :=
    (Metric.mem_closure_iff_infDist_zero ⟨0, V.zero_mem⟩).2 heq
  rwa [V.closed_of_finiteDimensional.closure_eq] at hcl

lemma condA (hg : WhitneyHyp g) (s : ℝ) {x : W3} (hx : x ∈ S0) (xs : ℕ → W3)
    (V : Submodule ℝ W3) (hxs : ∀ k, xs k ∈ Sp g s) (hlim : Tendsto xs atTop (𝓝 x))
    (hgap : Tendsto (fun k => PathoSubgrad.Circle.subspaceGap
      (ProjLikeRetr.Retractor.tangentSpace (Sp g s) (xs k)) V) atTop (𝓝 0)) :
    ProjLikeRetr.Retractor.tangentSpace S0 x ≤ V := by
  have he := e1_mem hg s hx xs V hxs hlim hgap
  show Submodule.span ℝ (tangentConeAt ℝ S0 x) ≤ V
  exact Submodule.span_le.2 (fun v hv => S0_le V he (cone_S0 hx hv))

lemma condA_S (hg : WhitneyHyp g) : ∀ i j, i ≠ j → ∀ x ∈ closure (S g i) ∩ S g j,
    ∀ (xs : ℕ → W3) (V : Submodule ℝ W3), (∀ k, xs k ∈ S g i) → Tendsto xs atTop (𝓝 x) →
    Tendsto (fun k => PathoSubgrad.Circle.subspaceGap
      (ProjLikeRetr.Retractor.tangentSpace (S g i) (xs k)) V) atTop (𝓝 0) →
    ProjLikeRetr.Retractor.tangentSpace (S g j) x ≤ V := by
  intro i j hij x hx xs V hxs hlim hgap
  rcases fin3 i with rfl | rfl | rfl <;> rcases fin3 j with rfl | rfl | rfl
  · exact absurd rfl hij
  · exact (no0p 1 ⟨x, hx⟩).elim
  · exact (no0p (-1) ⟨x, hx⟩).elim
  · exact condA hg 1 hx.2 xs V hxs hlim hgap
  · exact absurd rfl hij
  · exact (nopm ⟨x, hx⟩).elim
  · exact condA hg (-1) hx.2 xs V hxs hlim hgap
  · exact (nomp ⟨x, hx⟩).elim
  · exact absurd rfl hij

end

end W7

theorem whitney_generic (g : EuclideanSpace ℝ (Fin 2) → ℝ) (hg : WhitneyHyp g) :
    PathoSubgrad.Circle.IsWhitneyCInfStratifiable g := by
  refine ⟨Fin 3, W7.S g, ⟨0, (W7.mem_graph g 0).2 (W7.S0_graph hg ⟨by simp, by simp⟩)⟩,
    W7.iUnion_S hg, W7.pairwise_S, fun _ _ => ⟨Set.univ, Filter.univ_mem, Set.toFinite _⟩, ?_,
    W7.frontier_S hg, W7.condA_S hg⟩
  intro i
  rcases W7.fin3 i with rfl | rfl | rfl
  · exact ⟨W7.conn_S0, 1, W7.sub_S0⟩
  · exact ⟨W7.conn_Sp hg 1 one_ne_zero, 2, W7.sub_Sp hg 1⟩
  · exact ⟨W7.conn_Sp hg (-1) (by norm_num), 2, W7.sub_Sp hg (-1)⟩

end

end CE1D

open Filter Topology ContDiff PathoSubgrad.Circle in
theorem solution :
    ∃ (f : EuclideanSpace ℝ (Fin 2) → ℝ) (ε : ℕ → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin 2)),
      IsSubgradientSeq f ε x ∧ Bornology.IsBounded (Set.range x) ∧
      (¬ ∃ p, Tendsto x atTop (𝓝 p)) ∧
      (∃ K, LipschitzWith K f) ∧ IsPathDifferentiable f ∧ WeakSard f ∧
      IsWhitneyCInfStratifiable f ∧
      (∀ y ∉ critSet f, DifferentiableAt ℝ f y ∧ 1 / 2 ≤ ‖gradient f y‖) ∧
      (∀ i, ∃ r > 0, ContDiffOn ℝ ∞ f (Metric.ball (x i) r)) := by
  exact CE1D.assembly CE1D.whitney_generic
