-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P04.finite_uniform_tensor_density
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T05:23:11.110017+00:00
-- url     : https://prove2.me/submissions/f6fc30df-ddea-4bc2-95e7-44c5acfaa3ad

import Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_local_tensor_density
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences

noncomputable section
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1000000

open QAlgorithms.Papers.Independent.Renew46.P04
attribute [local instance] linearOperatorNorm linearOperatorSeminormedGroup
attribute [local instance] linearOperatorNormedGroup linearOperatorNormedSpace
attribute [local instance] dualNormedGroup dualNormedSpace

open Filter Set
open scoped Topology

namespace X9FU
variable {K X Y : Type*} [RCLike K]
variable [NormedAddCommGroup X] [NormedSpace K X]
variable [NormedAddCommGroup Y] [NormedSpace K Y]

@[simp] theorem update_pair_false (x a : X) (y : Y) :
    Function.update (pair x y) false (ULift.up a) = pair a y := by
  funext b
  cases b <;> simp [Function.update, pair] <;> rfl

@[simp] theorem update_pair_true (x : X) (y b : Y) :
    Function.update (pair x y) true (ULift.up b) = pair x b := by
  funext i
  cases i <;> simp [Function.update, pair] <;> rfl

theorem form_add_left (B : Bilinear K X Y K) (x a : X) (y : Y) :
    B (pair (x + a) y) = B (pair x y) + B (pair a y) := by
  have h := B.map_update_add (pair x y) false (ULift.up x) (ULift.up a)
  change B (Function.update (pair x y) false (ULift.up (x + a))) = _ at h
  simpa only [update_pair_false] using h

theorem form_add_right (B : Bilinear K X Y K) (x : X) (y b : Y) :
    B (pair x (y + b)) = B (pair x y) + B (pair x b) := by
  have h := B.map_update_add (pair x y) true (ULift.up y) (ULift.up b)
  change B (Function.update (pair x y) true (ULift.up (y + b))) = _ at h
  simpa only [update_pair_true] using h

theorem form_smul_left (B : Bilinear K X Y K) (c : K) (x : X) (y : Y) :
    B (pair (c • x) y) = c • B (pair x y) := by
  have h := B.map_update_smul (pair x y) false c (ULift.up x)
  change B (Function.update (pair x y) false (ULift.up (c • x))) = _ at h
  simpa only [update_pair_false] using h

theorem form_smul_right (B : Bilinear K X Y K) (c : K) (x : X) (y : Y) :
    B (pair x (c • y)) = c • B (pair x y) := by
  have h := B.map_update_smul (pair x y) true c (ULift.up y)
  change B (Function.update (pair x y) true (ULift.up (c • y))) = _ at h
  simpa only [update_pair_true] using h

def formLinear (B : Bilinear K X Y K) : X →ₗ[K] Y →ₗ[K] K where
  toFun x :=
    { toFun := fun y => B (pair x y)
      map_add' := form_add_right B x
      map_smul' := fun c y => form_smul_right B c x y }
  map_add' x a := by ext y; exact form_add_left B x a y
  map_smul' c x := by ext y; exact form_smul_left B c x y

theorem form_bound (B : Bilinear K X Y K) (x : X) (y : Y) :
    ‖B (pair x y)‖ ≤ ‖B‖ * ‖x‖ * ‖y‖ := by
  have h := B.le_opNorm (pair x y)
  simp only [Fintype.prod_bool] at h
  change ‖B (pair x y)‖ ≤ ‖B‖ * (‖y‖ * ‖x‖) at h
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h

def formOperator (B : Bilinear K X Y K) : X →L[K] (Y →L[K] K) :=
  (formLinear B).mkContinuous₂ ‖B‖ (form_bound B)

@[simp] theorem formOperator_apply (B : Bilinear K X Y K) (x : X) (y : Y) :
    formOperator B x y = B (pair x y) := rfl

theorem norm_formOperator (B : Bilinear K X Y K) : ‖formOperator B‖ = ‖B‖ := by
  apply le_antisymm
  · exact LinearMap.mkContinuous₂_norm_le _ (norm_nonneg _) _
  · apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
    intro m
    have hm : pair (m false).down (m true).down = m := by
      funext b
      cases b <;> rfl
    have h := (formOperator B).le_opNorm₂ (m false).down (m true).down
    rw [formOperator_apply, hm] at h
    simp only [Fintype.prod_bool]
    change ‖B m‖ ≤ ‖formOperator B‖ * (‖(m true).down‖ * ‖(m false).down‖)
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h

/-- A sequence on the unit sphere whose image under a contraction converges
    to a unit scalar is Cauchy in a uniformly convex space. -/
theorem cauchy_of_eval_tendsto [UniformConvexSpace Y]
    (f : Y →L[K] K) (hf : ‖f‖ ≤ 1) (u : ℕ → Y) (hu : ∀ n, ‖u n‖ = 1)
    (c : K) (hc : ‖c‖ = 1) (ht : Tendsto (fun n => f (u n)) atTop (𝓝 c)) :
    CauchySeq u := by
  apply Metric.cauchySeq_iff.mpr
  intro eps heps
  obtain ⟨d, hd, hconv⟩ := exists_forall_sphere_dist_add_le_two_sub Y heps
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht (d / 4) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  rw [dist_eq_norm]
  by_contra hmn
  have hsum := hconv (hu m) (hu n) (le_of_not_gt hmn)
  have hfm : ‖f (u m) - c‖ < d / 4 := by simpa [dist_eq_norm] using hN m hm
  have hfn : ‖f (u n) - c‖ < d / 4 := by simpa [dist_eq_norm] using hN n hn
  have hnorm : ‖f (u m + u n)‖ ≤ ‖u m + u n‖ :=
    (f.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hf)
  have hlow : 2 ≤ ‖f (u m + u n)‖ + ‖f (u m) - c‖ + ‖f (u n) - c‖ := by
    calc
      2 = ‖c + c‖ := by rw [← two_smul ℝ c, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2), hc]; norm_num
      _ = ‖f (u m + u n) - (f (u m) - c) - (f (u n) - c)‖ := by
        congr 1
        rw [map_add]
        abel
      _ ≤ ‖f (u m + u n) - (f (u m) - c)‖ + ‖f (u n) - c‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add (norm_sub_le (f (u m + u n)) (f (u m) - c)) le_rfl
  linarith

/-- The geometric fact in Example 4.2(b). -/
theorem finite_uniform_local [FiniteDimensional K X] [CompleteSpace Y]
    [UniformConvexSpace Y] : LocalBilinear K X Y := by
  classical
  intro eps heps B hB
  by_contra h
  have hbad : ∀ eta : ℝ, 0 < eta → ∃ x : X, ∃ y : Y,
      ‖x‖ = 1 ∧ ‖y‖ = 1 ∧ 1 - eta < ‖B (pair x y)‖ ∧
      ¬ ∃ a : X, ∃ b : Y, ‖a‖ = 1 ∧ ‖b‖ = 1 ∧
        ‖B (pair a b)‖ = 1 ∧ ‖x - a‖ < eps ∧ ‖y - b‖ < eps := by
    intro eta heta
    by_contra hnone
    apply h
    refine ⟨eta, heta, ?_⟩
    intro x y hx hy hnear
    by_contra hno
    exact hnone ⟨x, y, hx, hy, hnear, hno⟩
  choose x y hx hy hnear hfar using
    fun n : ℕ => hbad (1 / ((n : ℝ) + 1)) (by positivity)
  have hbound (n : ℕ) : ‖B (pair (x n) (y n))‖ ≤ 1 := by
    simpa [hB, hx n, hy n] using form_bound B (x n) (y n)
  have hnorm : Tendsto (fun n => ‖B (pair (x n) (y n))‖) atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (show Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 1)) atTop (𝓝 1) by
        simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
      tendsto_const_nhds (fun n => (hnear n).le) hbound
  letI : ProperSpace X := FiniteDimensional.proper K X
  have hcompact := (isCompact_sphere (0 : X) 1).prod (isCompact_closedBall (0 : K) 1)
  obtain ⟨p, hp, φ, hφ, ht⟩ := hcompact.tendsto_subseq
    (x := fun n => (x n, B (pair (x n) (y n)))) (fun n => by
      exact ⟨by simpa using hx n, by simpa using hbound n⟩)
  have ha : ‖p.1‖ = 1 := by simpa using hp.1
  have hxt : Tendsto (fun n => x (φ n)) atTop (𝓝 p.1) := by
    exact (continuous_fst.tendsto p).comp ht
  have hct : Tendsto (fun n => B (pair (x (φ n)) (y (φ n)))) atTop (𝓝 p.2) := by
    exact (continuous_snd.tendsto p).comp ht
  have hc : ‖p.2‖ = 1 := tendsto_nhds_unique hct.norm (hnorm.comp hφ.tendsto_atTop)
  let T := formOperator B
  let f := T p.1
  have hf : ‖f‖ ≤ 1 := by
    simpa [f, T, norm_formOperator, hB, ha] using (formOperator B).le_opNorm p.1
  have hft : Tendsto (fun n => f (y (φ n))) atTop (𝓝 p.2) := by
    apply Metric.tendsto_atTop.mpr
    intro e he
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hxt (e / 2) (by positivity)
    obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hct (e / 2) (by positivity)
    refine ⟨max N M, fun n hn => ?_⟩
    have hb : ‖T (p.1 - x (φ n)) (y (φ n))‖ ≤ ‖p.1 - x (φ n)‖ := by
      simpa [T, norm_formOperator, hB, hy] using T.le_opNorm₂ (p.1 - x (φ n)) (y (φ n))
    have hdiff : dist (f (y (φ n))) (B (pair (x (φ n)) (y (φ n)))) < e / 2 := by
      rw [dist_eq_norm]
      change ‖T p.1 (y (φ n)) - T (x (φ n)) (y (φ n))‖ < _
      rw [← ContinuousLinearMap.sub_apply, ← map_sub]
      exact hb.trans_lt (by simpa [dist_eq_norm, norm_sub_rev] using hN n (le_trans (le_max_left _ _) hn))
    calc
      dist (f (y (φ n))) p.2 ≤
          dist (f (y (φ n))) (B (pair (x (φ n)) (y (φ n)))) +
          dist (B (pair (x (φ n)) (y (φ n)))) p.2 := dist_triangle _ _ _
      _ < e / 2 + e / 2 := add_lt_add hdiff (hM n (le_trans (le_max_right _ _) hn))
      _ = e := by ring
  obtain ⟨b, hbt⟩ := cauchySeq_tendsto_of_complete
    (cauchy_of_eval_tendsto f hf (fun n => y (φ n)) (fun n => hy (φ n)) p.2 hc hft)
  have hb : ‖b‖ = 1 := tendsto_nhds_unique hbt.norm (by simpa [hy] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)))
  have hfb : f b = p.2 := tendsto_nhds_unique (f.continuous.tendsto b |>.comp hbt) hft
  have hBab : ‖B (pair p.1 b)‖ = 1 := by change ‖f b‖ = 1; rw [hfb, hc]
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hxt eps heps
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hbt eps heps
  exact hfar (φ (max N M)) ⟨p.1, b, ha, hb, hBab,
    by simpa [dist_eq_norm] using hN (max N M) (le_max_left _ _),
    by simpa [dist_eq_norm] using hM (max N M) (le_max_right _ _)⟩

end X9FU

variable {K : Type*} [RCLike K]
variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace K X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]

theorem solution [FiniteDimensional K X] [UniformConvexSpace Y] :
    TensorDense K X Y :=
  local_tensor_density X9FU.finite_uniform_local
