-- Prove2me | solution 1 for SchwartzDist.existsUnique_finsupp_eq_sum_derivCLM_pow_delta
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T18:52:44.109689+00:00
-- url     : https://prove2.me/submissions/d6396b2c-fab4-40e3-b569-18891e34962b

import Mathlib
import Theorems.Thm_SchwartzDist_dsupport_subset_singleton_iff_mem_span_iteratedLineDerivOp_delta

open SchwartzMap LineDeriv Topology Filter

set_option autoImplicit false

namespace Sol_SchwartzDist_existsUnique_finsupp_eq_sum_derivCLM_pow_delta

open scoped ContDiff

/-- `δ₀^{(k)}`. -/
noncomputable abbrev dd (k : ℕ) : 𝓢'(ℝ, ℂ) :=
  ((TemperedDistribution.derivCLM ℂ) ^ k) (TemperedDistribution.delta (0 : ℝ))

lemma derivCLM_pow_apply (k : ℕ) (T : 𝓢'(ℝ, ℂ)) (g : 𝓢(ℝ, ℂ)) :
    ((TemperedDistribution.derivCLM ℂ) ^ k) T g =
      T (((-SchwartzMap.derivCLM ℂ ℂ) ^ k) g) := by
  induction k generalizing T g with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, ContinuousLinearMap.mul_apply, ih, pow_succ', ContinuousLinearMap.mul_apply]
    rfl

lemma negDeriv_pow_coe (k : ℕ) (g : 𝓢(ℝ, ℂ)) :
    ⇑(((-SchwartzMap.derivCLM ℂ ℂ) ^ k) g) = fun x => (-1 : ℂ) ^ k * iteratedDeriv k g x := by
  induction k with
  | zero => funext x; simp
  | succ k ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply]
    funext x
    rw [ContinuousLinearMap.neg_apply, SchwartzMap.neg_apply, SchwartzMap.derivCLM_apply, ih,
      iteratedDeriv_succ, deriv_const_mul_field', pow_succ]
    ring

lemma dd_apply (k : ℕ) (g : 𝓢(ℝ, ℂ)) :
    dd k g = (-1 : ℂ) ^ k * iteratedDeriv k g 0 := by
  rw [dd, derivCLM_pow_apply, TemperedDistribution.delta_apply, negDeriv_pow_coe]

lemma lineDerivOp_eq (v : ℝ) (T : 𝓢'(ℝ, ℂ)) :
    ∂_{v} T = (v : ℂ) • TemperedDistribution.derivCLM ℂ T := by
  ext g
  have hg : (-∂_{v} g : 𝓢(ℝ, ℂ)) = (v : ℂ) • (-SchwartzMap.derivCLM ℂ ℂ g) := by
    ext x
    have : fderiv ℝ (⇑g) x v = v • fderiv ℝ (⇑g) x 1 := by
      rw [← ContinuousLinearMap.map_smul, smul_eq_mul, mul_one]
    simp [SchwartzMap.lineDerivOp_apply_eq_fderiv, this, Complex.real_smul]
  rw [TemperedDistribution.lineDerivOp_apply_apply, hg, map_smul]
  rfl

lemma iteratedLineDerivOp_delta (k : ℕ) (m : Fin k → ℝ) :
    ∂^{m} (TemperedDistribution.delta (0 : ℝ)) = (∏ i, (m i : ℂ)) • dd k := by
  induction k with
  | zero => simp [dd]
  | succ k ih =>
    rw [iteratedLineDerivOp_succ_left, ih, lineDerivOp_eq, map_smul, Fin.prod_univ_succ,
      smul_smul, dd, dd, pow_succ', ContinuousLinearMap.mul_apply]
    rfl

/-- Cut-off equal to `1` on `[-1, 1]`, supported in `[-2, 2]`. -/
noncomputable def chi : ContDiffBump (0 : ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩

/-- The test function `x ↦ x ^ m χ(x)`. -/
noncomputable def testFun (m : ℕ) : ℝ → ℂ := fun x => (x ^ m * chi x) • (1 : ℂ)

lemma testFun_hasCompactSupport (m : ℕ) : HasCompactSupport (testFun m) := by
  have h : HasCompactSupport ((fun x : ℝ => x ^ m) * (chi : ℝ → ℝ)) :=
    chi.hasCompactSupport.mul_left
  have h2 : HasCompactSupport (((fun x : ℝ => x ^ m) * (chi : ℝ → ℝ)) • fun _ : ℝ => (1 : ℂ)) :=
    h.smul_right
  exact h2

lemma testFun_contDiff (m : ℕ) : ContDiff ℝ ∞ (testFun m) :=
  ((contDiff_id.pow m).mul chi.contDiff).smul contDiff_const

/-- `x ↦ x ^ m χ(x)` as a Schwartz function. -/
noncomputable def phi (m : ℕ) : 𝓢(ℝ, ℂ) :=
  (testFun_hasCompactSupport m).toSchwartzMap (testFun_contDiff m)

lemma iteratedDeriv_phi_zero (k m : ℕ) :
    iteratedDeriv k (phi m) 0 = if k = m then (m.factorial : ℂ) else 0 := by
  have h1 : ⇑(phi m) = fun x : ℝ => (x ^ m * chi x) • (1 : ℂ) := rfl
  have hev : (fun x : ℝ => x ^ m * chi x) =ᶠ[𝓝 0] (fun x : ℝ => x ^ m) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) zero_lt_one] with x hx
    rw [chi.one_of_mem_closedBall (Metric.ball_subset_closedBall hx), mul_one]
  have hcd : ContDiffAt ℝ k (fun x : ℝ => x ^ m * chi x) 0 :=
    ((contDiff_id.pow m).mul chi.contDiff).contDiffAt.of_le (by exact_mod_cast le_top)
  rw [h1, iteratedDeriv_smul_const (f := fun x : ℝ => x ^ m * chi x) hcd (1 : ℂ),
    hev.iteratedDeriv_eq, iteratedDeriv_fun_pow_zero]
  split_ifs <;> simp

lemma dd_phi (k m : ℕ) : dd k (phi m) = if k = m then (-1 : ℂ) ^ m * m.factorial else 0 := by
  rw [dd_apply, iteratedDeriv_phi_zero]
  split_ifs with h
  · rw [h]
  · rw [mul_zero]

/-- Evaluation at a test function, as a linear map. -/
noncomputable def ev (g : 𝓢(ℝ, ℂ)) : 𝓢'(ℝ, ℂ) →ₗ[ℂ] ℂ where
  toFun T := T g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma linearIndependent_dd : LinearIndependent ℂ dd := by
  rw [linearIndependent_iff']
  intro s g hg m hm
  have h := congrArg (ev (phi m)) hg
  rw [map_sum, map_zero, Finset.sum_eq_single m] at h
  · change g m • dd m (phi m) = 0 at h
    rw [dd_phi, if_pos rfl, smul_eq_mul, mul_eq_zero] at h
    rcases h with h | h
    · exact h
    · exfalso
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast m.factorial_ne_zero) h
  · intro i _ hi
    change g i • dd i (phi m) = 0
    rw [dd_phi, if_neg hi, smul_zero]
  · intro h'
    exact absurd hm h'

lemma span_le :
    Submodule.span ℂ (Set.range fun p : (Σ k : ℕ, Fin k → ℝ) =>
        ∂^{p.2} (TemperedDistribution.delta (0 : ℝ))) ≤ Submodule.span ℂ (Set.range dd) := by
  rw [Submodule.span_le]
  rintro _ ⟨p, rfl⟩
  show ∂^{p.2} (TemperedDistribution.delta (0 : ℝ)) ∈ _
  rw [iteratedLineDerivOp_delta]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p.1, rfl⟩)

end Sol_SchwartzDist_existsUnique_finsupp_eq_sum_derivCLM_pow_delta

open Sol_SchwartzDist_existsUnique_finsupp_eq_sum_derivCLM_pow_delta in
theorem solution (T : 𝓢'(ℝ, ℂ))
    (hT : Distribution.dsupport (⇑T) ⊆ {(0 : ℝ)}) :
    ∃! c : ℕ →₀ ℂ, T = c.sum fun k a =>
      a • ((TemperedDistribution.derivCLM ℂ) ^ k) (TemperedDistribution.delta (0 : ℝ)) := by
  have hspan : T ∈ Submodule.span ℂ (Set.range dd) :=
    span_le ((SchwartzDist.dsupport_subset_singleton_iff_mem_span_iteratedLineDerivOp_delta
      (0 : ℝ) T).mp hT)
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hspan
  refine ⟨c, hc.symm, fun d hd => ?_⟩
  apply linearIndependent_dd
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, hc]
  exact hd.symm
