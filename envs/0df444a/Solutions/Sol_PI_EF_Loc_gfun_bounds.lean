-- Prove2me | solution 1 for PI.EF.Loc.gfun_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:42:29.380848+00:00
-- url     : https://prove2.me/submissions/05f945b2-cc2d-42c8-9c17-7147273476ed

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LogDerivBoundOfZeroFree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_NormLogDerivReflLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LocalAbstract
import Theorems.Thm_PI_EF_Loc_differentiable_refl
import Theorems.Thm_PI_EF_Loc_norm_refl_sphere
import Theorems.Thm_PI_EF_Loc_refl_center

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.EF.Loc
open Complex Metric Set Filter Topology
section core
variable {r R' R M : ℝ} {f h : ℂ → ℂ} {s₀ : ℂ} {Z : Finset ℂ} {m : ℂ → ℕ}
private theorem differentiableOn_gfun_of_differentiableOn {U : Set ℂ} (hh : DifferentiableOn ℂ h U) :
    DifferentiableOn ℂ (gfun s₀ R Z m h) U := by
  have e : gfun s₀ R Z m h = fun z => (∏ ρ ∈ Z, refl s₀ R ρ z ^ m ρ) * h z := rfl
  rw [e]
  refine DifferentiableOn.mul ?_ hh
  have hd : Differentiable ℂ (fun z => ∏ ρ ∈ Z, refl s₀ R ρ z ^ m ρ) := by
    first
      | exact Differentiable.finset_prod fun ρ _ => (differentiable_refl s₀ R ρ).pow (m ρ)
      | (have hbd := differentiable_refl s₀ R; fun_prop)
  exact hd.differentiableOn
end core
end PI.EF.Loc
end
end

set_option autoImplicit false
noncomputable section
open PI PI.EF PI.EF.Loc
open Complex Metric Set Filter Topology
variable {r R' R M : ℝ} {f h : ℂ → ℂ} {s₀ : ℂ} {Z : Finset ℂ} {m : ℂ → ℕ}
namespace PI.EF.Loc
theorem _root_.solution (hR' : 0 < R') (hR'R : R' < R)
    (hZ : ∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ closedBall s₀ R' ∧ f ρ = 0))
    (hh : DifferentiableOn ℂ h (closedBall s₀ R)) (hh0 : ∀ z ∈ closedBall s₀ R', h z ≠ 0)
    (hfac : ∀ z ∈ closedBall s₀ R, f z = (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * h z)
    (hb : ∀ s ∈ closedBall s₀ R, ‖f s‖ ≤ Real.exp M * ‖f s₀‖) :
    (∀ z ∈ closedBall s₀ R, ‖gfun s₀ R Z m h z‖ ≤ Real.exp M * ‖gfun s₀ R Z m h s₀‖) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) * Real.log (R / R') ≤ M := by
  have hR : 0 < R := hR'.trans hR'R
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∑ ρ ∈ Z, m ρ = N := ⟨_, rfl⟩
  have hs₀R' : s₀ ∈ closedBall s₀ R' := mem_closedBall_self hR'.le
  have hs₀R : s₀ ∈ closedBall s₀ R := mem_closedBall_self hR.le
  have hhs₀ : h s₀ ≠ 0 := hh0 s₀ hs₀R'
  have hg₀ : gfun s₀ R Z m h s₀ = (R : ℂ) ^ N * h s₀ := by
    have hc : ∀ ρ ∈ Z, refl s₀ R ρ s₀ ^ m ρ = (R : ℂ) ^ m ρ := fun ρ _ => by
      rw [refl_center hR]
    simp only [gfun]
    rw [Finset.prod_congr rfl hc, Finset.prod_pow_eq_pow_sum, hN]
  have hg₀n : ‖gfun s₀ R Z m h s₀‖ = R ^ N * ‖h s₀‖ := by
    rw [hg₀, norm_mul, norm_pow]
    rw [Complex.norm_real, Real.norm_of_nonneg hR.le]
  have hf₀ : ‖f s₀‖ ≤ R' ^ N * ‖h s₀‖ := by
    rw [hfac s₀ hs₀R, norm_mul, norm_prod]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc ∏ ρ ∈ Z, ‖(s₀ - ρ) ^ m ρ‖ = ∏ ρ ∈ Z, ‖s₀ - ρ‖ ^ m ρ := by simp only [norm_pow]
      _ ≤ ∏ ρ ∈ Z, R' ^ m ρ := by
        refine Finset.prod_le_prod (fun ρ _ => by positivity) fun ρ hρ => ?_
        have hρ' : ρ ∈ closedBall s₀ R' := ((hZ ρ).1 hρ).1
        rw [mem_closedBall, dist_eq_norm] at hρ'
        rw [norm_sub_rev]
        exact pow_le_pow_left₀ (norm_nonneg _) hρ' _
      _ = R' ^ N := by rw [Finset.prod_pow_eq_pow_sum, hN]
  have hsphere : ∀ z ∈ sphere s₀ R, ‖gfun s₀ R Z m h z‖ = ‖f z‖ := by
    intro z hz
    rw [hfac z (sphere_subset_closedBall hz)]
    simp only [gfun, norm_mul, norm_prod, norm_pow, norm_refl_sphere hR hz]
  have hdc : DiffContOnCl ℂ (gfun s₀ R Z m h) (ball s₀ R) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball s₀ hR.ne']
    exact differentiableOn_gfun_of_differentiableOn hh
  have hmax : ∀ z ∈ closedBall s₀ R,
      ‖gfun s₀ R Z m h z‖ ≤ Real.exp M * (R' ^ N * ‖h s₀‖) := by
    intro z hz
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc ?_
      (by rwa [closure_ball s₀ hR.ne'])
    intro w hw
    rw [frontier_ball s₀ hR.ne'] at hw
    rw [hsphere w hw]
    exact (hb w (sphere_subset_closedBall hw)).trans
      (mul_le_mul_of_nonneg_left hf₀ (Real.exp_pos M).le)
  have hkey : R ^ N ≤ Real.exp M * R' ^ N := by
    have h1 := hmax s₀ hs₀R
    rw [hg₀n, ← mul_assoc] at h1
    exact le_of_mul_le_mul_right h1 (norm_pos_iff.mpr hhs₀)
  refine ⟨fun z hz => ?_, ?_⟩
  · rw [hg₀n]
    refine (hmax z hz).trans ?_
    have hp : R' ^ N ≤ R ^ N := pow_le_pow_left₀ hR'.le hR'R.le N
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp (norm_nonneg _))
      (Real.exp_pos M).le
  · rw [hN]
    have hl := Real.log_le_log (pow_pos hR N) hkey
    rw [Real.log_mul (Real.exp_pos M).ne' (pow_pos hR' N).ne', Real.log_exp, Real.log_pow,
      Real.log_pow] at hl
    rw [Real.log_div hR.ne' hR'.ne', mul_sub]
    linarith
end PI.EF.Loc
