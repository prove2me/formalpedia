-- Prove2me | solution 1 for OnlineConvexOpt.ConvexBasics.constrained_gd_well_conditioned_convergence
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T07:15:05.901658+00:00
-- url     : https://prove2.me/submissions/561212b0-d9cd-4854-b63e-f4665339cc3a

import Mathlib
import Definitions.Def_OnlineConvexOpt_ConvexBasics_ConstrainedGradientDescent
import Definitions.Def_OnlineConvexOpt_ConvexBasics_StronglyConvexOn
import Definitions.Def_OnlineConvexOpt_ConvexBasics_SmoothOn

set_option autoImplicit false

open scoped InnerProductSpace

/-- The projected-gradient objective: `(β/2)‖x - (1/β)g - z‖² = ⟪g, z - x⟫ + (β/2)‖z - x‖² + ‖g‖²/(2β)`. -/
theorem oco_proj_model {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (β : ℝ) (hβ : 0 < β) (x gx z : E) :
    (β / 2) * ‖x - (1 / β) • gx - z‖ ^ 2
      = ⟪gx, z - x⟫_ℝ + (β / 2) * ‖z - x‖ ^ 2 + (1 / (2 * β)) * ‖gx‖ ^ 2 := by
  have e : x - (1 / β) • gx - z = -((z - x) + (1 / β) • gx) := by abel
  have hc : ⟪z - x, gx⟫_ℝ = ⟪gx, z - x⟫_ℝ := real_inner_comm _ _
  rw [e, norm_neg, norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ) < 1 / β), hc]
  field_simp
  ring

open OnlineConvexOpt.ConvexBasics OnlineConvexOpt.FirstOrder in
/-- One step of projected gradient descent contracts the gap by `1 - η` for any
`η ∈ [0, 1]` with `η β ≤ α`. -/
theorem oco_cgd_step {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (hK : Convex ℝ K) (f : E → ℝ) (g : E → E) (α β : ℝ) (hβ : 0 < β)
    (hsc : StronglyConvexOn K f g α) (hsm : SmoothOn K f g β)
    (xstar : E) (hxstarK : xstar ∈ K) (xt p : E) (hxt : xt ∈ K)
    (hp : IsMetricProjection K (xt - (1 / β) • g xt) p)
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hηα : η * β ≤ α) :
    f p - f xstar ≤ (1 - η) * (f xt - f xstar) := by
  obtain ⟨hpK, hpmin⟩ := hp
  set d := xstar - xt with hd
  set z := xt + η • d with hz
  have hzK : z ∈ K := hK.add_smul_sub_mem hxt hxstarK ⟨hη0, hη1⟩
  -- smoothness from `xt` to `p`
  have hA := hsm xt hxt p hpK
  -- projection optimality against `z`
  have hB : (β / 2) * ‖xt - (1 / β) • g xt - p‖ ^ 2
      ≤ (β / 2) * ‖xt - (1 / β) • g xt - z‖ ^ 2 := by
    have h1 := hpmin z hzK
    rw [dist_eq_norm, dist_eq_norm] at h1
    have h2 : ‖xt - (1 / β) • g xt - p‖ ^ 2 ≤ ‖xt - (1 / β) • g xt - z‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  rw [oco_proj_model β hβ, oco_proj_model β hβ] at hB
  have hzx : z - xt = η • d := by rw [hz]; abel
  rw [hzx, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη0] at hB
  -- strong convexity from `xt` to `xstar`
  have hC := hsc xt hxt xstar hxstarK
  rw [← hd] at hC
  have hq : η * (β * η - α) * ‖d‖ ^ 2 ≤ 0 := by
    have h1 : β * η - α ≤ 0 := by linarith
    have h2 : η * (β * η - α) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hη0 h1
    exact mul_nonpos_of_nonpos_of_nonneg h2 (sq_nonneg _)
  have hC' : η * ⟪g xt, d⟫_ℝ ≤ η * (f xstar - f xt - (α / 2) * ‖d‖ ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ hη0
    linarith
  nlinarith [hA, hB, hC', hq]

open OnlineConvexOpt.ConvexBasics in
theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Set E) (hK : Convex ℝ K) (f : E → ℝ) (g : E → E) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β)
    (hsc : StronglyConvexOn K f g α) (hsm : SmoothOn K f g β)
    (xstar : E) (hxstarK : xstar ∈ K) (hxstar : IsMinOn f K xstar)
    (x : ℕ → E) (hGD : IsConstrainedGradientDescent K f g β x) (t : ℕ) :
    f (x t) - f xstar ≤ (f (x 0) - f xstar) * Real.exp (-(α / β) * t / 4) := by
  obtain ⟨hx0, -, hproj⟩ := hGD
  have hmem : ∀ s, x s ∈ K := by
    intro s
    cases s with
    | zero => exact hx0
    | succ s => exact (hproj s).1
  have hnn : ∀ s, 0 ≤ f (x s) - f xstar := by
    intro s
    have := isMinOn_iff.mp hxstar (x s) (hmem s)
    linarith
  set γ := α / β with hγ
  have hγpos : 0 < γ := div_pos hα hβ
  -- a contraction factor `c ∈ [0, exp (-γ/4)]`
  obtain ⟨c, hc0, hcle, hstep⟩ : ∃ c : ℝ, 0 ≤ c ∧ c ≤ Real.exp (-γ / 4) ∧
      ∀ s, f (x (s + 1)) - f xstar ≤ c * (f (x s) - f xstar) := by
    by_cases h1 : γ ≤ 1
    · refine ⟨1 - γ, by linarith, ?_, ?_⟩
      · have e1 := Real.add_one_le_exp (-γ)
        have e2 : Real.exp (-γ) ≤ Real.exp (-γ / 4) := Real.exp_le_exp.mpr (by linarith)
        linarith
      · intro s
        refine oco_cgd_step K hK f g α β hβ hsc hsm xstar hxstarK (x s) (x (s + 1)) (hmem s)
          (hproj s) γ hγpos.le h1 ?_
        rw [hγ, div_mul_cancel₀ α hβ.ne']
    · push Not at h1
      refine ⟨0, le_refl _, (Real.exp_pos _).le, ?_⟩
      intro s
      have hβα : 1 * β ≤ α := by
        have : β < α := by
          have := (one_lt_div hβ).mp (by rw [← hγ]; exact h1)
          exact this
        linarith
      have := oco_cgd_step K hK f g α β hβ hsc hsm xstar hxstarK (x s) (x (s + 1)) (hmem s)
        (hproj s) 1 zero_le_one le_rfl hβα
      simpa using this
  induction t with
  | zero => simp
  | succ s ih =>
    have hE : 0 ≤ (f (x 0) - f xstar) * Real.exp (-γ * s / 4) :=
      mul_nonneg (hnn 0) (Real.exp_pos _).le
    calc f (x (s + 1)) - f xstar ≤ c * (f (x s) - f xstar) := hstep s
      _ ≤ c * ((f (x 0) - f xstar) * Real.exp (-γ * s / 4)) :=
          mul_le_mul_of_nonneg_left ih hc0
      _ ≤ Real.exp (-γ / 4) * ((f (x 0) - f xstar) * Real.exp (-γ * s / 4)) :=
          mul_le_mul_of_nonneg_right hcle hE
      _ = (f (x 0) - f xstar) * Real.exp (-γ * ((s + 1 : ℕ) : ℝ) / 4) := by
          rw [mul_left_comm, ← Real.exp_add]
          congr 2
          push_cast
          ring
