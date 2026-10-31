-- Prove2me | solution 1 for RiemOpt.FR.proposition_15
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-31T03:30:58.258784+00:00
-- url     : https://prove2.me/submissions/3811c975-f047-4b9e-a79d-108ed022f2b0

import Mathlib
import Definitions.Def_RiemOpt_FR_Setting

open Bundle Manifold
open scoped ContDiff

section

open Bundle Manifold
open scoped ContDiff

namespace RiemOpt.FR.RFFresh
end RiemOpt.FR.RFFresh
end

section

open Bundle Manifold
open scoped ContDiff

namespace RiemOpt.FR.RFFresh

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]

theorem line_derivative (f : M → ℝ)
    (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M)
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f)
    (hR : RiemOpt.BFGS.IsRetraction R) (x : M)
    (p : TangentSpace 𝓘(ℝ, E) x) (t : ℝ) :
    deriv (fun r : ℝ => f (R x (r • p))) t =
      RiemOpt.BFGS.Df f (R x (t • p)) (RiemOpt.BFGS.transport R x (t • p) p) := by
  have hr : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun v : E => R x v) (t • p) :=
    (hR x).1.mdifferentiable (by simp) _
  have hc := (hf (R x (t • p))).comp (f := fun v : E => R x v) (t • (p : E)) hr
  have hd : DifferentiableAt ℝ (fun v : E => f (R x v)) (t • p) :=
    mdifferentiableAt_iff_differentiableAt.mp hc
  have hh := hd.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const (p : E))
  have he := mfderiv_comp_apply (f := fun v : E => R x v) (g := f) (t • (p : E)) (hf (R x (t • p))) hr (p : E)
  erw [mfderiv_eq_fderiv] at he
  simp only [one_smul] at hh
  exact hh.deriv.trans he

theorem line_derivative_zero (f : M → ℝ)
    (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M)
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f)
    (hR : RiemOpt.BFGS.IsRetraction R) (x : M)
    (p : TangentSpace 𝓘(ℝ, E) x) :
    deriv (fun r : ℝ => f (R x (r • p))) 0 = RiemOpt.BFGS.Df f x p := by
  rw [line_derivative f R hf hR, zero_smul]
  change RiemOpt.BFGS.Df f (R x (0 : E))
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun w : E => R x w) (0 : E) (p : E)) = _
  rw [(hR x).2.2 p]
  erw [(hR x).2.1]

end RiemOpt.FR.RFFresh
end

section

open scoped BigOperators

namespace RiemOpt.FR.RFFresh

theorem scalar_decrease {c₁ c₂ L P s a F F' : ℝ}
    (hc₁ : 0 < c₁) (hL : 0 < L) (hP : 0 < P) (hs : s < 0)
    (hlow : (1 - c₂) * (-s) ≤ L * a * P ^ 2)
    (harmijo : F' ≤ F + c₁ * a * s) :
    (c₁ * (1 - c₂) / L) * (s ^ 2 / P ^ 2) ≤ F - F' := by
  have hden : 0 < L * P ^ 2 := mul_pos hL (sq_pos_of_pos hP)
  have ha : (1 - c₂) * (-s) / (L * P ^ 2) ≤ a := by
    apply (div_le_iff₀ hden).2
    nlinarith [hlow]
  have hh := mul_le_mul_of_nonneg_right ha (le_of_lt (mul_pos hc₁ (neg_pos.mpr hs)))
  have he : ((1 - c₂) * (-s) / (L * P ^ 2)) * (c₁ * (-s)) =
      (c₁ * (1 - c₂) / L) * (s ^ 2 / P ^ 2) := by ring
  rw [he] at hh
  nlinarith

theorem finite_decrease_sum (F Q : ℕ → ℝ) (K B : ℝ)
    (hB : ∀ k, B ≤ F k) (hstep : ∀ k, K * Q k ≤ F k - F (k + 1))
    (m : ℕ) : K * ∑ k ∈ Finset.range m, Q k ≤ F 0 - B := by
  have ht : ∀ m, K * ∑ k ∈ Finset.range m, Q k ≤ F 0 - F m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, mul_add]
      linarith [hstep m]
  exact (ht m).trans (sub_le_sub_left (hB m) _)

end RiemOpt.FR.RFFresh
end

section

open Bundle Manifold
open scoped ContDiff
namespace RiemOpt.FR.RFFresh
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]

theorem differential_eq_inner (f : M → ℝ)
    (grad : (x : M) → TangentSpace 𝓘(ℝ, E) x) (hg : IsGradient f grad) (x : M) :
    RiemOpt.BFGS.Df (E := E) f x = innerSL ℝ (grad x) := by
  ext v
  exact (hg x v).symm

theorem gradient_norm (f : M → ℝ)
    (grad : (x : M) → TangentSpace 𝓘(ℝ, E) x) (hg : IsGradient f grad) (x : M) :
    ‖grad x‖ = ‖RiemOpt.BFGS.Df (E := E) f x‖ := by
  rw [differential_eq_inner f grad hg x, innerSL_apply_norm]

theorem differential_gradient (f : M → ℝ)
    (grad : (x : M) → TangentSpace 𝓘(ℝ, E) x) (hg : IsGradient f grad) (x : M) :
    RiemOpt.BFGS.Df (E := E) f x (grad x) = ‖RiemOpt.BFGS.Df (E := E) f x‖ ^ 2 := by
  rw [← hg, real_inner_self_eq_norm_sq, gradient_norm f grad hg x]

omit [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)] in
theorem transported_eval (f : M → ℝ)
    (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M)
    (x : ℕ → M) (p : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)) (α : ℕ → ℝ)
    (hstep : ∀ k, x (k + 1) = R (x k) (α k • p k)) (k : ℕ) :
    RiemOpt.BFGS.Df (E := E) f (x (k + 1)) (transportedDir R x p α k) =
      RiemOpt.BFGS.Df (E := E) f (R (x k) (α k • p k))
        (RiemOpt.BFGS.transport R (x k) (α k • p k) (p k)) := by
  unfold transportedDir
  rw [hstep k]
end RiemOpt.FR.RFFresh
end

section
open Bundle Manifold
open scoped ContDiff
namespace RiemOpt.FR.RFFresh
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]

variable {f : M → ℝ} {R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M}
  {grad : (x : M) → TangentSpace 𝓘(ℝ, E) x} {c₁ c₂ : ℝ}
  {x : ℕ → M} {p : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)} {α : ℕ → ℝ}

theorem fr_initial (h : IsFRRun f R grad c₁ c₂ x p α) :
    -RiemOpt.BFGS.Df (E := E) f (x 0) (p 0) / ‖RiemOpt.BFGS.Df (E := E) f (x 0)‖ ^ 2 = 1 := by
  rw [h.dir_zero, map_neg, neg_neg, differential_gradient f grad h.isGradient]
  exact div_self (pow_ne_zero 2 ((norm_ne_zero_iff (a := RiemOpt.BFGS.Df (E := E) f (x 0))).mpr (h.nonstationary 0)))

theorem fr_normalized_step (h : IsFRRun f R grad c₁ c₂ x p α) (k : ℕ) :
    |(-RiemOpt.BFGS.Df (E := E) f (x (k + 1)) (p (k + 1)) /
      ‖RiemOpt.BFGS.Df (E := E) f (x (k + 1))‖ ^ 2) - 1| ≤
      c₂ * (-RiemOpt.BFGS.Df (E := E) f (x k) (p k) / ‖RiemOpt.BFGS.Df (E := E) f (x k)‖ ^ 2) := by
  have hkn := (norm_ne_zero_iff (a := RiemOpt.BFGS.Df (E := E) f (x k))).mpr (h.nonstationary k)
  have hnn := (norm_ne_zero_iff (a := RiemOpt.BFGS.Df (E := E) f (x (k + 1)))).mpr (h.nonstationary (k + 1))
  have hk := pow_pos ((norm_pos_iff (a := RiemOpt.BFGS.Df (E := E) f (x k))).mpr (h.nonstationary k)) 2
  have hn := pow_pos ((norm_pos_iff (a := RiemOpt.BFGS.Df (E := E) f (x (k + 1)))).mpr (h.nonstationary (k + 1))) 2
  have heq : (-RiemOpt.BFGS.Df (E := E) f (x (k + 1)) (p (k + 1)) /
      ‖RiemOpt.BFGS.Df (E := E) f (x (k + 1))‖ ^ 2) - 1 =
      -RiemOpt.BFGS.Df (E := E) f (x (k + 1)) (transportedDir R x p α k) /
        ‖RiemOpt.BFGS.Df (E := E) f (x k)‖ ^ 2 := by
    rw [h.dir_succ, map_add, map_neg, map_smul, differential_gradient f grad h.isGradient]
    simp only [smul_eq_mul]
    field_simp [hkn, hnn]
    ring
  rw [heq, abs_div, abs_neg, abs_of_pos hk]
  rw [transported_eval f R x p α h.step k]
  have hw := (h.strongWolfe k).2
  apply (div_le_iff₀ hk).2
  calc
    _ ≤ -(c₂ * RiemOpt.BFGS.Df (E := E) f (x k) (p k)) := hw
    _ = c₂ * (-RiemOpt.BFGS.Df (E := E) f (x k) (p k) /
        ‖RiemOpt.BFGS.Df (E := E) f (x k)‖ ^ 2) * ‖RiemOpt.BFGS.Df (E := E) f (x k)‖ ^ 2 := by
      field_simp [hkn]

theorem scalar_descent_interval (r : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c) (hc' : c < 1 / 2)
    (h0 : r 0 = 1) (hs : ∀ k, |r (k + 1) - 1| ≤ c * r k) :
    ∀ k, (1 - 2 * c) / (1 - c) ≤ r k ∧ r k ≤ 1 / (1 - c) := by
  have hd : 0 < 1 - c := by linarith
  have hid : (1 / (1 - c)) * (1 - c) = 1 := by field_simp
  have hlo : ((1 - 2 * c) / (1 - c)) * (1 - c) = 1 - 2 * c := by field_simp
  intro k
  induction k with
  | zero =>
    rw [h0]
    constructor
    · apply (div_le_iff₀ hd).2
      nlinarith
    · apply (le_div_iff₀ hd).2
      nlinarith
  | succ k ih =>
    have hab := abs_le.mp (hs k)
    have hm := mul_le_mul_of_nonneg_left ih.2 hc
    constructor
    · apply (div_le_iff₀ hd).2
      nlinarith
    · apply (le_div_iff₀ hd).2
      nlinarith

theorem descent_bounds (h : IsFRRun f R grad c₁ c₂ x p α) (hc : c₂ < 1 / 2) (k : ℕ) :
    ((1 - 2 * c₂) / (1 - c₂)) * ‖RiemOpt.BFGS.Df (E := E) f (x k)‖ ^ 2 ≤
      -RiemOpt.BFGS.Df (E := E) f (x k) (p k) ∧
    -RiemOpt.BFGS.Df (E := E) f (x k) (p k) ≤
      (1 / (1 - c₂)) * ‖RiemOpt.BFGS.Df (E := E) f (x k)‖ ^ 2 := by
  have hi := scalar_descent_interval
    (fun j => -RiemOpt.BFGS.Df (E := E) f (x j) (p j) / ‖RiemOpt.BFGS.Df (E := E) f (x j)‖ ^ 2)
    c₂ (le_of_lt (h.c₁_pos.trans h.c₁_lt_c₂)) hc (fr_initial h) (fr_normalized_step h) k
  have hg := pow_pos ((norm_pos_iff (a := RiemOpt.BFGS.Df (E := E) f (x k))).mpr (h.nonstationary k)) 2
  exact ⟨(le_div_iff₀ hg).mp hi.1, (div_le_iff₀ hg).mp hi.2⟩

theorem fr_descent (h : IsFRRun f R grad c₁ c₂ x p α) (hc : c₂ < 1 / 2) (k : ℕ) :
    RiemOpt.BFGS.Df (E := E) f (x k) (p k) < 0 := by
  have ha : 0 < (1 - 2 * c₂) / (1 - c₂) := div_pos (by linarith) (by linarith)
  have hp := mul_pos ha (pow_pos ((norm_pos_iff (a := RiemOpt.BFGS.Df (E := E) f (x k))).mpr (h.nonstationary k)) 2)
  have hh := (descent_bounds h hc k).1
  linarith
end RiemOpt.FR.RFFresh
end

section

open Bundle Manifold
open scoped ContDiff BigOperators

namespace RiemOpt.FR.RFFresh

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]

variable {f : M → ℝ} {R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M}
  {grad : (x : M) → TangentSpace 𝓘(ℝ, E) x} {c₁ c₂ : ℝ}
  {x : ℕ → M} {p : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)} {α : ℕ → ℝ}

 theorem native_decrease (h : IsFRRun f R grad c₁ c₂ x p α) (hc : c₂ < 1 / 2)
    {L : ℝ} (hL : 0 < L) (hlip : LineLipschitz f R x p L) (k : ℕ) :
    (c₁ * (1 - c₂) / L) * ((RiemOpt.BFGS.Df (E := E) f (x k) (p k)) ^ 2 / ‖p k‖ ^ 2) ≤
      f (x k) - f (x (k + 1)) := by
  have hs := fr_descent h hc k
  have hp : 0 < ‖p k‖ := norm_pos_iff.mpr (by
    intro hz
    simp only [hz, map_zero] at hs
    exact (lt_irrefl 0 hs))
  have hl := (hlip k).2 (α k) 0
  rw [line_derivative f R h.differentiable h.isRetraction,
    line_derivative_zero f R h.differentiable h.isRetraction] at hl
  have ha : |α k - 0| = α k := by simp [le_of_lt (h.step_pos k)]
  rw [ha] at hl
  have hw := (h.strongWolfe k).2
  have he := (abs_le.mp hl).2
  have hw' := neg_abs_le (RiemOpt.BFGS.Df (E := E) f (R (x k) (α k • p k))
    (RiemOpt.BFGS.transport R (x k) (α k • p k) (p k)))
  apply scalar_decrease (a := α k) (c₂ := c₂) h.c₁_pos hL hp hs
  · nlinarith
  · rw [h.step k]
    exact (h.strongWolfe k).1

 theorem native_zoutendijk_bound (h : IsFRRun f R grad c₁ c₂ x p α) (hc : c₂ < 1 / 2)
    (hbdd : BddBelow (Set.range f)) {L : ℝ} (hL : 0 < L)
    (hlip : LineLipschitz f R x p L) :
    ∃ B : ℝ, ∀ m : ℕ, ∑ k ∈ Finset.range m,
      (RiemOpt.BFGS.Df (E := E) f (x k) (p k)) ^ 2 / ‖p k‖ ^ 2 ≤ B := by
  obtain ⟨b, hb⟩ := hbdd
  let K := c₁ * (1 - c₂) / L
  have hK : 0 < K := div_pos (mul_pos h.c₁_pos (by linarith)) hL
  refine ⟨(f (x 0) - b) / K, fun m => ?_⟩
  apply (le_div_iff₀ hK).2
  rw [mul_comm]
  exact finite_decrease_sum (fun k => f (x k))
    (fun k => (RiemOpt.BFGS.Df (E := E) f (x k) (p k)) ^ 2 / ‖p k‖ ^ 2) K b
    (fun k => hb ⟨x k, rfl⟩) (native_decrease h hc hL hlip) m

end RiemOpt.FR.RFFresh
end

section
open Bundle Manifold
open scoped ContDiff
namespace RiemOpt.FR.RFFresh
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
variable {f : M → ℝ} {R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M}
  {grad : (x : M) → TangentSpace 𝓘(ℝ, E) x} {c₁ c₂ : ℝ}
  {x : ℕ → M} {p : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)} {α : ℕ → ℝ}

theorem direction_sq_step (h : IsFRRun f R grad c₁ c₂ x p α) (hc : c₂ < 1 / 2)
    (hT : ∀ k, ‖transportedDir R x p α k‖ ≤ ‖p k‖) (k : ℕ) :
    ‖p (k + 1)‖ ^ 2 ≤
      ((1 + c₂) / (1 - c₂)) * ‖RiemOpt.BFGS.Df (E := E) f (x (k + 1))‖ ^ 2 +
      (‖RiemOpt.BFGS.Df (E := E) f (x (k + 1))‖ ^ 2 /
        ‖RiemOpt.BFGS.Df (E := E) f (x k)‖ ^ 2) ^ 2 * ‖p k‖ ^ 2 := by
  let g := ‖RiemOpt.BFGS.Df (E := E) f (x k)‖ ^ 2
  let gn := ‖RiemOpt.BFGS.Df (E := E) f (x (k + 1))‖ ^ 2
  let b := gn / g
  have hg : 0 < g := pow_pos ((norm_pos_iff (a := RiemOpt.BFGS.Df (E := E) f (x k))).mpr (h.nonstationary k)) 2
  have hgn : 0 < gn := pow_pos ((norm_pos_iff (a := RiemOpt.BFGS.Df (E := E) f (x (k + 1)))).mpr (h.nonstationary (k + 1))) 2
  have hb : 0 < b := div_pos hgn hg
  have hc0 : 0 < c₂ := h.c₁_pos.trans h.c₁_lt_c₂
  have hd : 0 < 1 - c₂ := by linarith
  have he := (h.strongWolfe k).2
  rw [← transported_eval f R x p α h.step k] at he
  have hl := (abs_le.mp he).1
  have hu := (descent_bounds h hc k).2
  have hm := mul_le_mul_of_nonneg_left hu hc0.le
  have heval : -c₂ * (1 / (1 - c₂)) * g ≤
      RiemOpt.BFGS.Df (E := E) f (x (k + 1)) (transportedDir R x p α k) := by
    dsimp [g]
    nlinarith
  have hnorm : ‖transportedDir R x p α k‖ ^ 2 ≤ ‖p k‖ ^ 2 :=
    sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr (hT k)
  have hexpand : ‖p (k + 1)‖ ^ 2 = gn -
      2 * b * RiemOpt.BFGS.Df (E := E) f (x (k + 1)) (transportedDir R x p α k) +
      b ^ 2 * ‖transportedDir R x p α k‖ ^ 2 := by
    rw [h.dir_succ, norm_add_sq_real]
    simp only [norm_neg, inner_neg_left, real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
    rw [h.isGradient]
    rw [gradient_norm f grad h.isGradient]
    dsimp [gn, b, g]
    ring
  have hcross := mul_le_mul_of_nonneg_left heval (by positivity : 0 ≤ 2 * b)
  have hn := mul_le_mul_of_nonneg_left hnorm (sq_nonneg b)
  have hbg : b * g = gn := by dsimp [b]; field_simp
  have hbgc := congrArg (fun z : ℝ => 2 * c₂ * (1 / (1 - c₂)) * z) hbg
  have hcoef : ((1 + c₂) / (1 - c₂)) = 1 + 2 * c₂ * (1 / (1 - c₂)) := by
    field_simp
    ring
  change ‖p (k + 1)‖ ^ 2 ≤ ((1 + c₂) / (1 - c₂)) * gn + b ^ 2 * ‖p k‖ ^ 2
  rw [hcoef]
  nlinarith

theorem direction_normalized_step (h : IsFRRun f R grad c₁ c₂ x p α) (hc : c₂ < 1 / 2)
    (hT : ∀ k, ‖transportedDir R x p α k‖ ≤ ‖p k‖) (k : ℕ) :
    ‖p (k + 1)‖ ^ 2 / ‖RiemOpt.BFGS.Df (E := E) f (x (k + 1))‖ ^ 4 ≤
      ‖p k‖ ^ 2 / ‖RiemOpt.BFGS.Df (E := E) f (x k)‖ ^ 4 +
      ((1 + c₂) / (1 - c₂)) / ‖RiemOpt.BFGS.Df (E := E) f (x (k + 1))‖ ^ 2 := by
  have hk := (norm_pos_iff (a := RiemOpt.BFGS.Df (E := E) f (x k))).mpr (h.nonstationary k)
  have hn := (norm_pos_iff (a := RiemOpt.BFGS.Df (E := E) f (x (k + 1)))).mpr (h.nonstationary (k + 1))
  have hh := div_le_div_of_nonneg_right (direction_sq_step h hc hT k)
    (le_of_lt (pow_pos hn 4))
  calc
    _ ≤ _ := hh
    _ = _ := by
      field_simp [ne_of_gt hk, ne_of_gt hn]
      ring
end RiemOpt.FR.RFFresh
end

section
open Bundle Manifold
open scoped ContDiff
namespace RiemOpt.FR.RFFresh
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
variable {f : M → ℝ} {R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M}
  {grad : (x : M) → TangentSpace 𝓘(ℝ, E) x} {c₁ c₂ : ℝ}
  {x : ℕ → M} {p : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)} {α : ℕ → ℝ}

theorem direction_normalized_initial (h : IsFRRun f R grad c₁ c₂ x p α) :
    ‖p 0‖ ^ 2 / ‖RiemOpt.BFGS.Df (E := E) f (x 0)‖ ^ 4 =
      1 / ‖RiemOpt.BFGS.Df (E := E) f (x 0)‖ ^ 2 := by
  have hg := (norm_ne_zero_iff (a := RiemOpt.BFGS.Df (E := E) f (x 0))).mpr (h.nonstationary 0)
  rw [h.dir_zero, norm_neg, gradient_norm f grad h.isGradient]
  field_simp
end RiemOpt.FR.RFFresh
end

section

open scoped BigOperators
namespace RiemOpt.FR.RFFresh

lemma scalar_growth_sum (u v : ℕ → ℝ) (C : ℝ)
    (h0 : u 0 ≤ C*v 0) (hstep : ∀ k, u (k+1) ≤ u k+C*v (k+1)) :
    ∀ k, u k ≤ C*∑ j ∈ Finset.range (k+1), v j := by
  intro k
  induction k with
  | zero => simpa using h0
  | succ k ih =>
    rw [Finset.sum_range_succ]
    calc
      u (k+1) ≤ u k+C*v (k+1) := hstep k
      _ ≤ C*(∑ j ∈ Finset.range (k+1), v j)+C*v (k+1) := add_le_add ih le_rfl
      _ = _ := by ring

end RiemOpt.FR.RFFresh
end

section
open Bundle Manifold
open scoped ContDiff
namespace RiemOpt.FR.RFFresh
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
variable {f : M → ℝ} {R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M}
  {grad : (x : M) → TangentSpace 𝓘(ℝ, E) x} {c₁ c₂ : ℝ}
  {x : ℕ → M} {p : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)} {α : ℕ → ℝ}

theorem direction_normalized (h : IsFRRun f R grad c₁ c₂ x p α) (hc : c₂ < 1 / 2)
    (hT : ∀ k, ‖transportedDir R x p α k‖ ≤ ‖p k‖) (k : ℕ) :
    ‖p k‖ ^ 2 / ‖RiemOpt.BFGS.Df (E := E) f (x k)‖ ^ 4 ≤
      ((1 + c₂) / (1 - c₂)) *
        ∑ j ∈ Finset.range (k + 1), 1 / ‖RiemOpt.BFGS.Df (E := E) f (x j)‖ ^ 2 := by
  have hc0 : 0 < c₂ := h.c₁_pos.trans h.c₁_lt_c₂
  have hd : 0 < 1 - c₂ := by linarith
  have hC : 1 ≤ (1 + c₂) / (1 - c₂) := (le_div_iff₀ hd).2 (by linarith)
  apply scalar_growth_sum
    (fun j => ‖p j‖ ^ 2 / ‖RiemOpt.BFGS.Df (E := E) f (x j)‖ ^ 4)
    (fun j => 1 / ‖RiemOpt.BFGS.Df (E := E) f (x j)‖ ^ 2)
    ((1 + c₂) / (1 - c₂)) _ _ k
  · rw [direction_normalized_initial h]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hC
      (by positivity : 0 ≤ 1 / ‖RiemOpt.BFGS.Df (E := E) f (x 0)‖ ^ 2)
  · intro j
    simpa only [mul_one_div] using direction_normalized_step h hc hT j
end RiemOpt.FR.RFFresh
end

section

open scoped BigOperators
open Filter
namespace RiemOpt.FR.RFFresh

lemma small_norms_of_direction_bound (G P : ℕ → ℝ) (C M : ℝ)
    (hG : ∀ k, 0 < G k) (hP : ∀ k, 0 < P k) (hC : 0 < C)
    (hdir : ∀ k, (P k)^2/(G k)^4 ≤ C * ∑ j ∈ Finset.range (k+1), 1/(G j)^2)
    (hsum : ∀ m, (∑ k ∈ Finset.range m, (G k)^4/(P k)^2) ≤ M) :
    ∀ ε > 0, ∀ N : ℕ, ∃ k ≥ N, G k < ε := by
  intro ε hε N
  by_contra hbad
  push Not at hbad
  let H := (∑ j ∈ Finset.range N, 1/(G j)^2) + 1/ε^2
  have hprefix : 0 ≤ ∑ j ∈ Finset.range N, 1/(G j)^2 := by
    apply Finset.sum_nonneg
    intro j _
    positivity
  have hH : 0 < H := by dsimp [H]; positivity
  have hinv (j : ℕ) : 1/(G j)^2 ≤ H := by
    by_cases hj : j < N
    · have hle : 1/(G j)^2 ≤ ∑ i ∈ Finset.range N, 1/(G i)^2 :=
        Finset.single_le_sum (f := fun i : ℕ => (1 : ℝ)/(G i)^2) (fun i _ => by positivity) (Finset.mem_range.mpr hj)
      dsimp [H]
      linarith [show (0:ℝ) ≤ 1/ε^2 by positivity]
    · have heG : ε ≤ G j := hbad j (by omega)
      have hsquare : ε^2 ≤ (G j)^2 := by nlinarith [hG j]
      have hle := one_div_le_one_div_of_le (by positivity : (0:ℝ) < ε^2) hsquare
      dsimp [H]
      linarith
  have hpartial (k : ℕ) :
      (∑ j ∈ Finset.range (k+1), 1/(G j)^2) ≤ ((k:ℝ)+1)*H := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (k+1), H := Finset.sum_le_sum fun j _ => hinv j
      _ = _ := by simp
  have hpoint (k : ℕ) : 1/((k:ℝ)+1) ≤ (C*H)*((G k)^4/(P k)^2) := by
    have hg4 : 0 < (G k)^4 := pow_pos (hG k) _
    have hp2 : 0 < (P k)^2 := pow_pos (hP k) _
    have hk1 : (0:ℝ) < (k:ℝ)+1 := by positivity
    have hbound := (hdir k).trans (mul_le_mul_of_nonneg_left (hpartial k) hC.le)
    have hcross := (div_le_iff₀ hg4).mp hbound
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hk1 hp2).mpr
    nlinarith
  have hbounded (m : ℕ) :
      (∑ k ∈ Finset.range m, (1:ℝ)/((k:ℝ)+1)) ≤ (C*H)*M := by
    calc
      _ ≤ ∑ k ∈ Finset.range m, (C*H)*((G k)^4/(P k)^2) :=
        Finset.sum_le_sum fun k _ => hpoint k
      _ = (C*H)*(∑ k ∈ Finset.range m, (G k)^4/(P k)^2) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hsum m) (mul_pos hC hH).le
  obtain ⟨m, hm⟩ :=
    (Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually_gt_atTop ((C*H)*M)).exists
  exact (not_lt_of_ge (hbounded m)) hm

end RiemOpt.FR.RFFresh
end

section

open scoped BigOperators
namespace RiemOpt.FR.RFFresh

lemma small_norms_of_zoutendijk (G P s : ℕ → ℝ) (A C M : ℝ)
    (hG : ∀ k, 0 < G k) (hP : ∀ k, 0 < P k) (hA : 0 < A) (hC : 0 < C)
    (hdescent : ∀ k, A*(G k)^2 ≤ -s k)
    (hdir : ∀ k, (P k)^2/(G k)^4 ≤ C * ∑ j ∈ Finset.range (k+1), 1/(G j)^2)
    (hsum : ∀ m, (∑ k ∈ Finset.range m, (s k)^2/(P k)^2) ≤ M) :
    ∀ ε > 0, ∀ N : ℕ, ∃ k ≥ N, G k < ε := by
  have hpoint (k : ℕ) : (G k)^4/(P k)^2 ≤ ((s k)^2/(P k)^2)/A^2 := by
    have hs := mul_self_le_mul_self (by positivity : 0 ≤ A*(G k)^2) (hdescent k)
    have hg : (G k)^4 ≤ (s k)^2/A^2 := by
      apply (le_div_iff₀ (pow_pos hA 2)).mpr
      nlinarith
    have hh := div_le_div_of_nonneg_right hg (sq_nonneg (P k))
    calc
      _ ≤ ((s k)^2/A^2)/(P k)^2 := hh
      _ = _ := by ring
  apply small_norms_of_direction_bound G P C (M/A^2) hG hP hC hdir
  intro m
  calc
    _ ≤ ∑ k ∈ Finset.range m, ((s k)^2/(P k)^2)/A^2 :=
      Finset.sum_le_sum fun k _ => hpoint k
    _ = (∑ k ∈ Finset.range m, (s k)^2/(P k)^2)/A^2 := by rw [Finset.sum_div]
    _ ≤ _ := div_le_div_of_nonneg_right (hsum m) (sq_nonneg A)

end RiemOpt.FR.RFFresh
end

section

open Bundle Manifold
open scoped ContDiff BigOperators

namespace RiemOpt.FR.RFFresh

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]

theorem native_proposition_15
    (f : M → ℝ) (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M)
    (grad : (x : M) → TangentSpace 𝓘(ℝ, E) x) (c₁ c₂ : ℝ)
    (x : ℕ → M) (p : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)) (α : ℕ → ℝ)
    (hrun : IsFRRun f R grad c₁ c₂ x p α) (hc₂ : c₂ < 1 / 2)
    (hT : ∀ k : ℕ, ‖transportedDir R x p α k‖ ≤ ‖p k‖)
    (hbdd : BddBelow (Set.range f)) (L : ℝ) (hL : 0 < L) (hlip : LineLipschitz f R x p L) :
    ∀ ε > 0, ∀ N : ℕ, ∃ k ≥ N, ‖RiemOpt.BFGS.Df (E := E) f (x k)‖ < ε := by
  let G : ℕ → ℝ := fun k => ‖RiemOpt.BFGS.Df (E := E) f (x k)‖
  let P : ℕ → ℝ := fun k => ‖p k‖
  let s : ℕ → ℝ := fun k => RiemOpt.BFGS.Df (E := E) f (x k) (p k)
  let A : ℝ := (1 - 2 * c₂) / (1 - c₂)
  let C : ℝ := (1 + c₂) / (1 - c₂)
  have hc0 : 0 < c₂ := hrun.c₁_pos.trans hrun.c₁_lt_c₂
  have hA : 0 < A := div_pos (by linarith) (by linarith)
  have hC : 0 < C := div_pos (by linarith) (by linarith)
  have hG (k : ℕ) : 0 < G k := by
    exact (norm_pos_iff (a := RiemOpt.BFGS.Df (E := E) f (x k))).2 (hrun.nonstationary k)
  have hP (k : ℕ) : 0 < P k := by
    apply norm_pos_iff.mpr
    intro hz
    have hh := fr_descent hrun hc₂ k
    rw [hz, map_zero] at hh
    exact (lt_irrefl 0 hh)
  obtain ⟨B, hB⟩ := native_zoutendijk_bound hrun hc₂ hbdd hL hlip
  apply small_norms_of_zoutendijk G P s A C B hG hP hA hC
  · exact fun k => (descent_bounds hrun hc₂ k).1
  · exact direction_normalized hrun hc₂ hT
  · exact hB

end RiemOpt.FR.RFFresh
end

open Bundle Manifold RiemOpt.FR
open scoped ContDiff
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]


    (f : M → ℝ) (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M)
    (grad : (x : M) → TangentSpace 𝓘(ℝ, E) x) (c₁ c₂ : ℝ)
    (x : ℕ → M) (p : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)) (α : ℕ → ℝ)
    (hrun : IsFRRun f R grad c₁ c₂ x p α) (hc₂ : c₂ < 1 / 2)
    (hT : ∀ k : ℕ, ‖transportedDir R x p α k‖ ≤ ‖p k‖)
    (hbdd : BddBelow (Set.range f)) (L : ℝ) (hL : 0 < L) (hlip : LineLipschitz f R x p L) :
    ∀ ε > 0, ∀ N : ℕ, ∃ k ≥ N, ‖RiemOpt.BFGS.Df (E := E) f (x k)‖ < ε := by
  exact RFFresh.native_proposition_15 f R grad c₁ c₂ x p α hrun hc₂ hT hbdd L hL hlip
