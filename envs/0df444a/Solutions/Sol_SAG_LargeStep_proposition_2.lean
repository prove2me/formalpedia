-- Prove2me | solution 1 for SAG.LargeStep.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-22T22:50:06.485912+00:00
-- url     : https://prove2.me/submissions/cadb9e56-c4c8-4a9b-a202-dfefe35c8bd5

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum
import Definitions.Def_SAGA_Convex_sagaRun
import Definitions.Def_SAG_LargeStep_setting
import Definitions.Def_SAG_LargeStep_hybrid

open scoped BigOperators

namespace SAGLargeStepProof
abbrev V (p : ℕ) := EuclideanSpace ℝ (Fin p)
noncomputable def stepSize (n : ℕ) (μ : ℝ) : ℝ := 1 / (2 * (n : ℝ) * μ)
noncomputable def rate (n : ℕ) : ℝ := 1 - 1 / (8 * (n : ℝ))
noncomputable def gap {p n : ℕ} (f : Fin n → V p → ℝ)
    (xstar x : V p) : ℝ := SAGA.Convex.fAvg f x - SAGA.Convex.fAvg f xstar
noncomputable def warmStart {p n K : ℕ} (f' : Fin n → V p → V p)
    (L μ : ℝ) (x0 : V p) (js : Fin K → Fin n) : V p :=
  (1 / (K : ℝ)) • ∑ j ∈ Finset.range K,
    SAG.LargeStep.sgIterate f' (SAG.LargeStep.sgStepSize L μ) x0 js j
noncomputable def lyapunov {p n : ℕ} (f : Fin n → V p → ℝ)
    (f' : Fin n → V p → V p) (μ : ℝ) (xstar : V p)
    (θ : (Fin n → V p) × V p) : ℝ :=
  2 * gap f xstar (θ.2 + (stepSize n μ / (n : ℝ)) • ∑ i, θ.1 i)
    + (1 / ((n : ℝ)^2 * μ)) * (∑ i, ‖θ.1 i - f' i xstar‖^2)
    + (((n : ℝ) - 1) / (2 * (n : ℝ)^3 * μ)) * ‖∑ i, θ.1 i‖^2
    - (1 / (n : ℝ)) * inner ℝ (∑ i, θ.1 i) (θ.2 - xstar)
end SAGLargeStepProof

open scoped BigOperators
open Set InnerProductSpace

namespace SAGLargeStepProof

variable {p : ℕ}

theorem gradient_support (f : V p → ℝ) (g : V p → V p)
    (hf : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x) (x y : V p) :
    f x + inner ℝ (g x) (y-x) ≤ f y := by
  have hc := hf.comp_affineMap (AffineMap.lineMap x y)
  have hd := (hg (AffineMap.lineMap x y (0 : ℝ))).hasFDerivAt.comp_hasDerivAt
    0 (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := (0 : ℝ)))
  have hs := hc.le_slope_of_hasDerivAt (x := (0 : ℝ)) (y := 1)
    (by simp) (by simp) (by norm_num) hd
  simp only [slope_def_field, Function.comp_apply, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one, sub_zero, div_one, toDual_apply_apply] at hs
  linarith

theorem smooth_descent (f : V p → ℝ) (g : V p → V p) (L : ℝ)
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hLip : ∀ x y, ‖g x-g y‖ ≤ L*‖x-y‖) (x d : V p) :
    f (x+d) ≤ f x + inner ℝ (g x) d + L/2*‖d‖^2 := by
  let φ : ℝ → ℝ := fun t => f (x+t•d)-f x-t*inner ℝ (g x) d-(L/2*‖d‖^2)*t^2
  have hd (t : ℝ) : HasDerivAt φ
      (inner ℝ (g (x+t•d)-g x) d-L*t*‖d‖^2) t := by
    have hp : HasDerivAt (fun t : ℝ => x+t•d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add x
    have hh := (((hg (x+t•d)).hasFDerivAt.comp_hasDerivAt t hp).sub_const (f x)).sub
      ((hasDerivAt_id t).mul_const (inner ℝ (g x) d))
    have hh' := hh.sub (((hasDerivAt_id t).pow 2).const_mul (L/2*‖d‖^2))
    simp only [toDual_apply_apply] at hh'
    convert! hh' using 1
    simp only [inner_sub_left, id_eq]
    ring
  have hn (t : ℝ) (ht : 0 ≤ t) :
      inner ℝ (g (x+t•d)-g x) d-L*t*‖d‖^2 ≤ 0 := by
    have hb : ‖g (x+t•d)-g x‖ ≤ L*(t*‖d‖) := by
      simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] using hLip (x+t•d) x
    have hi := real_inner_le_norm (g (x+t•d)-g x) d
    have hm := mul_le_mul_of_nonneg_right hb (norm_nonneg d)
    nlinarith
  have ha : AntitoneOn φ (Ici (0 : ℝ)) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      (fun t _ => (hd t).continuousAt.continuousWithinAt)
      (fun t _ => (hd t).hasDerivWithinAt)
      (fun t ht => hn t (interior_subset ht))
  have hh := ha (show (0 : ℝ) ∈ Ici 0 from mem_Ici.mpr le_rfl) (show (1 : ℝ) ∈ Ici 0 by norm_num)
    (show (0 : ℝ) ≤ 1 by norm_num)
  simp only [φ, zero_smul, add_zero, zero_mul, sub_self, zero_pow (by decide : 2 ≠ 0),
    one_smul, one_mul, one_pow, mul_one] at hh
  linarith

theorem cocoercive (f : V p → ℝ) (g : V p → V p) (L : ℝ) (hL : 0 < L)
    (hf : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (hLip : ∀ x y, ‖g x-g y‖ ≤ L*‖x-y‖) (x y : V p) :
    ‖g x-g y‖^2 ≤ L*inner ℝ (g x-g y) (x-y) := by
  have half (a b : V p) :
      ‖g a-g b‖^2/(2*L) ≤ f a-f b-inner ℝ (g b) (a-b) := by
    let d := -(L⁻¹) • (g a-g b)
    have hu := smooth_descent f g L hg hLip a d
    have hl := gradient_support f g hf hg b (a+d)
    have hid : inner ℝ (g a-g b) (g a-g b) = ‖g a-g b‖^2 := real_inner_self_eq_norm_sq _
    simp only [inner_sub_left, inner_sub_right] at hid
    have hd : ‖d‖^2 = (L⁻¹)^2*‖g a-g b‖^2 := by
      simp [d, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [hd] at hu
    simp only [d, inner_sub_right, inner_add_right, inner_smul_right] at hu hl
    have hi : inner ℝ (g b) a-inner ℝ (g b) b = inner ℝ (g b) (a-b) :=
      (inner_sub_right _ _ _).symm
    have hh : f b+inner ℝ (g b) (a-b) ≤ f a-(1/(2*L))*‖g a-g b‖^2 := by
      have hid' := congrArg (fun z : ℝ => L⁻¹*z) hid
      have hc : L/2*((L⁻¹)^2*‖g a-g b‖^2) =
          (L⁻¹-1/(2*L))*‖g a-g b‖^2 := by
        field_simp
        ring
      nlinarith
    calc
      ‖g a-g b‖^2/(2*L) = (1/(2*L))*‖g a-g b‖^2 := by ring
      _ ≤ f a-f b-inner ℝ (g b) (a-b) := by linarith only [hh]
  have hxy := (div_le_iff₀ (show 0 < 2*L by positivity)).mp (half x y)
  have hyx := (div_le_iff₀ (show 0 < 2*L by positivity)).mp (half y x)
  rw [norm_sub_rev (g y) (g x)] at hyx
  simp only [inner_sub_left, inner_sub_right] at hxy hyx ⊢
  nlinarith

variable {n : ℕ} (f : Fin n → V p → ℝ) (f' : Fin n → V p → V p)
  (L μ : ℝ) (xstar : V p) (h : SAG.LargeStep.Assumptions f f' L μ xstar)
include h

theorem avg_hasGradient (x : V p) :
    HasGradientAt (SAGA.Convex.fAvg f) (SAGA.Convex.gradAvg f' x) x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  change HasFDerivAt (fun y => (1/(n:ℝ))*(∑ i, f i y)) _ x
  simpa [SAGA.Convex.gradAvg, map_smul, map_sum, Pi.smul_def, smul_eq_mul] using
    (HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => (h.hasGradient i x).hasFDerivAt)).const_smul
      (1/(n : ℝ))

theorem avg_convex : ConvexOn ℝ univ (SAGA.Convex.fAvg f) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    (h.convex i).2 hx hy ha hb hab)
  have hn : 0 ≤ 1/(n : ℝ) := by positivity
  have hm := mul_le_mul_of_nonneg_left hh hn
  simpa [SAGA.Convex.fAvg, Finset.sum_add_distrib, Finset.mul_sum, smul_eq_mul,
    mul_add, mul_assoc, mul_left_comm] using hm

theorem avg_lipschitz (x y : V p) :
    ‖SAGA.Convex.gradAvg f' x-SAGA.Convex.gradAvg f' y‖ ≤ L*‖x-y‖ := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr h.n_pos
  rw [SAGA.Convex.gradAvg, SAGA.Convex.gradAvg, ← smul_sub, ← Finset.sum_sub_distrib,
    norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hn)]
  calc
    (1/(n:ℝ))*‖∑ i, (f' i x-f' i y)‖ ≤
        (1/(n:ℝ))*∑ i, ‖f' i x-f' i y‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (1/(n:ℝ))*∑ _i : Fin n, L*‖x-y‖ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => h.lipschitz i x y)) (by positivity)
    _ = L*‖x-y‖ := by simp; field_simp

theorem avg_support (x y : V p) :
    SAGA.Convex.fAvg f x+inner ℝ (SAGA.Convex.gradAvg f' x) (y-x) ≤ SAGA.Convex.fAvg f y :=
  gradient_support _ _ (avg_convex f f' L μ xstar h) (avg_hasGradient f f' L μ xstar h) x y

theorem avg_strong_support (x y : V p) :
    SAGA.Convex.fAvg f x+inner ℝ (SAGA.Convex.gradAvg f' x) (y-x)
      +(μ/2)*‖y-x‖^2 ≤ SAGA.Convex.fAvg f y := by
  have hg (z : V p) : HasGradientAt (fun z => SAGA.Convex.fAvg f z-μ/2*‖z‖^2)
      (SAGA.Convex.gradAvg f' z-μ•z) z := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    convert! (avg_hasGradient f f' L μ xstar h z).hasFDerivAt.sub
      ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_mul (μ/2)) using 1
    ext v
    simp
    ring
  have hs := gradient_support _ _ h.strongConvex hg x y
  simp only [inner_sub_left, real_inner_smul_left, inner_sub_right,
    real_inner_self_eq_norm_sq] at hs
  have hid := norm_sub_sq_real y x
  rw [real_inner_comm x y] at hid
  simp only [inner_sub_right]
  have hid' := congrArg (fun z : ℝ => μ*z) hid
  nlinarith

theorem grad_star_zero : SAGA.Convex.gradAvg f' xstar = 0 := by
  have hm : IsLocalMin (SAGA.Convex.fAvg f) xstar := Filter.Eventually.of_forall h.minimizer
  have hz := hm.hasFDerivAt_eq_zero (avg_hasGradient f f' L μ xstar h xstar).hasFDerivAt
  apply (toDual ℝ (V p)).injective
  simpa using hz

theorem grad_sum_star_zero : (∑ i, f' i xstar) = 0 := by
  have hn : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr h.n_pos).ne'
  have hz := congrArg (fun z : V p => (n : ℝ) • z) (grad_star_zero f f' L μ xstar h)
  simpa [SAGA.Convex.gradAvg, smul_smul, hn] using hz

theorem component_cocoercive (i : Fin n) (x y : V p) :
    ‖f' i x-f' i y‖^2 ≤ L*inner ℝ (f' i x-f' i y) (x-y) :=
  cocoercive _ _ L h.L_pos (h.convex i) (h.hasGradient i) (h.lipschitz i) x y

theorem table_gradient_bound (x : V p) :
    (∑ i, ‖f' i x-f' i xstar‖^2) ≤
      (n : ℝ)*L*inner ℝ (SAGA.Convex.gradAvg f' x) (x-xstar) := by
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    component_cocoercive f f' L μ xstar h i x xstar)
  have hn : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr h.n_pos).ne'
  rw [← Finset.mul_sum, ← sum_inner, Finset.sum_sub_distrib,
    grad_sum_star_zero f f' L μ xstar h, sub_zero] at hh
  simpa [SAGA.Convex.gradAvg, real_inner_smul_left, hn, mul_assoc, mul_left_comm] using hh

theorem gap_strong (x : V p) : (μ/2)*‖x-xstar‖^2 ≤ gap f xstar x := by
  have hh := avg_strong_support f f' L μ xstar h xstar x
  rw [grad_star_zero f f' L μ xstar h, inner_zero_left] at hh
  dsimp [gap]
  linarith

theorem gap_nonneg (x : V p) : 0 ≤ gap f xstar x := sub_nonneg.mpr (h.minimizer x)

theorem gap_le_inner (x : V p) :
    gap f xstar x ≤ inner ℝ (SAGA.Convex.gradAvg f' x) (x-xstar) := by
  have hh := avg_support f f' L μ xstar h x xstar
  simp only [inner_sub_right] at hh ⊢
  dsimp [gap]
  linarith

theorem strong_inner (x : V p) :
    μ*‖x-xstar‖^2 ≤ inner ℝ (SAGA.Convex.gradAvg f' x) (x-xstar) := by
  have ha := avg_strong_support f f' L μ xstar h x xstar
  have hb := gap_strong f f' L μ xstar h x
  rw [norm_sub_rev xstar x] at ha
  simp only [inner_sub_right] at ha ⊢
  dsimp [gap] at hb
  linarith

end SAGLargeStepProof

open scoped BigOperators
open SAGA.Convex

namespace SAGLargeStepProof

 theorem expectIdx_snoc {n k : ℕ} (hn : 0 < n)
    (F : (Fin (k + 1) → Fin n) → ℝ) :
    expectIdx n (k + 1) F = expectIdx n k (fun js =>
      (1 / (n : ℝ)) * ∑ i, F (Fin.snoc js i)) := by
  classical
  have hsum := (Fin.snocEquiv (fun _ : Fin (k + 1) => Fin n)).sum_comp F
  simp only [Fintype.sum_prod_type] at hsum
  change (∑ i, ∑ js, F (Fin.snoc js i)) = ∑ js, F js at hsum
  rw [Finset.sum_comm] at hsum
  unfold expectIdx
  rw [← hsum, ← Finset.mul_sum]
  have hN : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [pow_succ]
  field_simp

 theorem expectIdx_add {n a b : ℕ} (hn : 0 < n)
    (F : (Fin (a + b) → Fin n) → ℝ) :
    expectIdx n (a + b) F = expectIdx n a (fun u =>
      expectIdx n b (fun v => F (Fin.append u v))) := by
  classical
  have hsum := (Fin.appendEquiv (α := Fin n) a b).sum_comp F
  simp only [Fintype.sum_prod_type] at hsum
  change (∑ u, ∑ v, F (Fin.append u v)) = ∑ js, F js at hsum
  unfold expectIdx
  rw [← hsum, ← Finset.mul_sum, pow_add]
  have hN : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

 theorem expectIdx_const {n k : ℕ} (hn : 0 < n) (c : ℝ) :
    expectIdx n k (fun _ => c) = c := by
  classical
  have hN : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [expectIdx, hN]

 theorem expectIdx_mono {n k : ℕ}
    (F G : (Fin k → Fin n) → ℝ) (h : ∀ js, F js ≤ G js) :
    expectIdx n k F ≤ expectIdx n k G := by
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun js _ => h js) (by positivity)

 theorem expectIdx_linear {n k : ℕ} (a b : ℝ)
    (F G : (Fin k → Fin n) → ℝ) :
    expectIdx n k (fun js => a * F js + b * G js) =
      a * expectIdx n k F + b * expectIdx n k G := by
  simp only [expectIdx, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

 theorem expectIdx_mul {n k : ℕ} (a : ℝ) (F : (Fin k → Fin n) → ℝ) :
    expectIdx n k (fun js => a * F js) = a * expectIdx n k F := by
  simp only [expectIdx, ← Finset.mul_sum]
  ring

 theorem expectIdx_sum {n k : ℕ} {ι : Type*} (s : Finset ι)
    (F : ι → (Fin k → Fin n) → ℝ) :
    expectIdx n k (fun js => ∑ i ∈ s, F i js) = ∑ i ∈ s, expectIdx n k (F i) := by
  simp only [expectIdx, Finset.mul_sum]
  rw [Finset.sum_comm]

 theorem expectIdx_zero {n : ℕ} (F : (Fin 0 → Fin n) → ℝ) :
    expectIdx n 0 F = F Fin.elim0 := by
  classical
  simp [expectIdx, show (default : Fin 0 → Fin n) = Fin.elim0 from Subsingleton.elim _ _]

 theorem runFrom_snoc {p n k : ℕ} (f' : Fin n → V p → V p) (α : ℝ)
    (θ : (Fin n → V p) × V p) (js : Fin k → Fin n) (i : Fin n) :
    SAG.LargeStep.runFrom f' α θ (List.ofFn (Fin.snoc js i)) =
      SAG.LargeStep.sagStep f' α (SAG.LargeStep.runFrom f' α θ (List.ofFn js)) i := by
  rw [List.ofFn_succ']
  simp [SAG.LargeStep.runFrom, List.foldl_append]

 theorem rate_pos (n : ℕ) (hn : 0 < n) : 0 < rate n := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold rate
  have hi : 1 / (8 * (n : ℝ)) < 1 := (div_lt_one (by positivity)).2 (by linarith)
  linarith

 theorem rate_pow_lower (n : ℕ) (hn : 0 < n) : (7 / 8 : ℝ) ≤ rate n ^ n := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (n : ℝ) ≠ 0 := by positivity
  have hx : (-1 : ℝ) ≤ -(1 / (8 * (n : ℝ))) := by
    have hi : 1 / (8 * (n : ℝ)) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
    linarith
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ -(1 / (8 * (n : ℝ))) by linarith) n
  have he : 1 + (n : ℝ) * -(1 / (8 * (n : ℝ))) = (7 / 8 : ℝ) := by
    field_simp
    norm_num
  simpa only [he, rate, sub_eq_add_neg] using hb

end SAGLargeStepProof

open scoped BigOperators

namespace SAGLargeStepProof

 theorem norm_sq_smul {p : ℕ} (a : ℝ) (x : V p) :
    ‖a • x‖ ^ 2 = a ^ 2 * ‖x‖ ^ 2 := by
  simp [norm_smul, mul_pow]

 theorem quadratic_complete {p : ℕ} (a : ℝ) (ha : 0 < a) (x v : V p) :
    -a * ‖x‖ ^ 2 + inner ℝ x v ≤ ‖v‖ ^ 2 / (4 * a) := by
  have hp := sq_nonneg ‖(2 * a) • x - v‖
  rw [norm_sub_sq_real, norm_sq_smul, real_inner_smul_left] at hp
  apply (le_div_iff₀ (by positivity : 0 < 4 * a)).2
  nlinarith

 theorem sum_update_vector {p n : ℕ} (u v : Fin n → V p) (i : Fin n) :
    (∑ j, Function.update u i (v i) j) = (∑ j, u j) + v i - u i := by
  classical
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  have he := Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i) u
  rw [he]
  abel

 theorem sum_update_square {p n : ℕ} (u v : Fin n → V p) (i : Fin n) :
    (∑ j, ‖Function.update u i (v i) j‖ ^ 2) =
      (∑ j, ‖u j‖ ^ 2) + ‖v i‖ ^ 2 - ‖u i‖ ^ 2 := by
  classical
  have he : (fun j => ‖Function.update u i (v i) j‖ ^ 2) =
      Function.update (fun j => ‖u j‖ ^ 2) i (‖v i‖ ^ 2) := by
    ext j
    by_cases hj : j = i <;> simp [hj]
  rw [he, Finset.sum_update_of_mem (Finset.mem_univ i)]
  have hs := Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i)
    (fun j => ‖u j‖ ^ 2)
  rw [hs]
  ring

 theorem centered_square_sum {p n : ℕ} (u : Fin n → V p) (a : V p) :
    (∑ i, ‖u i - a‖ ^ 2) = (∑ i, ‖u i‖ ^ 2) -
      2 * inner ℝ (∑ i, u i) a + (n : ℝ) * ‖a‖ ^ 2 := by
  simp only [norm_sub_sq_real, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, sum_inner, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

 theorem centered_inner_sum {p n : ℕ} (u v : Fin n → V p) (a b : V p) :
    (∑ i, inner ℝ (u i - a) (v i - b)) = (∑ i, inner ℝ (u i) (v i)) -
      inner ℝ (∑ i, u i) b - inner ℝ a (∑ i, v i) + (n : ℝ) * inner ℝ a b := by
  simp only [inner_sub_left, inner_sub_right, Finset.sum_sub_distrib,
    sum_inner, inner_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

 theorem sum_square_ge {p n : ℕ} (hn : 0 < n) (u : Fin n → V p) :
    ‖∑ i, u i‖ ^ 2 / (n : ℝ) ≤ ∑ i, ‖u i‖ ^ 2 := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hh := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) =>
    sq_nonneg ‖u i - (1 / (n : ℝ)) • ∑ j, u j‖)
  rw [centered_square_sum, real_inner_smul_right, real_inner_self_eq_norm_sq,
    norm_sq_smul] at hh
  have he : (n : ℝ) * (1 / (n : ℝ)) ^ 2 = 1 / (n : ℝ) := by field_simp
  rw [← mul_assoc (n : ℝ) ((1 / (n : ℝ)) ^ 2) (‖∑ j, u j‖ ^ 2), he] at hh
  simp only [div_eq_mul_inv, one_mul] at hh ⊢
  nlinarith

 theorem table_moment_square {p n : ℕ} (u v : Fin n → V p) :
    (∑ i, ‖(∑ j, u j) + v i - u i‖ ^ 2) =
      ((n : ℝ) - 2) * ‖∑ j, u j‖ ^ 2 +
      2 * inner ℝ (∑ j, u j) (∑ i, v i) +
      (∑ i, ‖v i‖ ^ 2) + (∑ i, ‖u i‖ ^ 2) -
      2 * ∑ i, inner ℝ (u i) (v i) := by
  simp only [norm_sub_sq_real, norm_add_sq_real, inner_add_left,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← inner_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp_rw [real_inner_comm (v _)]
  rw [real_inner_self_eq_norm_sq]
  ring

 theorem table_moment_sum {p n : ℕ} (u v : Fin n → V p) :
    (∑ i, ((∑ j, u j) + v i - u i)) =
      ((n : ℝ) - 1) • (∑ j, u j) + ∑ i, v i := by
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, sub_smul, one_smul, Nat.cast_smul_eq_nsmul]
  abel


 theorem table_quadratic_bound {p n : ℕ} (hn : 0 < n) (μ : ℝ) (hμ : 0 < μ)
    (u v : Fin n → V p) (G e : V p) (hv : (∑ i, v i) = (n : ℝ) • G) :
    -(3 / (8 * μ * (n : ℝ)^3)) * (∑ i, ‖u i‖^2)
      - ((7 * (n : ℝ) + 1) / (16 * μ * (n : ℝ)^4)) * ‖∑ i, u i‖^2
      - (1 / (μ * (n : ℝ)^3)) * (∑ i, inner ℝ (u i) (v i))
      + (7 / (8 * (n : ℝ)^2)) * inner ℝ (∑ i, u i) e
      + (1 / (8 * μ * (n : ℝ)^3)) * inner ℝ (∑ i, u i) G
    ≤ (2 / (3 * μ * (n : ℝ)^3)) * ((∑ i, ‖v i‖^2) - (n : ℝ) * ‖G‖^2)
      + (7 * μ / (16 * ((n : ℝ) + 1))) * ‖e - (1 / ((n : ℝ) * μ)) • G‖^2 := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  let a : ℝ := 3 / (8 * μ * (n : ℝ)^3)
  let t : ℝ := -(1 / (μ * (n : ℝ)^3))
  let c : ℝ := 7 * ((n : ℝ) + 1) / (16 * μ * (n : ℝ)^4)
  let b : ℝ := 7 / (8 * (n : ℝ)^2)
  let s : V p := ∑ i, u i
  let z : V p := e - (1 / ((n : ℝ) * μ)) • G
  have ha : 0 < a := by dsimp [a]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hh (i : Fin n) := quadratic_complete a ha
    (u i - (1 / (n : ℝ)) • s) (t • (v i - G))
  simp only [real_inner_smul_right, norm_sq_smul] at hh
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hh i
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div] at hsum
  have hm := quadratic_complete c hc s (b • z)
  simp only [real_inner_smul_right, norm_sq_smul] at hm
  have hall := add_le_add hsum hm
  have he1 :
      (-a * (∑ i, ‖u i - (1 / (n : ℝ)) • s‖^2) +
        t * ∑ i, inner ℝ (u i - (1 / (n : ℝ)) • s) (v i - G)) +
        (-c * ‖s‖^2 + b * inner ℝ s z) =
      -(3 / (8 * μ * (n : ℝ)^3)) * (∑ i, ‖u i‖^2)
        - ((7 * (n : ℝ) + 1) / (16 * μ * (n : ℝ)^4)) * ‖s‖^2
        - (1 / (μ * (n : ℝ)^3)) * (∑ i, inner ℝ (u i) (v i))
        + (7 / (8 * (n : ℝ)^2)) * inner ℝ s e
        + (1 / (8 * μ * (n : ℝ)^3)) * inner ℝ s G := by
    rw [centered_square_sum, centered_inner_sum, hv]
    dsimp only [s]
    simp only [real_inner_smul_left, real_inner_smul_right, norm_sq_smul,
      real_inner_self_eq_norm_sq]
    dsimp [z, a, t, c, b]
    rw [inner_sub_right, real_inner_smul_right]
    field_simp
    ring
  have he2 : t^2 * (∑ i, ‖v i - G‖^2) / (4 * a) + b^2 * ‖z‖^2 / (4 * c) =
      (2 / (3 * μ * (n : ℝ)^3)) * ((∑ i, ‖v i‖^2) - (n : ℝ) * ‖G‖^2)
        + (7 * μ / (16 * ((n : ℝ) + 1))) * ‖z‖^2 := by
    rw [centered_square_sum, hv, real_inner_smul_left, real_inner_self_eq_norm_sq]
    dsimp [t, a, b, c]
    field_simp
    ring
  rw [he1, he2] at hall
  exact hall

end SAGLargeStepProof

open scoped BigOperators
open SAGA.Convex

namespace SAGLargeStepProof

variable {p n : ℕ} (f : Fin n → V p → ℝ) (f' : Fin n → V p → V p)
  (L μ : ℝ) (xstar : V p) (h : SAG.LargeStep.Assumptions f f' L μ xstar)
include h

 theorem centered_table_sum (y : Fin n → V p) :
    (∑ i, (y i - f' i xstar)) = ∑ i, y i := by
  rw [Finset.sum_sub_distrib, grad_sum_star_zero f f' L μ xstar h, sub_zero]

 theorem gradient_difference_sum (x : V p) :
    (∑ i, (f' i x - f' i xstar)) = (n : ℝ) • gradAvg f' x := by
  have hN : (n : ℝ) ≠ 0 := by exact_mod_cast h.n_pos.ne'
  rw [centered_table_sum f f' L μ xstar h, gradAvg, smul_smul]
  simp [hN]

 theorem lyapunov_zero_table (x : V p) :
    lyapunov f f' μ xstar (fun _ => 0, x) =
      2 * gap f xstar x + SAG.LargeStep.sigmaSq f' xstar / ((n : ℝ) * μ) := by
  have hN : (n : ℝ) ≠ 0 := by exact_mod_cast h.n_pos.ne'
  have hμ : μ ≠ 0 := h.μ_pos.ne'
  simp only [lyapunov, Finset.sum_const_zero, smul_zero, add_zero, zero_sub,
    norm_neg, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, inner_zero_left,
    sub_zero, SAG.LargeStep.sigmaSq]
  field_simp

 theorem lyapunov_dominates (hn : 8 * L / μ ≤ (n : ℝ))
    (θ : (Fin n → V p) × V p) :
    (6 / 7 : ℝ) * gap f xstar θ.2 ≤ lyapunov f f' μ xstar θ := by
  have hN : (0 : ℝ) < n := by exact_mod_cast h.n_pos
  have hμ := h.μ_pos
  have hNL : 8 * L ≤ (n : ℝ) * μ := (div_le_iff₀ hμ).1 hn
  let s : V p := ∑ i, θ.1 i
  let u : Fin n → V p := fun i => θ.1 i - f' i xstar
  let e : V p := θ.2 - xstar
  let G : V p := gradAvg f' θ.2
  let z : V p := e - (1 / ((n : ℝ) * μ)) • G
  let a : ℝ := ((n : ℝ) + 1) / (2 * (n : ℝ)^3 * μ)
  let K : ℝ := (n : ℝ) * μ / (2 * ((n : ℝ) + 1))
  have hsum : (∑ i, u i) = s := centered_table_sum f f' L μ xstar h θ.1
  have hU := sum_square_ge h.n_pos u
  rw [hsum] at hU
  have hUC := mul_le_mul_of_nonneg_left hU
    (by positivity : (0 : ℝ) ≤ 1 / ((n : ℝ)^2 * μ))
  have hsupp := avg_support f f' L μ xstar h θ.2
    (θ.2 + (stepSize n μ / (n : ℝ)) • s)
  simp only [add_sub_cancel_left, real_inner_smul_right] at hsupp
  rw [real_inner_comm s (gradAvg f' θ.2)] at hsupp
  have hlow : 2 * gap f xstar θ.2 + a * ‖s‖^2 -
      (1 / (n : ℝ)) * inner ℝ s z ≤ lyapunov f f' μ xstar θ := by
    have heq : a * ‖s‖^2 - (1 / (n : ℝ)) * inner ℝ s z =
        (1 / ((n : ℝ)^2 * μ)) * (‖s‖^2 / (n : ℝ)) +
        (((n : ℝ) - 1) / (2 * (n : ℝ)^3 * μ)) * ‖s‖^2 -
        (1 / (n : ℝ)) * inner ℝ s e +
        2 * (stepSize n μ / (n : ℝ)) * inner ℝ s G := by
      dsimp [a, z, stepSize]
      rw [inner_sub_right, real_inner_smul_right]
      field_simp
      ring
    rw [add_sub_assoc, heq]
    change _ ≤ 2 * gap f xstar (θ.2 + (stepSize n μ / (n : ℝ)) • s) +
      (1 / ((n : ℝ)^2 * μ)) * (∑ i, ‖u i‖^2) +
      (((n : ℝ) - 1) / (2 * (n : ℝ)^3 * μ)) * ‖s‖^2 -
      (1 / (n : ℝ)) * inner ℝ s e
    dsimp [gap] at hsupp ⊢
    nlinarith only [hUC, hsupp]
  have ha : 0 < a := by dsimp [a]; positivity
  have hcomp := quadratic_complete a ha s ((1 / (n : ℝ)) • z)
  rw [real_inner_smul_right, norm_sq_smul] at hcomp
  have heq : (1 / (n : ℝ))^2 * ‖z‖^2 / (4 * a) = K * ‖z‖^2 := by
    dsimp [a, K]
    field_simp
    ring
  rw [heq] at hcomp
  have hglobal : 2 * gap f xstar θ.2 - K * ‖z‖^2 ≤ lyapunov f f' μ xstar θ := by
    linarith only [hlow, hcomp]
  have hstrong := strong_inner f f' L μ xstar h θ.2
  have hH : 0 ≤ inner ℝ e G := by
    rw [real_inner_comm]
    exact (mul_nonneg hμ.le (sq_nonneg _)).trans hstrong
  have hgl := avg_lipschitz f f' L μ xstar h θ.2 xstar
  rw [grad_star_zero f f' L μ xstar h, sub_zero] at hgl
  have hgm : ‖(1 / ((n : ℝ) * μ)) • G‖ ≤ ‖e‖ / 8 := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ((n : ℝ) * μ))]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).2
    have hh := mul_le_mul_of_nonneg_right hNL (norm_nonneg e)
    have hg : 8 * ‖G‖ ≤ (n : ℝ) * μ * ‖e‖ := by nlinarith only [hgl, hh]
    have hi := mul_le_mul_of_nonneg_left hg
      (by positivity : (0 : ℝ) ≤ 1 / ((n : ℝ) * μ))
    field_simp at hi ⊢
    nlinarith only [hi]
  have hgm2 : ‖(1 / ((n : ℝ) * μ)) • G‖^2 ≤ (‖e‖ / 8)^2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hgm
  have hz : ‖z‖^2 ≤ (65 / 64 : ℝ) * ‖e‖^2 := by
    dsimp [z]
    rw [norm_sub_sq_real, real_inner_smul_right]
    have hh := mul_nonneg (by positivity : (0 : ℝ) ≤ 1 / ((n : ℝ) * μ)) hH
    nlinarith only [hgm2, hh]
  have hK : K ≤ μ / 2 := by
    dsimp [K]
    apply (div_le_iff₀ (by positivity)).2
    nlinarith only [hμ.le]
  have hmul : K * ‖z‖^2 ≤ (65 / 64 : ℝ) * gap f xstar θ.2 := by
    have h1 := mul_le_mul_of_nonneg_right hK (sq_nonneg ‖z‖)
    have h2 := mul_le_mul_of_nonneg_left hz (by positivity : (0 : ℝ) ≤ μ / 2)
    have h3 := gap_strong f f' L μ xstar h θ.2
    nlinarith only [h1, h2, h3]
  have hg0 := gap_nonneg f f' L μ xstar h θ.2
  nlinarith only [hglobal, hmul, hg0]

end SAGLargeStepProof

open scoped BigOperators
open SAGA.Convex

namespace SAGLargeStepProof

 theorem lyapunov_contract {p n : ℕ} (f : Fin n → V p → ℝ)
    (f' : Fin n → V p → V p) (L μ : ℝ) (xstar : V p)
    (h : SAG.LargeStep.Assumptions f f' L μ xstar)
    (hn : 8 * L / μ ≤ (n : ℝ)) (θ : (Fin n → V p) × V p) :
    (1 / (n : ℝ)) * ∑ i,
      lyapunov f f' μ xstar (SAG.LargeStep.sagStep f' (stepSize n μ) θ i)
      ≤ rate n * lyapunov f f' μ xstar θ := by
  classical
  have hN : (0 : ℝ) < n := by exact_mod_cast h.n_pos
  have hμ := h.μ_pos
  have hNL : 8 * L ≤ (n : ℝ) * μ := (div_le_iff₀ hμ).1 hn
  let u : Fin n → V p := fun i => θ.1 i - f' i xstar
  let v : Fin n → V p := fun i => f' i θ.2 - f' i xstar
  let s : V p := ∑ i, u i
  let G : V p := gradAvg f' θ.2
  let e : V p := θ.2 - xstar
  let H : ℝ := inner ℝ e G
  let U : ℝ := ∑ i, ‖u i‖^2
  let F : ℝ := ∑ i, ‖v i‖^2
  let S : ℝ := ‖s‖^2
  let J : ℝ := ∑ i, inner ℝ (u i) (v i)
  let c : ℝ := stepSize n μ / (n : ℝ)
  let a : ℝ := 1 / ((n : ℝ)^2 * μ)
  let b : ℝ := ((n : ℝ) - 1) / (2 * (n : ℝ)^3 * μ)
  let t : Fin n → V p := fun i => s + v i - u i
  let M : ℝ := ((n : ℝ) - 2) * S + 2 * (n : ℝ) * inner ℝ s G + F + U - 2 * J
  let R : ℝ := -(3 / (8 * μ * (n : ℝ)^3)) * U
    - ((7 * (n : ℝ) + 1) / (16 * μ * (n : ℝ)^4)) * S
    - (1 / (μ * (n : ℝ)^3)) * J + (7 / (8 * (n : ℝ)^2)) * inner ℝ s e
    + (1 / (8 * μ * (n : ℝ)^3)) * inner ℝ s G
  have hsu : s = ∑ i, θ.1 i := centered_table_sum f f' L μ xstar h θ.1
  have hsv : (∑ i, v i) = (n : ℝ) • G := gradient_difference_sum f f' L μ xstar h θ.2
  have hnew (i : Fin n) :
      (∑ j, (SAG.LargeStep.sagStep f' (stepSize n μ) θ i).1 j) = t i := by
    change (∑ j, Function.update θ.1 i (f' i θ.2) j) = t i
    rw [sum_update_vector θ.1 (fun j => f' j θ.2) i, ← hsu]
    dsimp [t, v, u]
    abel
  have htable (i : Fin n) :
      (fun j => (SAG.LargeStep.sagStep f' (stepSize n μ) θ i).1 j - f' j xstar) =
        Function.update u i (v i) := by
    ext j
    by_cases hj : j = i <;> simp [SAG.LargeStep.sagStep, u, v, hj]
  have hpoint (i : Fin n) :
      lyapunov f f' μ xstar (SAG.LargeStep.sagStep f' (stepSize n μ) θ i) =
      2 * gap f xstar θ.2 + a * (U + ‖v i‖^2 - ‖u i‖^2) + b * ‖t i‖^2 -
        (1 / (n : ℝ)) * (inner ℝ (t i) e - c * ‖t i‖^2) := by
    unfold lyapunov
    rw [hnew]
    have hx : (SAG.LargeStep.sagStep f' (stepSize n μ) θ i).2 = θ.2 - c • t i := by
      change θ.2 - c • _ = _
      rw [show (∑ j, Function.update θ.1 i (f' i θ.2) j) = t i from hnew i]
    rw [hx, sub_add_cancel]
    have hu : (∑ j, ‖(SAG.LargeStep.sagStep f' (stepSize n μ) θ i).1 j - f' j xstar‖^2) =
        U + ‖v i‖^2 - ‖u i‖^2 := by
      change (∑ j, ‖(fun k => (SAG.LargeStep.sagStep f' (stepSize n μ) θ i).1 k - f' k xstar) j‖^2) = _
      rw [htable, sum_update_square]
    rw [hu]
    have he : θ.2 - c • t i - xstar = e - c • t i := by dsimp [e]; abel
    rw [he, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hM : (∑ i, ‖t i‖^2) = M := by
    have hh := table_moment_square u v
    rw [hsv, real_inner_smul_right] at hh
    dsimp [t, M, U, F, S, J, s]
    nlinarith only [hh]
  have ht : (∑ i, t i) = ((n : ℝ) - 1) • s + (n : ℝ) • G := by
    exact (table_moment_sum u v).trans (by rw [hsv])
  have hte : (∑ i, inner ℝ (t i) e) = ((n : ℝ) - 1) * inner ℝ s e + (n : ℝ) * H := by
    rw [← sum_inner, ht, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    rw [real_inner_comm e G]
  have hQ : (1 / (n : ℝ)) * (∑ i, lyapunov f f' μ xstar
      (SAG.LargeStep.sagStep f' (stepSize n μ) θ i)) =
      2 * gap f xstar θ.2 + a * (((n : ℝ) - 1) * U + F) / (n : ℝ) +
        b * M / (n : ℝ) - (1 / (n : ℝ)^2) *
          (((n : ℝ) - 1) * inner ℝ s e + (n : ℝ) * H - c * M) := by
    simp_rw [hpoint]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hM, hte]
    field_simp
    ring
  have hbase : 2 * gap f xstar θ.2 + 2 * c * inner ℝ s G + a * U + b * S -
      (1 / (n : ℝ)) * inner ℝ s e ≤ lyapunov f f' μ xstar θ := by
    have hs := avg_support f f' L μ xstar h θ.2 (θ.2 + c • s)
    simp only [add_sub_cancel_left, real_inner_smul_right] at hs
    rw [real_inner_comm s (gradAvg f' θ.2)] at hs
    unfold lyapunov
    rw [← hsu]
    dsimp [gap, a, b, c, U, u, S, G, e] at hs ⊢
    linarith only [hs]
  have hq := mul_le_mul_of_nonneg_left hbase (rate_pos n h.n_pos).le
  have halg :
      (2 * gap f xstar θ.2 + a * (((n : ℝ) - 1) * U + F) / (n : ℝ) +
        b * M / (n : ℝ) - (1 / (n : ℝ)^2) *
          (((n : ℝ) - 1) * inner ℝ s e + (n : ℝ) * H - c * M)) -
      rate n * (2 * gap f xstar θ.2 + 2 * c * inner ℝ s G + a * U + b * S -
        (1 / (n : ℝ)) * inner ℝ s e) =
      gap f xstar θ.2 / (4 * (n : ℝ)) - H / (n : ℝ) +
        (3 / (2 * μ * (n : ℝ)^3)) * F + R := by
    dsimp [a, b, c, M, R, rate, stepSize]
    field_simp
    ring
  have hgap := gap_le_inner f f' L μ xstar h θ.2
  rw [real_inner_comm (θ.2 - xstar) (gradAvg f' θ.2)] at hgap
  have hF := table_gradient_bound f f' L μ xstar h θ.2
  rw [real_inner_comm (θ.2 - xstar) (gradAvg f' θ.2)] at hF
  have hH : 0 ≤ H := (gap_nonneg f f' L μ xstar h θ.2).trans hgap
  let C : ℝ := 3 * L / (2 * μ * (n : ℝ)^2) - 3 / (4 * (n : ℝ))
  have hraw : gap f xstar θ.2 / (4 * (n : ℝ)) - H / (n : ℝ) +
      (3 / (2 * μ * (n : ℝ)^3)) * F + R ≤ C * H + R := by
    have hg := div_le_div_of_nonneg_right hgap (by positivity : (0 : ℝ) ≤ 4 * (n : ℝ))
    have hf := mul_le_mul_of_nonneg_left hF
      (by positivity : (0 : ℝ) ≤ 3 / (2 * μ * (n : ℝ)^3))
    have he : H / (4 * (n : ℝ)) - H / (n : ℝ) +
        (3 / (2 * μ * (n : ℝ)^3)) * ((n : ℝ) * L * H) = C * H := by
      dsimp [C]
      field_simp
      ring
    nlinarith only [hg, hf, he]
  have hR := table_quadratic_bound h.n_pos μ hμ u v G e hsv
  change R ≤ _ at hR
  let K : ℝ := 7 * μ / (16 * ((n : ℝ) + 1))
  have hstrong := strong_inner f f' L μ xstar h θ.2
  rw [real_inner_comm (θ.2 - xstar) (gradAvg f' θ.2)] at hstrong
  have he : ‖e‖^2 ≤ H / μ := (le_div_iff₀ hμ).2 (by nlinarith only [hstrong])
  have hz : ‖e - (1 / ((n : ℝ) * μ)) • G‖^2 ≤
      H / μ + (1 / ((n : ℝ) * μ))^2 * ‖G‖^2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_sq_smul]
    have hh := mul_nonneg (by positivity : (0 : ℝ) ≤ 1 / ((n : ℝ) * μ)) hH
    nlinarith only [he, hh]
  have hCH : C + 2 * L / (3 * μ * (n : ℝ)^2) + 7 / (16 * ((n : ℝ) + 1)) ≤ 0 := by
    have hr : L / (μ * (n : ℝ)^2) ≤ 1 / (8 * (n : ℝ)) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith only [mul_le_mul_of_nonneg_left hNL hN.le]
    have hf : 1 / ((n : ℝ) + 1) ≤ 1 / (n : ℝ) :=
      one_div_le_one_div_of_le hN (by linarith)
    have hid : C + 2 * L / (3 * μ * (n : ℝ)^2) + 7 / (16 * ((n : ℝ) + 1)) =
        (13 / 6 : ℝ) * (L / (μ * (n : ℝ)^2)) - (3 / 4 : ℝ) * (1 / (n : ℝ)) +
        (7 / 16 : ℝ) * (1 / ((n : ℝ) + 1)) := by
      dsimp [C]
      field_simp
      ring
    rw [hid]
    have hi : 0 < 1 / (n : ℝ) := by positivity
    simp only [div_eq_mul_inv, mul_inv_rev, one_mul] at hr hf hi ⊢
    nlinarith only [hr, hf, hi]
  have hCG : (-2 / 3 + 7 / (16 * ((n : ℝ) + 1))) / (μ * (n : ℝ)^2) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    have hg : 7 / (16 * ((n : ℝ) + 1)) ≤ (7 / 16 : ℝ) :=
      (div_le_iff₀ (by positivity)).2 (by nlinarith only [hN.le])
    linarith only [hg]
  have hlast : C * H + (2 / (3 * μ * (n : ℝ)^3)) * (F - (n : ℝ) * ‖G‖^2) +
      K * ‖e - (1 / ((n : ℝ) * μ)) • G‖^2 ≤ 0 := by
    have hf := mul_le_mul_of_nonneg_left hF
      (by positivity : (0 : ℝ) ≤ 2 / (3 * μ * (n : ℝ)^3))
    have hz' := mul_le_mul_of_nonneg_left hz (by dsimp [K]; positivity : 0 ≤ K)
    have hident : C * H + (2 / (3 * μ * (n : ℝ)^3)) * ((n : ℝ) * L * H - (n : ℝ) * ‖G‖^2) +
        K * (H / μ + (1 / ((n : ℝ) * μ))^2 * ‖G‖^2) =
        (C + 2 * L / (3 * μ * (n : ℝ)^2) + 7 / (16 * ((n : ℝ) + 1))) * H +
        ((-2 / 3 + 7 / (16 * ((n : ℝ) + 1))) / (μ * (n : ℝ)^2)) * ‖G‖^2 := by
      dsimp [K]
      field_simp
      ring
    have hp := add_nonpos (mul_nonpos_of_nonpos_of_nonneg hCH hH)
      (mul_nonpos_of_nonpos_of_nonneg hCG (sq_nonneg ‖G‖))
    nlinarith only [hf, hz', hident, hp]
  rw [hQ]
  nlinarith only [hq, halg, hraw, hR, hlast]

end SAGLargeStepProof

open scoped BigOperators
open SAGA.Convex

namespace SAGLargeStepProof

 theorem potential_run_bound {p n : ℕ} (hn : 0 < n)
    (f' : Fin n → V p → V p) (α q : ℝ) (hq : 0 ≤ q)
    (Q : ((Fin n → V p) × V p) → ℝ)
    (hQ : ∀ θ, (1 / (n : ℝ)) * ∑ i, Q (SAG.LargeStep.sagStep f' α θ i) ≤ q * Q θ)
    (θ : (Fin n → V p) × V p) (k : ℕ) :
    expectIdx n k (fun js => Q (SAG.LargeStep.runFrom f' α θ (List.ofFn js))) ≤ q^k * Q θ := by
  induction k with
  | zero => simp [expectIdx_zero, SAG.LargeStep.runFrom]
  | succ k ih =>
    rw [expectIdx_snoc hn]
    simp_rw [runFrom_snoc]
    calc
      _ ≤ expectIdx n k (fun js => q * Q (SAG.LargeStep.runFrom f' α θ (List.ofFn js))) :=
        expectIdx_mono _ _ fun js => hQ _
      _ = q * expectIdx n k (fun js => Q (SAG.LargeStep.runFrom f' α θ (List.ofFn js))) :=
        expectIdx_mul q _
      _ ≤ q * (q^k * Q θ) := mul_le_mul_of_nonneg_left ih hq
      _ = q^(k + 1) * Q θ := by rw [pow_succ]; ring

 theorem sag_rate {p n : ℕ} (f : Fin n → V p → ℝ)
    (f' : Fin n → V p → V p) (L μ : ℝ) (xstar : V p)
    (h : SAG.LargeStep.Assumptions f f' L μ xstar)
    (hn : 8 * L / μ ≤ (n : ℝ)) (x0 : V p) (k : ℕ) :
    expectIdx n k (fun js =>
      gap f xstar (SAG.LargeStep.runFrom f' (stepSize n μ)
        (fun _ => 0, x0) (List.ofFn js)).2) ≤
      rate n ^ k * ((7 / 3 : ℝ) * gap f xstar x0 +
        7 * SAG.LargeStep.sigmaSq f' xstar / (6 * (n : ℝ) * μ)) := by
  have hp := potential_run_bound h.n_pos f' (stepSize n μ) (rate n) (rate_pos n h.n_pos).le
    (lyapunov f f' μ xstar) (lyapunov_contract f f' L μ xstar h hn) (fun _ => 0, x0) k
  rw [lyapunov_zero_table f f' L μ xstar h] at hp
  have hd := expectIdx_mono
    (fun js : Fin k → Fin n => (6 / 7 : ℝ) * gap f xstar
      (SAG.LargeStep.runFrom f' (stepSize n μ) (fun _ => 0, x0) (List.ofFn js)).2)
    (fun js => lyapunov f f' μ xstar
      (SAG.LargeStep.runFrom f' (stepSize n μ) (fun _ => 0, x0) (List.ofFn js)))
    (fun js => lyapunov_dominates f f' L μ xstar h hn _)
  rw [expectIdx_mul] at hd
  have he : rate n ^ k * ((7 / 3 : ℝ) * gap f xstar x0 +
      7 * SAG.LargeStep.sigmaSq f' xstar / (6 * (n : ℝ) * μ)) =
      (7 / 6 : ℝ) * (rate n ^ k *
        (2 * gap f xstar x0 + SAG.LargeStep.sigmaSq f' xstar / ((n : ℝ) * μ))) := by ring
  rw [he]
  linarith

end SAGLargeStepProof

open scoped BigOperators
open SAGA.Convex SAG.LargeStep

namespace SAGLargeStepProof

variable {p n : ℕ}

theorem sg_prefix {a b : ℕ} (f' : Fin n → V p → V p) (γ : ℕ → ℝ)
    (x0 : V p) (u : Fin a → Fin n) (v : Fin b → Fin n) (j : ℕ) (hj : j ≤ a) :
    sgIterate f' γ x0 (Fin.append u v) j = sgIterate f' γ x0 u j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hja : j < a := by omega
    have hjab : j < a+b := by omega
    simp only [sgIterate, dif_pos hja, dif_pos hjab, ih (by omega)]
    congr 2
    have he : (⟨j,hjab⟩ : Fin (a+b)) = Fin.castAdd b ⟨j,hja⟩ := rfl
    rw [he, Fin.append_left]

theorem sg_snoc {k : ℕ} (f' : Fin n → V p → V p) (γ : ℕ → ℝ)
    (x0 : V p) (js : Fin k → Fin n) (i : Fin n) :
    sgIterate f' γ x0 (Fin.snoc js i) (k+1) =
      sgIterate f' γ x0 js k-γ (k+1)•f' i (sgIterate f' γ x0 js k) := by
  have hp (j : ℕ) (hj : j ≤ k) :
      sgIterate f' γ x0 (Fin.snoc js i) j = sgIterate f' γ x0 js j := by
    induction j with
    | zero => rfl
    | succ j ih =>
      have hjk : j < k := by omega
      simp only [sgIterate, dif_pos hjk, dif_pos (show j < k+1 by omega), ih (by omega)]
      congr 2
      have he : (⟨j,by omega⟩ : Fin (k+1)) = (⟨j,hjk⟩ : Fin k).castSucc := rfl
      rw [he, Fin.snoc_castSucc]
  simp only [sgIterate, dif_pos (Nat.lt_succ_self k), hp k le_rfl]
  congr 2
  exact congrArg (fun a => f' a (sgIterate f' γ x0 js k))
    (Fin.snoc_last (n := k) (α := fun _ => Fin n) i js)

theorem hybrid_append {K : ℕ} (f' : Fin n → V p → V p)
    (L μ : ℝ) (x0 : V p) (a : Fin n → Fin n) (b : Fin K → Fin n) :
    hybrid f' L μ x0 (Fin.append a b) =
      (runFrom f' (stepSize n μ) ((fun _ => 0),warmStart f' L μ x0 a) (List.ofFn b)).2 := by
  unfold hybrid warmStart stepSize
  have hd : (List.ofFn a ++ List.ofFn b).drop n = List.ofFn b := by
    simpa only [List.length_ofFn] using (List.drop_left (l₁ := List.ofFn a) (l₂ := List.ofFn b))
  rw [List.ofFn_fin_append, hd]
  congr 3
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact sg_prefix f' _ x0 a b j (Nat.le_of_lt (Finset.mem_range.mp hj))

theorem warm_expect_add {k : ℕ} (F G : (Fin k → Fin n) → ℝ) :
    expectIdx n k (fun js => F js+G js) = expectIdx n k F+expectIdx n k G := by
  simpa using expectIdx_linear (n := n) 1 1 F G

theorem warm_expect_sub {k : ℕ} (F G : (Fin k → Fin n) → ℝ) :
    expectIdx n k (fun js => F js-G js) = expectIdx n k F-expectIdx n k G := by
  simpa [sub_eq_add_neg] using expectIdx_linear (n := n) 1 (-1) F G

theorem warm_expect_mul {k : ℕ} (c : ℝ) (F : (Fin k → Fin n) → ℝ) :
    expectIdx n k (fun js => c*F js) = c*expectIdx n k F := by
  simpa using expectIdx_linear (n := n) c 0 F (fun _ => 0)

theorem warm_expect_sum {k : ℕ} (s : Finset ℕ) (F : ℕ → (Fin k → Fin n) → ℝ) :
    expectIdx n k (fun js => ∑ j ∈ s, F j js) = ∑ j ∈ s, expectIdx n k (F j) := by
  simp only [expectIdx, Finset.mul_sum]
  rw [Finset.sum_comm]

noncomputable def warmGapSeq (f : Fin n → V p → ℝ) (f' : Fin n → V p → V p)
    (L μ : ℝ) (xstar x0 : V p) (k : ℕ) : ℝ :=
  expectIdx n k (fun js => gap f xstar (sgIterate f' (sgStepSize L μ) x0 js k))
noncomputable def warmDistSeq (f' : Fin n → V p → V p)
    (L μ : ℝ) (xstar x0 : V p) (k : ℕ) : ℝ :=
  expectIdx n k (fun js => ‖sgIterate f' (sgStepSize L μ) x0 js k-xstar‖^2)

variable (f : Fin n → V p → ℝ) (f' : Fin n → V p → V p)
  (L μ : ℝ) (xstar : V p) (h : Assumptions f f' L μ xstar)
include h

theorem gradient_second_moment (x : V p) :
    (1/(n:ℝ))*(∑ i, ‖f' i x‖^2) ≤
      2*L*inner ℝ (gradAvg f' x) (x-xstar)+2*sigmaSq f' xstar := by
  have hp (i : Fin n) : ‖f' i x‖^2 ≤ 2*‖f' i x-f' i xstar‖^2+2*‖f' i xstar‖^2 := by
    have ha := norm_add_sq_real (f' i x-f' i xstar) (f' i xstar)
    rw [sub_add_cancel] at ha
    have hb := norm_sub_sq_real (f' i x-f' i xstar) (f' i xstar)
    nlinarith [sq_nonneg ‖(f' i x-f' i xstar)-f' i xstar‖]
  have hs := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hp i)) (show 0 ≤ 1/(n:ℝ) by positivity)
  have ht := mul_le_mul_of_nonneg_left (table_gradient_bound f f' L μ xstar h x)
    (show 0 ≤ 1/(n:ℝ) by positivity)
  have hn : (n:ℝ) ≠ 0 := (Nat.cast_pos.mpr h.n_pos).ne'
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  simp [mul_assoc, mul_left_comm, hn] at ht
  dsimp [sigmaSq]
  simp only [one_div] at hs ⊢
  nlinarith

theorem sg_one_step (x : V p) (j : ℕ) :
    gap f xstar x ≤ (2*L+μ*(j:ℝ)/2)*‖x-xstar‖^2
      -(2*L+μ*((j+1:ℕ):ℝ)/2)*((1/(n:ℝ))*∑ i,
        ‖x-sgStepSize L μ (j+1)•f' i x-xstar‖^2)
      +2*sgStepSize L μ (j+1)*sigmaSq f' xstar := by
  have hL := h.L_pos
  have hμ := h.μ_pos
  let γ := sgStepSize L μ (j+1)
  let H := inner ℝ (gradAvg f' x) (x-xstar)
  let W := (1/(n:ℝ))*∑ i, ‖f' i x‖^2
  let D := (1/(n:ℝ))*∑ i, ‖x-γ•f' i x-xstar‖^2
  have hn : (n:ℝ) ≠ 0 := (Nat.cast_pos.mpr h.n_pos).ne'
  have hd : D = ‖x-xstar‖^2-2*γ*H+γ^2*W := by
    have he (i : Fin n) : x-γ•f' i x-xstar = (x-xstar)-γ•f' i x := by abel
    dsimp [D,H,W,gradAvg]
    simp_rw [he, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_smul_right, real_inner_smul_left, sum_inner]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    simp_rw [real_inner_comm (f' _ x) (x-xstar)]
    field_simp
  have hden : 0 < 2*L+μ/2*((j+1:ℕ):ℝ) := by positivity
  have hγ : 0 < γ := one_div_pos.mpr hden
  have hγL : 2*L*γ ≤ 1 := by
    dsimp [γ,sgStepSize]
    rw [mul_one_div]
    apply (div_le_one hden).mpr
    have hh : 0 ≤ μ/2*((j+1:ℕ):ℝ) := by positivity
    linarith
  have hH : 0 ≤ H := le_trans (gap_nonneg f f' L μ xstar h x) (gap_le_inner f f' L μ xstar h x)
  have hW : W ≤ 2*L*H+2*sigmaSq f' xstar := gradient_second_moment f f' L μ xstar h x
  have hW' := mul_le_mul_of_nonneg_left hW (sq_nonneg γ)
  have hsh := avg_strong_support f f' L μ xstar h x xstar
  rw [norm_sub_rev xstar x] at hsh
  have hstrong : gap f xstar x+(μ/2)*‖x-xstar‖^2 ≤ H := by
    dsimp [gap,H]
    simp only [inner_sub_right] at hsh ⊢
    linarith
  have hdrop := mul_le_mul_of_nonneg_right hγL (mul_nonneg hγ.le hH)
  have hbound : D ≤ ‖x-xstar‖^2-γ*(gap f xstar x+(μ/2)*‖x-xstar‖^2)
      +2*γ^2*sigmaSq f' xstar := by
    have hh := mul_le_mul_of_nonneg_left hstrong hγ.le
    nlinarith
  have hb := mul_le_mul_of_nonneg_left hbound hden.le
  change gap f xstar x ≤ (2*L+μ*(j:ℝ)/2)*‖x-xstar‖^2
    -(2*L+μ*((j+1:ℕ):ℝ)/2)*D+2*γ*sigmaSq f' xstar
  have hid : (2*L+μ/2*((j+1:ℕ):ℝ))*
      (‖x-xstar‖^2-γ*(gap f xstar x+(μ/2)*‖x-xstar‖^2)
        +2*γ^2*sigmaSq f' xstar) =
      (2*L+μ*(j:ℝ)/2)*‖x-xstar‖^2-gap f xstar x+2*γ*sigmaSq f' xstar := by
    dsimp [γ,sgStepSize]
    field_simp
    push_cast
    ring
  rw [hid] at hb
  nlinarith

theorem sg_expected_step (x0 : V p) (j : ℕ) :
    warmGapSeq f f' L μ xstar x0 j ≤
      (2*L+μ*(j:ℝ)/2)*warmDistSeq f' L μ xstar x0 j
      -(2*L+μ*((j+1:ℕ):ℝ)/2)*warmDistSeq f' L μ xstar x0 (j+1)
      +2*sgStepSize L μ (j+1)*sigmaSq f' xstar := by
  have hh := expectIdx_mono
    (fun js : Fin j → Fin n => gap f xstar (sgIterate f' (sgStepSize L μ) x0 js j))
    (fun js => (2*L+μ*(j:ℝ)/2)*‖sgIterate f' (sgStepSize L μ) x0 js j-xstar‖^2
      -(2*L+μ*((j+1:ℕ):ℝ)/2)*((1/(n:ℝ))*∑ i,
        ‖sgIterate f' (sgStepSize L μ) x0 js j-sgStepSize L μ (j+1)•
          f' i (sgIterate f' (sgStepSize L μ) x0 js j)-xstar‖^2)
      +2*sgStepSize L μ (j+1)*sigmaSq f' xstar)
    (fun js => sg_one_step f f' L μ xstar h _ j)
  rw [warm_expect_add, warm_expect_sub, warm_expect_mul, warm_expect_mul,
    expectIdx_const h.n_pos] at hh
  have he : warmDistSeq f' L μ xstar x0 (j+1) =
      expectIdx n j (fun js => (1/(n:ℝ))*∑ i,
        ‖sgIterate f' (sgStepSize L μ) x0 js j-sgStepSize L μ (j+1)•
          f' i (sgIterate f' (sgStepSize L μ) x0 js j)-xstar‖^2) := by
    rw [warmDistSeq, expectIdx_snoc h.n_pos]
    simp only [sg_snoc]
  rw [he]
  exact hh

omit h in
theorem sg_distance_nonneg (x0 : V p) (j : ℕ) : 0 ≤ warmDistSeq f' L μ xstar x0 j := by
  dsimp [warmDistSeq,expectIdx]
  positivity

theorem sg_prefix_expectation (x0 : V p) (K j : ℕ) (hj : j ≤ K) :
    expectIdx n K (fun js => gap f xstar (sgIterate f' (sgStepSize L μ) x0 js j)) =
      warmGapSeq f f' L μ xstar x0 j := by
  obtain ⟨b,rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [expectIdx_add h.n_pos]
  simp only [sg_prefix f' (sgStepSize L μ) x0 _ _ j le_rfl, expectIdx_const h.n_pos]
  rfl

theorem sg_telescope (x0 : V p) (K : ℕ) :
    (∑ j ∈ Finset.range K, warmGapSeq f f' L μ xstar x0 j) ≤
      2*L*‖x0-xstar‖^2-(2*L+μ*(K:ℝ)/2)*warmDistSeq f' L μ xstar x0 K
      +2*sigmaSq f' xstar*(∑ j ∈ Finset.range K, sgStepSize L μ (j+1)) := by
  induction K with
  | zero => simp [warmDistSeq,sgIterate,expectIdx]
  | succ K ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hh := sg_expected_step f f' L μ xstar h x0 K
    linarith

omit h in
theorem stepsize_log_bound (hL : 0 < L) (hμ : 0 < μ) (K : ℕ) :
    (∑ j ∈ Finset.range K, sgStepSize L μ (j+1)) ≤
      (2/μ)*Real.log (1+μ*(K:ℝ)/(4*L)) := by
  have ht (j : ℕ) : sgStepSize L μ (j+1) ≤ (2/μ)*
      (Real.log (2*L+μ*((j+1:ℕ):ℝ)/2)-Real.log (2*L+μ*(j:ℝ)/2)) := by
    have ha : 0 < 2*L+μ*(j:ℝ)/2 := by positivity
    have hb : 0 < 2*L+μ*((j+1:ℕ):ℝ)/2 := by positivity
    have hl := mul_le_mul_of_nonneg_left
      (Real.one_sub_inv_le_log_of_pos (div_pos hb ha)) (show 0 ≤ 2/μ by positivity)
    rw [Real.log_div hb.ne' ha.ne'] at hl
    have he : (2/μ)*(1-((2*L+μ*((j+1:ℕ):ℝ)/2)/(2*L+μ*(j:ℝ)/2))⁻¹) =
        sgStepSize L μ (j+1) := by
      unfold sgStepSize
      push_cast
      field_simp
      ring
    rwa [he] at hl
  have hs (k : ℕ) : (∑ j ∈ Finset.range k, sgStepSize L μ (j+1)) ≤
      (2/μ)*(Real.log (2*L+μ*(k:ℝ)/2)-Real.log (2*L)) := by
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ]; linarith [ht k]
  have ha : 0 < 2*L+μ*(K:ℝ)/2 := by positivity
  have hb : 0 < 2*L := by positivity
  have he : (2*L+μ*(K:ℝ)/2)/(2*L) = 1+μ*(K:ℝ)/(4*L) := by field_simp; ring
  simpa only [← Real.log_div ha.ne' hb.ne',he] using hs K

theorem warm_start_bound (x0 : V p) (K : ℕ) (hK : 0 < K) :
    expectIdx n K (fun js => gap f xstar (warmStart f' L μ x0 js)) ≤
      (2*L/(K:ℝ))*‖x0-xstar‖^2+(4*sigmaSq f' xstar/((K:ℝ)*μ))
        *Real.log (1+μ*(K:ℝ)/(4*L)) := by
  have hL := h.L_pos
  have hμ := h.μ_pos
  have hKr : (0:ℝ) < K := Nat.cast_pos.mpr hK
  have hj (js : Fin K → Fin n) : gap f xstar (warmStart f' L μ x0 js) ≤
      (1/(K:ℝ))*∑ j ∈ Finset.range K, gap f xstar (sgIterate f' (sgStepSize L μ) x0 js j) := by
    have hw : ∑ _j ∈ Finset.range K, (1/(K:ℝ)) = 1 := by simp; field_simp
    have hh := (avg_convex f f' L μ xstar h).map_sum_le
      (t := Finset.range K) (w := fun _ => (1/(K:ℝ)))
      (p := fun j => sgIterate f' (sgStepSize L μ) x0 js j)
      (fun _ _ => by positivity) hw (fun _ _ => Set.mem_univ _)
    simp only [← Finset.smul_sum, smul_eq_mul, ← Finset.mul_sum] at hh
    dsimp [gap,warmStart]
    have hc : (1/(K:ℝ))*(∑ _j ∈ Finset.range K, fAvg f xstar) = fAvg f xstar := by
      simp
      field_simp
    simp only [Finset.sum_sub_distrib, mul_sub]
    rw [hc]
    linarith
  have he := expectIdx_mono _ _ hj
  rw [warm_expect_mul, warm_expect_sum] at he
  have hp : (∑ j ∈ Finset.range K,
      expectIdx n K (fun js => gap f xstar (sgIterate f' (sgStepSize L μ) x0 js j))) =
      ∑ j ∈ Finset.range K, warmGapSeq f f' L μ xstar x0 j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact sg_prefix_expectation f f' L μ xstar h x0 K j (Nat.le_of_lt (Finset.mem_range.mp hj))
  rw [hp] at he
  have hs := sg_telescope f f' L μ xstar h x0 K
  have hd := mul_nonneg (show 0 ≤ 2*L+μ*(K:ℝ)/2 by positivity)
    (sg_distance_nonneg f' L μ xstar x0 K)
  have hσ : 0 ≤ sigmaSq f' xstar := by unfold sigmaSq; positivity
  have hl := mul_le_mul_of_nonneg_left (stepsize_log_bound L μ h.L_pos h.μ_pos K)
    (show 0 ≤ 2*sigmaSq f' xstar by positivity)
  have hf : (∑ j ∈ Finset.range K, warmGapSeq f f' L μ xstar x0 j) ≤
      2*L*‖x0-xstar‖^2+2*sigmaSq f' xstar*((2/μ)*Real.log (1+μ*(K:ℝ)/(4*L))) := by linarith
  have hm := mul_le_mul_of_nonneg_left hf (show 0 ≤ 1/(K:ℝ) by positivity)
  refine he.trans (hm.trans_eq ?_)
  ring

end SAGLargeStepProof

open SAGLargeStepProof

namespace SAG.LargeStep

/-- Proposition 2, p. 6: if `n ≥ 8L/μ`, the run of `hybrid` (one pass of stochastic gradient
with `γ_j = 1/(2L + μj/2)`, average of its iterates, table reset to `0`, then SAG with
`α = 1/(2nμ)`) satisfies, for `k ≥ n`, `E[g(xᵏ) − g(x*)] ≤ C (1 − 1/(8n))ᵏ` with
`C = 16L/(3n)‖x⁰ − x*‖² + 4σ²/(3nμ)(8 log(1 + μn/(4L)) + 1)`. -/
theorem proposition_2 {p n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L μ : ℝ)
    (xstar : EuclideanSpace ℝ (Fin p)) (h : Assumptions f f' L μ xstar)
    (hn : 8 * L / μ ≤ (n : ℝ)) (x0 : EuclideanSpace ℝ (Fin p)) (k : ℕ) (hk : n ≤ k) :
    SAGA.Convex.expectIdx n k (fun js =>
        SAGA.Convex.fAvg f (hybrid f' L μ x0 js) - SAGA.Convex.fAvg f xstar)
      ≤ (16 * L / (3 * (n : ℝ)) * ‖x0 - xstar‖ ^ 2
          + 4 * sigmaSq f' xstar / (3 * (n : ℝ) * μ)
            * (8 * Real.log (1 + μ * (n : ℝ) / (4 * L)) + 1))
        * (1 - 1 / (8 * (n : ℝ))) ^ k := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hk
  have hN : (0:ℝ) < n := Nat.cast_pos.mpr h.n_pos
  have hL := h.L_pos
  have hμ := h.μ_pos
  have hN1 : (1:ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_iff.mpr h.n_pos)
  have hq : 0 ≤ rate n := by
    have hh : 1/(8*(n:ℝ)) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    dsimp [rate]
    linarith
  have hσ : 0 ≤ sigmaSq f' xstar := by unfold sigmaSq; positivity
  have hlog : 0 ≤ Real.log (1+μ*(n:ℝ)/(4*L)) := by
    apply Real.log_nonneg
    have hh : 0 ≤ μ*(n:ℝ)/(4*L) := by positivity
    linarith
  let C0 := (7/3:ℝ)*((2*L/(n:ℝ))*‖x0-xstar‖^2+
      (4*sigmaSq f' xstar/((n:ℝ)*μ))*Real.log (1+μ*(n:ℝ)/(4*L)))
    +7*sigmaSq f' xstar/(6*(n:ℝ)*μ)
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  have hp : rate n^m ≤ (8/7:ℝ)*rate n^(n+m) := by
    have hh := mul_le_mul_of_nonneg_right (rate_pow_lower n h.n_pos) (pow_nonneg hq m)
    rw [pow_add]
    nlinarith
  change SAGA.Convex.expectIdx n (n+m) (fun js => gap f xstar (hybrid f' L μ x0 js)) ≤ _
  rw [expectIdx_add h.n_pos]
  simp only [hybrid_append]
  have hs := expectIdx_mono
    (fun a : Fin n → Fin n => SAGA.Convex.expectIdx n m (fun b =>
      gap f xstar (runFrom f' (stepSize n μ) ((fun _ => 0),warmStart f' L μ x0 a)
        (List.ofFn b)).2))
    (fun a => rate n^m*((7/3:ℝ)*gap f xstar (warmStart f' L μ x0 a)
      +7*sigmaSq f' xstar/(6*(n:ℝ)*μ)))
    (fun a => sag_rate f f' L μ xstar h hn (warmStart f' L μ x0 a) m)
  rw [warm_expect_mul,warm_expect_add,warm_expect_mul,expectIdx_const h.n_pos] at hs
  have hw := warm_start_bound f f' L μ xstar h x0 n h.n_pos
  have hw' := mul_le_mul_of_nonneg_left hw (show (0:ℝ) ≤ 7/3 by norm_num)
  have hc : (7/3:ℝ)*SAGA.Convex.expectIdx n n
      (fun a => gap f xstar (warmStart f' L μ x0 a))
      +7*sigmaSq f' xstar/(6*(n:ℝ)*μ) ≤ C0 := by dsimp [C0]; linarith
  calc
    _ ≤ rate n^m*((7/3:ℝ)*SAGA.Convex.expectIdx n n
        (fun a => gap f xstar (warmStart f' L μ x0 a))
        +7*sigmaSq f' xstar/(6*(n:ℝ)*μ)) := hs
    _ ≤ rate n^m*C0 := mul_le_mul_of_nonneg_left hc (pow_nonneg hq m)
    _ ≤ ((8/7:ℝ)*rate n^(n+m))*C0 := mul_le_mul_of_nonneg_right hp hC0
    _ = _ := by dsimp [C0,rate]; ring

end SAG.LargeStep

open SAG.LargeStep

theorem solution {p n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L μ : ℝ)
    (xstar : EuclideanSpace ℝ (Fin p)) (h : Assumptions f f' L μ xstar)
    (hn : 8 * L / μ ≤ (n : ℝ)) (x0 : EuclideanSpace ℝ (Fin p)) (k : ℕ) (hk : n ≤ k) :
    SAGA.Convex.expectIdx n k (fun js =>
        SAGA.Convex.fAvg f (hybrid f' L μ x0 js) - SAGA.Convex.fAvg f xstar)
      ≤ (16 * L / (3 * (n : ℝ)) * ‖x0 - xstar‖ ^ 2
          + 4 * sigmaSq f' xstar / (3 * (n : ℝ) * μ)
            * (8 * Real.log (1 + μ * (n : ℝ) / (4 * L)) + 1))
        * (1 - 1 / (8 * (n : ℝ))) ^ k := by
  exact SAG.LargeStep.proposition_2 f f' L μ xstar h hn x0 k hk
