-- Prove2me | solution 1 for UnifErgHW.Diffusion.eq_2_28
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T19:39:37.188441+00:00
-- url     : https://prove2.me/submissions/5f9fd898-9f24-4826-9cfa-3715b9639bc4

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_ManyServerQED_Scheduling_Diffusion
import Definitions.Def_GPhNGIDiffusion_EMError_Diffusion
import Definitions.Def_GPhNGIDiffusion_EMError_Distances
import Definitions.Def_GPhNGIDiffusion_EMError_Lyapunov
import Definitions.Def_UnifErgHW_Diffusion_Lyapunov
import Theorems.Thm_UnifErgHW_Diffusion_lemma_2_1
import Theorems.Thm_UnifErgHW_Diffusion_eq_2_31
import Theorems.Thm_UnifErgHW_Diffusion_eq_2_10

open MeasureTheory
open scoped NNReal ENNReal RealInnerProductSpace
open GPhNGIDiffusion.EMError (SolvesAdditiveSDE IsTransitionFunction IsInvariantMeasure generator tvNormWeighted cutoff partial2)

namespace UEHpsi
open Filter Topology Set

noncomputable def cl (z : ℝ) : ℝ := max (-1) (min z 0)
noncomputable def dpsi (z : ℝ) : ℝ := -2 * cl z ^ 3 - 3 * cl z ^ 2 + 1
noncomputable def ddpsi (z : ℝ) : ℝ := -6 * cl z * (cl z + 1)

lemma cl_mem (z : ℝ) : -1 ≤ cl z ∧ cl z ≤ 0 := by
  unfold cl; constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_right _ _)

lemma cl_of_nonneg {z : ℝ} (h : 0 ≤ z) : cl z = 0 := by
  unfold cl; rw [min_eq_right h]; norm_num
lemma cl_of_le {z : ℝ} (h : z ≤ -1) : cl z = -1 := by
  unfold cl; rw [min_eq_left (by linarith)]; exact max_eq_left h
lemma cl_of_mid {z : ℝ} (h1 : -1 ≤ z) (h2 : z ≤ 0) : cl z = z := by
  unfold cl; rw [min_eq_left h2]; exact max_eq_right h1

lemma continuous_cl : Continuous cl := by unfold cl; fun_prop
lemma continuous_dpsi : Continuous dpsi := by unfold dpsi; have := continuous_cl; fun_prop
lemma continuous_ddpsi : Continuous ddpsi := by unfold ddpsi; have := continuous_cl; fun_prop

lemma cutoff_eq (z : ℝ) : cutoff z = (-(1/2) * cl z ^ 4 - cl z ^ 3 + cl z) + max z 0 := by
  unfold cutoff
  by_cases h0 : 0 ≤ z
  · rw [if_pos h0, cl_of_nonneg h0, max_eq_left h0]; ring
  · rw [if_neg h0, max_eq_right (by linarith)]
    by_cases h1 : z ≤ -1
    · rw [if_pos h1, cl_of_le h1]; norm_num
    · rw [if_neg h1, cl_of_mid (by linarith) (by linarith)]; ring

lemma continuous_cutoff : Continuous cutoff := by
  have : cutoff = fun z => (-(1/2) * cl z ^ 4 - cl z ^ 3 + cl z) + max z 0 := funext cutoff_eq
  rw [this]; have := continuous_cl; fun_prop

lemma piece {f g h : ℝ → ℝ} {a d : ℝ} (hg : HasDerivAt g d a) (hh : HasDerivAt h d a)
    (h1 : f =ᶠ[𝓝[≤] a] g) (h2 : f =ᶠ[𝓝[≥] a] h) (ha : f a = g a) (hb : f a = h a) :
    HasDerivAt f d a := by
  have A := (hg.hasDerivWithinAt (s := Iic a)).congr_of_eventuallyEq h1 ha
  have B := (hh.hasDerivWithinAt (s := Ici a)).congr_of_eventuallyEq h2 hb
  simpa using A.union B

/-- Generic: a function agreeing with `p` on `[-1,0]`, `c₁` (const) left, `q` right. -/
lemma hasDerivAt_pw {f f' : ℝ → ℝ} {L R P : ℝ → ℝ} {L' R' P' : ℝ → ℝ}
    (hL : ∀ x, HasDerivAt L (L' x) x) (hR : ∀ x, HasDerivAt R (R' x) x)
    (hP : ∀ x, HasDerivAt P (P' x) x)
    (fL : ∀ x, x ≤ -1 → f x = L x) (fR : ∀ x, 0 ≤ x → f x = R x)
    (fP : ∀ x, -1 ≤ x → x ≤ 0 → f x = P x)
    (dL : ∀ x, x ≤ -1 → f' x = L' x) (dR : ∀ x, 0 ≤ x → f' x = R' x)
    (dP : ∀ x, -1 ≤ x → x ≤ 0 → f' x = P' x) (a : ℝ) : HasDerivAt f (f' a) a := by
  rcases lt_trichotomy a (-1) with h | h | h
  · rw [dL a h.le]
    refine (hL a).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds h] with y hy using fL y (le_of_lt hy)
  · subst h
    refine piece (g := L) (h := P) ?_ ?_ ?_ ?_ (fL _ le_rfl) (fP _ le_rfl (by norm_num))
    · rw [dL _ le_rfl]; exact hL _
    · rw [dP _ le_rfl (by norm_num)]; exact hP _
    · filter_upwards [self_mem_nhdsWithin] with y hy using fL y hy
    · filter_upwards [self_mem_nhdsWithin, Iio_mem_nhds (show (-1:ℝ) < 0 by norm_num) |>
        nhdsWithin_le_nhds] with y hy hy2 using fP y hy (le_of_lt hy2)
  rcases lt_trichotomy a 0 with h' | h' | h'
  · rw [dP a h.le h'.le]
    refine (hP a).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds h h'] with y hy using fP y hy.1.le hy.2.le
  · subst h'
    refine piece (g := P) (h := R) ?_ ?_ ?_ ?_ (fP _ (by norm_num) le_rfl) (fR _ le_rfl)
    · rw [dP _ (by norm_num) le_rfl]; exact hP _
    · rw [dR _ le_rfl]; exact hR _
    · filter_upwards [self_mem_nhdsWithin, Ioi_mem_nhds (show (-1:ℝ) < 0 by norm_num) |>
        nhdsWithin_le_nhds] with y hy hy2 using fP y (le_of_lt hy2) hy
    · filter_upwards [self_mem_nhdsWithin] with y hy using fR y hy
  · rw [dR a h'.le]
    refine (hR a).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds h'] with y hy using fR y (le_of_lt hy)

lemma hasDerivAt_cutoff (a : ℝ) : HasDerivAt cutoff (dpsi a) a := by
  refine hasDerivAt_pw (L := fun _ => -1/2) (R := fun x => x)
    (P := fun x => -(1/2) * x ^ 4 - x ^ 3 + x) (L' := fun _ => 0) (R' := fun _ => 1)
    (P' := fun x => -2 * x ^ 3 - 3 * x ^ 2 + 1) (fun x => hasDerivAt_const _ _)
    (fun x => hasDerivAt_id x) ?_ ?_ ?_ ?_ ?_ ?_ ?_ a
  · intro x; have := ((hasDerivAt_pow 4 x).const_mul (-(1/2:ℝ))).sub (hasDerivAt_pow 3 x)
      |>.add (hasDerivAt_id x)
    exact this.congr_deriv (by norm_num <;> ring)
  · intro x hx; simp [cutoff, cl_of_le hx, hx, show ¬ (0 ≤ x) by intro h; linarith]
  · intro x hx; simp [cutoff, hx]
  · intro x h1 h2; rw [cutoff_eq, cl_of_mid h1 h2, max_eq_right h2]; ring
  · intro x hx; simp [dpsi, cl_of_le hx]; norm_num
  · intro x hx; simp [dpsi, cl_of_nonneg hx]
  · intro x h1 h2; simp [dpsi, cl_of_mid h1 h2]

lemma hasDerivAt_dpsi (a : ℝ) : HasDerivAt dpsi (ddpsi a) a := by
  refine hasDerivAt_pw (L := fun _ => 0) (R := fun _ => 1)
    (P := fun x => -2 * x ^ 3 - 3 * x ^ 2 + 1) (L' := fun _ => 0) (R' := fun _ => 0)
    (P' := fun x => -6 * x * (x + 1)) (fun x => hasDerivAt_const _ _)
    (fun x => hasDerivAt_const _ _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ a
  · intro x; have := (((hasDerivAt_pow 3 x).const_mul (-2:ℝ)).sub
      ((hasDerivAt_pow 2 x).const_mul (3:ℝ))).add_const (1:ℝ)
    exact this.congr_deriv (by norm_num <;> ring)
  · intro x hx; simp [dpsi, cl_of_le hx]; norm_num
  · intro x hx; simp [dpsi, cl_of_nonneg hx]
  · intro x h1 h2; simp [dpsi, cl_of_mid h1 h2]
  · intro x hx; simp [ddpsi, cl_of_le hx]
  · intro x hx; simp [ddpsi, cl_of_nonneg hx]
  · intro x h1 h2; simp [ddpsi, cl_of_mid h1 h2]

lemma deriv_cutoff : deriv cutoff = dpsi := funext fun a => (hasDerivAt_cutoff a).deriv
lemma deriv_dpsi : deriv dpsi = ddpsi := funext fun a => (hasDerivAt_dpsi a).deriv

lemma ddpsi_nonneg (z : ℝ) : 0 ≤ ddpsi z := by
  obtain ⟨h1, h2⟩ := cl_mem z; unfold ddpsi; nlinarith
lemma ddpsi_le (z : ℝ) : ddpsi z ≤ 3 / 2 := by
  unfold ddpsi; nlinarith [sq_nonneg (2 * cl z + 1)]
lemma dpsi_mem (z : ℝ) : 0 ≤ dpsi z ∧ dpsi z ≤ 1 := by
  obtain ⟨h1, h2⟩ := cl_mem z; unfold dpsi
  constructor <;> nlinarith [mul_nonneg (neg_nonneg.mpr h2) (show 0 ≤ cl z + 1 by linarith),
    mul_nonneg (mul_nonneg (neg_nonneg.mpr h2) (neg_nonneg.mpr h2)) (show 0 ≤ cl z + 1 by linarith)]

lemma contDiff_cutoff : ContDiff ℝ 2 cutoff := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun a => (hasDerivAt_cutoff a).differentiableAt, by simp, ?_⟩
  rw [deriv_cutoff, contDiff_one_iff_deriv, deriv_dpsi]
  exact ⟨fun a => (hasDerivAt_dpsi a).differentiableAt, continuous_ddpsi⟩

lemma hasDerivAt_psiEps (ε t : ℝ) :
    HasDerivAt (UnifErgHW.Diffusion.psiEps ε) (ε * dpsi (ε * t)) t := by
  have := (hasDerivAt_cutoff (ε * t)).comp t ((hasDerivAt_id t).const_mul ε)
  unfold UnifErgHW.Diffusion.psiEps
  exact this.congr_deriv (by norm_num <;> ring)

lemma hasDerivAt_dpsiEps (ε t : ℝ) :
    HasDerivAt (fun s => ε * dpsi (ε * s)) (ε ^ 2 * ddpsi (ε * t)) t := by
  have := ((hasDerivAt_dpsi (ε * t)).comp t ((hasDerivAt_id t).const_mul ε)).const_mul ε
  exact this.congr_deriv (by norm_num <;> ring)


lemma cutoff_le (z : ℝ) : cutoff z ≤ max z 0 := by
  rw [cutoff_eq]; obtain ⟨h1, h2⟩ := cl_mem z
  have : -(1/2) * cl z ^ 4 - cl z ^ 3 + cl z ≤ 0 := by
    nlinarith [mul_nonneg (neg_nonneg.mpr h2) (show 0 ≤ 1 - cl z ^ 2 - cl z ^ 3 / 2 by nlinarith [sq_nonneg (cl z), mul_nonneg (neg_nonneg.mpr h2) (sq_nonneg (cl z))])]
  linarith
lemma le_cutoff (z : ℝ) : max z 0 - 1 / 2 ≤ cutoff z := by
  rw [cutoff_eq]; obtain ⟨h1, h2⟩ := cl_mem z
  have h3 : 0 ≤ cl z + 1 := by linarith
  have : 0 ≤ (cl z + 1) ^ 3 * (1 - (cl z + 1) / 2) := mul_nonneg (pow_nonneg h3 3) (by linarith)
  nlinarith
lemma cutoff_of_nonneg {z : ℝ} (h : 0 ≤ z) : cutoff z = z := by simp [cutoff, h]


noncomputable def hs (ε θ t : ℝ) : ℝ := ε * θ * cutoff (-t) + cutoff (ε * t)
noncomputable def hs1 (ε θ t : ℝ) : ℝ := -(ε * θ * dpsi (-t)) + ε * dpsi (ε * t)
noncomputable def hs2 (ε θ t : ℝ) : ℝ := ε * θ * ddpsi (-t) + ε ^ 2 * ddpsi (ε * t)

lemma hasDerivAt_hs (ε θ t : ℝ) : HasDerivAt (hs ε θ) (hs1 ε θ t) t := by
  have h1 := ((hasDerivAt_cutoff (-t)).comp t (hasDerivAt_neg t)).const_mul (ε * θ)
  have h2 := (hasDerivAt_cutoff (ε * t)).comp t ((hasDerivAt_id t).const_mul ε)
  exact (h1.add h2).congr_deriv (by simp [hs1]; ring)

lemma hasDerivAt_hs1 (ε θ t : ℝ) : HasDerivAt (hs1 ε θ) (hs2 ε θ t) t := by
  have h1 := ((hasDerivAt_dpsi (-t)).comp t (hasDerivAt_neg t)).const_mul (ε * θ)
  have h2 := ((hasDerivAt_dpsi (ε * t)).comp t ((hasDerivAt_id t).const_mul ε)).const_mul ε
  exact (h1.neg.add h2).congr_deriv (by simp [hs2]; ring)

end UEHpsi

namespace UEHlib
open UEHpsi UnifErgHW.Diffusion

variable {m : ℕ}

lemma PsiStar_eq (D : ManyServerQED.Scheduling.DiffusionData m) (ε θ : ℝ) :
    PsiStar D ε θ = fun y => ∑ i, hs ε θ (y i) / D.mu i := by
  funext y
  simp only [PsiStar, Psi, PsiEps, psiEps, PiLp.neg_apply, Finset.mul_sum, add_div,
    Finset.sum_add_distrib, mul_div_assoc, hs]

/-- coefficient functions -/
noncomputable def cf (D : ManyServerQED.Scheduling.DiffusionData m) (ε θ : ℝ) (i : Fin m) (t : ℝ) : ℝ :=
  hs1 ε θ t / D.mu i
noncomputable def cf' (D : ManyServerQED.Scheduling.DiffusionData m) (ε θ : ℝ) (i : Fin m) (t : ℝ) : ℝ :=
  hs2 ε θ t / D.mu i

noncomputable def Lmap (D : ManyServerQED.Scheduling.DiffusionData m) (ε θ : ℝ)
    (y : EthierKurtz.SDEState m) : EthierKurtz.SDEState m →L[ℝ] ℝ :=
  ∑ i, cf D ε θ i (y i) • EuclideanSpace.proj i

lemma hasFDerivAt_PsiStar (D : ManyServerQED.Scheduling.DiffusionData m) (ε θ : ℝ)
    (x : EthierKurtz.SDEState m) : HasFDerivAt (PsiStar D ε θ) (Lmap D ε θ x) x := by
  rw [PsiStar_eq]
  unfold Lmap
  refine HasFDerivAt.fun_sum fun i _ => ?_
  have hp : HasFDerivAt (fun y : EthierKurtz.SDEState m => y i)
      (EuclideanSpace.proj i : EthierKurtz.SDEState m →L[ℝ] ℝ) x :=
    (EuclideanSpace.proj i : EthierKurtz.SDEState m →L[ℝ] ℝ).hasFDerivAt
  have := ((hasDerivAt_hs ε θ (x i)).div_const (D.mu i)).comp_hasFDerivAt x hp
  exact this

lemma hasFDerivAt_V (D : ManyServerQED.Scheduling.DiffusionData m) (ε θ : ℝ)
    (x : EthierKurtz.SDEState m) :
    HasFDerivAt (lyapV D ε θ) (lyapV D ε θ x • Lmap D ε θ x) x :=
  (hasFDerivAt_PsiStar D ε θ x).exp

lemma fderiv_V (D : ManyServerQED.Scheduling.DiffusionData m) (ε θ : ℝ) :
    fderiv ℝ (lyapV D ε θ) = fun x => lyapV D ε θ x • Lmap D ε θ x :=
  funext fun x => (hasFDerivAt_V D ε θ x).fderiv

lemma inner_gradient_V (D : ManyServerQED.Scheduling.DiffusionData m) (ε θ : ℝ)
    (x w : EthierKurtz.SDEState m) :
    ⟪gradient (lyapV D ε θ) x, w⟫ = lyapV D ε θ x * ∑ i, cf D ε θ i (x i) * w i := by
  rw [gradient, InnerProductSpace.toDual_symm_apply, fderiv_V]
  simp [Lmap]

lemma hasFDerivAt_Lmap (D : ManyServerQED.Scheduling.DiffusionData m) (ε θ : ℝ)
    (x : EthierKurtz.SDEState m) :
    HasFDerivAt (Lmap D ε θ)
      (∑ i, (cf' D ε θ i (x i) • (EuclideanSpace.proj i : EthierKurtz.SDEState m →L[ℝ] ℝ)).smulRight
        (EuclideanSpace.proj i : EthierKurtz.SDEState m →L[ℝ] ℝ)) x := by
  unfold Lmap
  refine HasFDerivAt.fun_sum fun i _ => ?_
  have hp : HasFDerivAt (fun y : EthierKurtz.SDEState m => y i)
      (EuclideanSpace.proj i : EthierKurtz.SDEState m →L[ℝ] ℝ) x :=
    (EuclideanSpace.proj i : EthierKurtz.SDEState m →L[ℝ] ℝ).hasFDerivAt
  have h0 : HasDerivAt (cf D ε θ i) (cf' D ε θ i (x i)) (x i) :=
    (hasDerivAt_hs1 ε θ (x i)).div_const (D.mu i)
  have hc : HasFDerivAt (fun y : EthierKurtz.SDEState m => cf D ε θ i (y i))
      (cf' D ε θ i (x i) • (EuclideanSpace.proj i : EthierKurtz.SDEState m →L[ℝ] ℝ)) x := by
    have := h0.comp_hasFDerivAt x hp
    exact this
  have := hc.smul_const (EuclideanSpace.proj i : EthierKurtz.SDEState m →L[ℝ] ℝ)
  exact this

lemma partial2_V (D : ManyServerQED.Scheduling.DiffusionData m) (ε θ : ℝ) (i j : Fin m)
    (x : EthierKurtz.SDEState m) :
    partial2 (lyapV D ε θ) i j x = lyapV D ε θ x *
      ((if i = j then cf' D ε θ i (x i) else 0) + cf D ε θ i (x i) * cf D ε θ j (x j)) := by
  unfold partial2
  rw [iteratedFDeriv_two_apply, fderiv_V]
  have h : HasFDerivAt (fun y => lyapV D ε θ y • Lmap D ε θ y) _ x :=
    (hasFDerivAt_V D ε θ x).smul (hasFDerivAt_Lmap D ε θ x)
  rw [h.fderiv]
  simp [Lmap]
  split_ifs <;> ring


-- facts on dpsi
lemma dpsi_of_nonneg {z : ℝ} (h : 0 ≤ z) : dpsi z = 1 := by simp [dpsi, cl_of_nonneg h]
lemma dpsi_of_le {z : ℝ} (h : z ≤ -1) : dpsi z = 0 := by simp [dpsi, cl_of_le h]; norm_num
lemma ddpsi_of_le {z : ℝ} (h : z ≤ -1) : ddpsi z = 0 := by simp [ddpsi, cl_of_le h]
lemma ddpsi_of_nonneg {z : ℝ} (h : 0 ≤ z) : ddpsi z = 0 := by simp [ddpsi, cl_of_nonneg h]

lemma z_dpsi_ge (z : ℝ) : max z 0 - 1 / 2 ≤ z * dpsi z := by
  rcases le_total 0 z with h | h
  · rw [dpsi_of_nonneg h, max_eq_left h]; linarith
  · rw [max_eq_right h]
    rcases le_total z (-1) with h1 | h1
    · rw [dpsi_of_le h1]; norm_num
    · rw [dpsi, cl_of_mid h1 h]
      nlinarith [mul_nonneg (mul_nonneg (neg_nonneg.mpr h) (show 0 ≤ z + 1 by linarith))
        (sq_nonneg (z + 1/2)), mul_nonneg (neg_nonneg.mpr h) (show 0 ≤ z + 1 by linarith),
        sq_nonneg z, sq_nonneg (z+1)]

lemma z_dpsi_ge' (z : ℝ) : z ≤ z * dpsi z := by
  rcases le_total 0 z with h | h
  · rw [dpsi_of_nonneg h]; linarith
  · have := (dpsi_mem z).2; nlinarith

end UEHlib

namespace UEHlib
open UEHpsi UnifErgHW.Diffusion Matrix

lemma trace_V {m : ℕ} (D : ManyServerQED.Scheduling.DiffusionData m) (ε θ : ℝ)
    (x : EthierKurtz.SDEState m) :
    (1 / 2) * ∑ i, ∑ j, (sigma D * (sigma D)ᵀ) i j * partial2 (lyapV D ε θ) i j x =
      lyapV D ε θ x * ∑ i, D.r i ^ 2 / 2 * (cf' D ε θ i (x i) + cf D ε θ i (x i) ^ 2) := by
  simp only [sigma, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply,
    partial2_V]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp; ring
  · intro j _ hj; simp [Ne.symm hj]
  · simp

lemma hs1_sq_le (ε θ t : ℝ) (hε : 0 < ε) (hθ : 0 < θ) (hθ1 : θ ≤ 1) : hs1 ε θ t ^ 2 ≤ ε ^ 2 := by
  obtain ⟨p0, p1⟩ := dpsi_mem (ε * t)
  obtain ⟨a0, a1⟩ := dpsi_mem (-t)
  have h1 : -ε ≤ hs1 ε θ t := by
    unfold hs1
    have : ε * θ * dpsi (-t) ≤ ε * 1 * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hθ1 hε.le) a1 a0 (by positivity)
    nlinarith [mul_nonneg hε.le p0]
  have h2 : hs1 ε θ t ≤ ε := by
    unfold hs1
    nlinarith [mul_nonneg (mul_nonneg hε.le hθ.le) a0, mul_le_mul_of_nonneg_left p1 hε.le]
  nlinarith

lemma hs2_le (ε θ t : ℝ) (hε : 0 < ε) (hθ : 0 < θ) : hs2 ε θ t ≤ 3 / 2 * (ε * θ + ε ^ 2) := by
  unfold hs2
  have h1 := ddpsi_le (-t); have h2 := ddpsi_le (ε * t)
  have : ε * θ * ddpsi (-t) ≤ ε * θ * (3 / 2) := mul_le_mul_of_nonneg_left h1 (by positivity)
  have : ε ^ 2 * ddpsi (ε * t) ≤ ε ^ 2 * (3 / 2) := mul_le_mul_of_nonneg_left h2 (by positivity)
  nlinarith


lemma trace_refined {m : ℕ} (D : ManyServerQED.Scheduling.DiffusionData m) (hσ : IsNormalized D)
    (ε θ : ℝ) (hε : 0 < ε) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (x : EthierKurtz.SDEState m)
    (hx : ∀ i, ddpsi (-(x i)) = 0) :
    (1 / 2) * ∑ i, ∑ j, (sigma D * (sigma D)ᵀ) i j * partial2 (lyapV D ε θ) i j x ≤
      ε * (3 / 2 * ε + ε * ∑ i, (D.r i ^ 2 / 2) / D.mu i ^ 2) * lyapV D ε θ x := by
  rw [trace_V]
  have hV : 0 < lyapV D ε θ x := Real.exp_pos _
  have key : ∑ i, D.r i ^ 2 / 2 * (cf' D ε θ i (x i) + cf D ε θ i (x i) ^ 2) ≤
      ∑ i, (3 / 2 * ε ^ 2 * (D.r i ^ 2 / (2 * D.mu i)) + ε ^ 2 * ((D.r i ^ 2 / 2) / D.mu i ^ 2)) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have hμ := D.mu_pos i
    have e1 : cf' D ε θ i (x i) = hs2 ε θ (x i) / D.mu i := rfl
    have e2 : cf D ε θ i (x i) ^ 2 = hs1 ε θ (x i) ^ 2 / D.mu i ^ 2 := by rw [cf, div_pow]
    rw [e1, e2]
    have b1 : hs2 ε θ (x i) ≤ 3 / 2 * ε ^ 2 := by
      unfold hs2; rw [hx i]
      have := mul_le_mul_of_nonneg_left (ddpsi_le (ε * x i)) (sq_nonneg ε)
      nlinarith
    have b2 := hs1_sq_le ε θ (x i) hε hθ hθ1
    have b1' : hs2 ε θ (x i) / D.mu i ≤ 3 / 2 * ε ^ 2 / D.mu i :=
      div_le_div_of_nonneg_right b1 hμ.le
    have b2' : hs1 ε θ (x i) ^ 2 / D.mu i ^ 2 ≤ ε ^ 2 / D.mu i ^ 2 :=
      div_le_div_of_nonneg_right b2 (by positivity)
    have hr : 0 ≤ D.r i ^ 2 / 2 := by positivity
    calc D.r i ^ 2 / 2 * (hs2 ε θ (x i) / D.mu i + hs1 ε θ (x i) ^ 2 / D.mu i ^ 2)
        ≤ D.r i ^ 2 / 2 * (3 / 2 * ε ^ 2 / D.mu i + ε ^ 2 / D.mu i ^ 2) :=
          mul_le_mul_of_nonneg_left (add_le_add b1' b2') hr
      _ = _ := by field_simp
  have hsum : ∑ i, (3 / 2 * ε ^ 2 * (D.r i ^ 2 / (2 * D.mu i)) + ε ^ 2 * ((D.r i ^ 2 / 2) / D.mu i ^ 2)) =
      ε * (3 / 2 * ε + ε * ∑ i, (D.r i ^ 2 / 2) / D.mu i ^ 2) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    unfold IsNormalized at hσ
    rw [hσ]; ring
  rw [hsum] at key
  have := mul_le_mul_of_nonneg_left key hV.le
  linarith [mul_comm (lyapV D ε θ x) (ε * (3 / 2 * ε + ε * ∑ i, (D.r i ^ 2 / 2) / D.mu i ^ 2))]

lemma ctrlDrift_eq {m : ℕ} (D : ManyServerQED.Scheduling.DiffusionData m) (ϱ : ℝ)
    (hℓ : IsCentered D ϱ) (u : Fin m → ℝ) (x : EthierKurtz.SDEState m) :
    ctrlDrift D u x = WithLp.toLp 2 (driftTrunc D ϱ ⊤ (WithLp.ofLp x) u) := by
  ext i
  simp only [ctrlDrift, driftTrunc, PiLp.toLp_apply, ManyServerQED.Scheduling.drift, hℓ i, le_top,
    if_true]
  ring

lemma negL1_le {m : ℕ} (x : EthierKurtz.SDEState m) : negL1 x ≤ l1 x :=
  Finset.sum_le_sum fun i _ => max_le (neg_le_abs _) (abs_nonneg _)
lemma negL1_nonneg {m : ℕ} (x : EthierKurtz.SDEState m) : 0 ≤ negL1 x :=
  Finset.sum_nonneg fun i _ => le_max_right _ _
lemma l1_nonneg {m : ℕ} (x : EthierKurtz.SDEState m) : 0 ≤ l1 x :=
  Finset.sum_nonneg fun i _ => abs_nonneg _


lemma num_m1 (ϱ θ ε N : ℝ) (hϱ : 0 < ϱ) (hθ' : θ * (3 * 1 * (2 * ϱ + 1)) ≤ ϱ)
    (hεN : ε * N * (12 * 1) ≤ ϱ) :
    θ * ϱ + θ * 1 / 2 - ϱ / (2 * 1) + ε * N ≤ 0 := by
  nlinarith

lemma num_m2 (ϱ θ ε N m : ℝ) (hϱ : 0 < ϱ) (hθ : 0 < θ) (hm2 : 2 ≤ m)
    (hθ' : θ * (3 * m * (2 * ϱ + m)) ≤ ϱ) (hεN : ε * N * (12 * m) ≤ ϱ) :
    θ * ϱ + θ * m / 2 - ϱ / (2 * m) + (ε * N + 3 / 2 * θ) ≤ 0 := by
  have hm' : 0 < m := by linarith
  have a1 : θ * m * 2 ≤ θ * m * (2 * ϱ + m) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have key0 : (θ * ϱ + θ * m / 2 + 3 / 2 * θ + ε * N) * (2 * m) ≤ ϱ := by nlinarith
  have : θ * ϱ + θ * m / 2 + 3 / 2 * θ + ε * N ≤ ϱ / (2 * m) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  linarith

lemma num_m2small (ϱ θ ε m : ℝ) (hε : 0 < ε) (hθ : 0 < θ) (hm' : 0 < m) :
    θ * m / 2 ≤ m / (2 * ε) * (1 + ε * θ) := by
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [mul_pos hm' hε]

end UEHlib

open Matrix
open UEHlib UEHpsi UnifErgHW.Diffusion in
theorem solution {m : ℕ} (hm : 0 < m) (D : ManyServerQED.Scheduling.DiffusionData m) (ϱ θ : ℝ)
    (hℓ : IsCentered D ϱ) (hϱ : 0 < ϱ) (hσ : IsNormalized D)
    (h215 : ∀ i, θ * max (D.theta i / D.mu i - 1) 0 ≤ 1)
    (hθ : 0 < θ) (h227 : θ ≤ ϱ / (3 * m * (2 * ϱ + m))) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ κ₀ : ℝ, 0 < κ₀ ∧
      ∀ (x : EthierKurtz.SDEState m) (u : Fin m → ℝ), u ∈ stdSimplex ℝ (Fin m) →
        generator (ctrlDrift D u) (sigma D) (lyapV D ε θ) x
          ≤ κ₀ - ε * (ϱ / (2 * m) + θ / 2 * negL1 x) * lyapV D ε θ x := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨Cb, hCb⟩ : ∃ Cb, Cb = ∑ i, (D.r i ^ 2 / 2) / D.mu i ^ 2 := ⟨_, rfl⟩
  have hCb0 : 0 ≤ Cb := by rw [hCb]; exact Finset.sum_nonneg fun i _ => by positivity
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = 3 / 2 + Cb := ⟨_, rfl⟩
  have hN0 : 0 < N := by rw [hN]; positivity
  have hθ' : θ * (3 * m * (2 * ϱ + m)) ≤ ϱ := (le_div_iff₀ (by positivity)).mp h227
  have hθ1 : θ ≤ 1 := by
    have h6 : 6 * ϱ + 3 ≤ 3 * m * (2 * ϱ + m) := by nlinarith
    have : θ * (6 * ϱ + 3) ≤ ϱ := le_trans (mul_le_mul_of_nonneg_left h6 hθ.le) hθ'
    nlinarith
  refine ⟨ϱ / (12 * m * N), by positivity, fun ε hε hε0 => ?_⟩
  have hεN : ε * N * (12 * m) ≤ ϱ := by
    have := (le_div_iff₀ (by positivity : (0:ℝ) < 12 * m * N)).mp hε0; linarith
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 3 / 2 * (ε + θ) + ε * Cb := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hK]; positivity
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = θ * ϱ + m / (2 * ε) * (1 + ε * θ) + K + ϱ / (2 * m) := ⟨_, rfl⟩
  have hA0 : 0 < A := by rw [hA]; positivity
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = max (2 * A / θ) 1 := ⟨_, rfl⟩
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  obtain ⟨μlo, hμlo⟩ : ∃ μlo, μlo = Finset.univ.inf' hne D.mu := ⟨_, rfl⟩
  obtain ⟨μhi, hμhi⟩ : ∃ μhi, μhi = Finset.univ.sup' hne D.mu := ⟨_, rfl⟩
  have hlo : 0 < μlo := by rw [hμlo]; exact (Finset.lt_inf'_iff hne).mpr fun i _ => D.mu_pos i
  have hμ : ∀ i, μlo ≤ D.mu i ∧ D.mu i ≤ μhi := fun i => by
    rw [hμlo, hμhi]
    exact ⟨Finset.inf'_le _ (Finset.mem_univ i), Finset.le_sup' _ (Finset.mem_univ i)⟩
  obtain ⟨cc, hcc⟩ : ∃ cc, cc = ε * max 1 θ / μlo := ⟨_, rfl⟩
  have hcc0 : 0 ≤ cc := by rw [hcc]; positivity
  obtain ⟨E, hE⟩ : ∃ E, E = Real.exp (cc * R) := ⟨_, rfl⟩
  have hE1 : 1 ≤ E := by rw [hE]; exact Real.one_le_exp (by rw [hR]; positivity)
  refine ⟨ε * A * E + 1, by positivity, fun x u hu => ?_⟩
  have hV : 0 < lyapV D ε θ x := Real.exp_pos _
  have hVb : l1 x ≤ R → lyapV D ε θ x ≤ E := by
    intro hl
    have := (UnifErgHW.Diffusion.eq_2_10 D ε θ hε hθ μlo μhi hlo hμ x).2
    rw [hE]; unfold lyapV
    apply Real.exp_le_exp.mpr
    calc PsiStar D ε θ x ≤ ε * max 1 θ / μlo * l1 x := this
      _ ≤ cc * R := by rw [hcc]; exact mul_le_mul_of_nonneg_left hl (by positivity)
  have hL1 : ∑ i, x i ≤ 0 →
      ⟪gradient (lyapV D ε θ) x, WithLp.toLp 2 (driftTrunc D ϱ ⊤ (WithLp.ofLp x) u)⟫ ≤
        ε * (θ * ϱ + m / (2 * ε) * (1 + ε * θ) - θ * l1 x) * lyapV D ε θ x := fun hx => by
    have := (UnifErgHW.Diffusion.lemma_2_1 hm D ϱ θ ε hϱ hθ h215 hε ⊤ le_top).1 x u hx
    rwa [min_eq_left hθ1] at this
  have hL2 : 0 ≤ ∑ i, x i →
      ⟪gradient (lyapV D ε θ) x, WithLp.toLp 2 (driftTrunc D ϱ ⊤ (WithLp.ofLp x) u)⟫ ≤
        -ε * (ϱ / m - θ * ϱ - θ * m / 2 + θ * negL1 x) * lyapV D ε θ x := fun hx =>
    (UnifErgHW.Diffusion.lemma_2_1 hm D ϱ θ ε hϱ hθ h215 hε ⊤ le_top).2 x hx u hu
  have hT : (1 / 2) * ∑ i, ∑ j, (sigma D * (sigma D)ᵀ) i j * partial2 (lyapV D ε θ) i j x ≤
      ε * K * lyapV D ε θ x := by
    rw [hK, hCb]; exact UnifErgHW.Diffusion.eq_2_31 D hσ ε θ hε hθ hθ1 x
  have hT2 : (∀ i, ddpsi (-(x i)) = 0) →
      (1 / 2) * ∑ i, ∑ j, (sigma D * (sigma D)ᵀ) i j * partial2 (lyapV D ε θ) i j x ≤
      ε * (3 / 2 * ε + ε * Cb) * lyapV D ε θ x := fun h => by
    rw [hCb]; exact trace_refined D hσ ε θ hε hθ hθ1 x h
  -- m = 1 geometric fact
  have hm1fact : (m = 1) → 0 ≤ ∑ i, x i → R < l1 x → ∀ i, ddpsi (-(x i)) = 0 := by
    intro h1m hx hl i
    have hi : ∀ j : Fin m, j = i := fun j => by
      have := j.isLt; have := i.isLt; ext; omega
    have hs : ∑ j, x j = x i := by
      rw [Finset.sum_eq_single i (fun j _ hj => absurd (hi j) hj) (by simp)]
    have hl1 : l1 x = |x i| := by
      unfold l1; rw [Finset.sum_eq_single i (fun j _ hj => absurd (hi j) hj) (by simp)]
    rw [hs] at hx
    rw [hl1, abs_of_nonneg hx] at hl
    have : 1 < x i := lt_of_le_of_lt (by rw [hR]; exact le_max_right _ _) hl
    exact ddpsi_of_le (by linarith)
  have hgen : generator (ctrlDrift D u) (sigma D) (lyapV D ε θ) x =
      ⟪gradient (lyapV D ε θ) x, WithLp.toLp 2 (driftTrunc D ϱ ⊤ (WithLp.ofLp x) u)⟫ +
        (1 / 2) * ∑ i, ∑ j, (sigma D * (sigma D)ᵀ) i j * partial2 (lyapV D ε θ) i j x := by
    rw [generator, ctrlDrift_eq D ϱ hℓ u x]
  rw [hgen]
  have hneg := negL1_le x
  have hneg0 := negL1_nonneg x
  have hl10 := l1_nonneg x
  have hRA : 2 * A / θ ≤ R := by rw [hR]; exact le_max_left _ _
  have hdich : (m = 1 → 0 ≤ ∑ i, x i → R < l1 x → ∀ i, ddpsi (-(x i)) = 0) := hm1fact
  generalize ⟪gradient (lyapV D ε θ) x, WithLp.toLp 2 (driftTrunc D ϱ ⊤ (WithLp.ofLp x) u)⟫ = G
    at hL1 hL2 ⊢
  generalize (1 / 2 : ℝ) * ∑ i : Fin m, ∑ j : Fin m,
      ((sigma D * (sigma D)ᵀ : Matrix (Fin m) (Fin m) ℝ) i j) * partial2 (lyapV D ε θ) i j x = T
    at hT hT2 ⊢
  generalize lyapV D ε θ x = V at hV hVb hL1 hL2 hT hT2 ⊢
  generalize ∑ i, x i = S at hL1 hL2 hdich
  generalize negL1 x = n at hneg hneg0 hL2 ⊢
  generalize l1 x = l at hneg hl10 hVb hL1 hdich
  have hεV : 0 < ε * V := mul_pos hε hV
  have hgoal0 : 0 < ε * A * E + 1 := by positivity
  have hεA : 0 ≤ ε * A := (mul_pos hε hA0).le
  rcases le_total S 0 with hx | hx
  · -- K₀⁻
    have h1 := hL1 hx
    have hθn : ε * V * (θ / 2 * n) ≤ ε * V * (θ / 2 * l) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hneg (by positivity)) hεV.le
    have hsum : G + T + ε * (ϱ / (2 * m) + θ / 2 * n) * V ≤ ε * V * (A - θ / 2 * l) := by
      rw [hA]; linear_combination h1 + hT + hθn
    by_cases hl : l ≤ R
    · have hv := hVb hl
      have h0 : 0 ≤ ε * V * (θ / 2 * l) := mul_nonneg hεV.le (by positivity)
      have h3 : ε * A * V ≤ ε * A * E := mul_le_mul_of_nonneg_left hv hεA
      have : ε * V * (A - θ / 2 * l) ≤ ε * A * E := by linear_combination h0 + h3
      linarith
    · push_neg at hl
      have h2A : 2 * A < θ * l := by
        have := (div_lt_iff₀ hθ).mp (lt_of_le_of_lt hRA hl); linarith
      have : ε * V * (A - θ / 2 * l) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hεV.le (by linarith)
      linarith
  · -- K₀⁺
    have h1 := hL2 hx
    have h0 : 0 ≤ ε * V * (θ / 2 * n) := mul_nonneg hεV.le (by positivity)
    have hgrad : G + ε * (ϱ / (2 * m) + θ / 2 * n) * V ≤
        ε * V * (θ * ϱ + θ * m / 2 - ϱ / (2 * m)) := by
      linear_combination h1 + h0
    by_cases hl : l ≤ R
    · have hv := hVb hl
      have hm2 := num_m2small ϱ θ ε m hε hθ hm'
      have hcoef : θ * ϱ + θ * m / 2 - ϱ / (2 * m) + K ≤ A := by
        rw [hA]; have : 0 ≤ ϱ / (2 * m) := by positivity
        linarith
      have h2 := mul_le_mul_of_nonneg_left hcoef hεV.le
      have h3 : ε * A * V ≤ ε * A * E := mul_le_mul_of_nonneg_left hv hεA
      have : G + T + ε * (ϱ / (2 * m) + θ / 2 * n) * V ≤ ε * A * E := by
        linear_combination hgrad + hT + h2 + h3
      linarith
    · push_neg at hl
      rcases eq_or_lt_of_le (show 1 ≤ m from hm) with h1m | h2m
      · have hT' := hT2 (hdich h1m.symm hx hl)
        have hm1' : (m : ℝ) = 1 := by exact_mod_cast h1m.symm
        have key : θ * ϱ + θ * m / 2 - ϱ / (2 * m) + (3 / 2 * ε + ε * Cb) ≤ 0 := by
          have : 3 / 2 * ε + ε * Cb = ε * N := by rw [hN]; ring
          rw [this, hm1']
          rw [hm1'] at hθ' hεN
          exact num_m1 ϱ θ ε N hϱ hθ' hεN
        have h4 := mul_nonpos_of_nonneg_of_nonpos hεV.le key
        have : G + T + ε * (ϱ / (2 * m) + θ / 2 * n) * V ≤ 0 := by
          linear_combination hgrad + hT' + h4
        linarith
      · have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast h2m
        have hKN : K = ε * N + 3 / 2 * θ := by rw [hK, hN]; ring
        have key : θ * ϱ + θ * m / 2 - ϱ / (2 * m) + K ≤ 0 := by
          rw [hKN]; exact num_m2 ϱ θ ε N m hϱ hθ hm2 hθ' hεN
        have h4 := mul_nonpos_of_nonneg_of_nonpos hεV.le key
        have : G + T + ε * (ϱ / (2 * m) + θ / 2 * n) * V ≤ 0 := by
          linear_combination hgrad + hT + h4
        linarith
