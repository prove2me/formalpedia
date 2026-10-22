-- Prove2me | solution 1 for UnifErgHW.Diffusion.psi_properties
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T19:15:21.864725+00:00
-- url     : https://prove2.me/submissions/c79ba558-1826-4018-8c23-40fec740b040

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_ManyServerQED_Scheduling_Diffusion
import Definitions.Def_GPhNGIDiffusion_EMError_Diffusion
import Definitions.Def_GPhNGIDiffusion_EMError_Distances
import Definitions.Def_GPhNGIDiffusion_EMError_Lyapunov
import Definitions.Def_UnifErgHW_Diffusion_Lyapunov

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

end UEHpsi

open UEHpsi in
theorem solution :
    ContDiff ℝ 2 cutoff ∧ ConvexOn ℝ Set.univ cutoff ∧
      (∀ t : ℝ, t ≤ -1 → cutoff t = -1 / 2) ∧
      (∀ t : ℝ, 0 ≤ t → cutoff t = t) ∧
      (∀ t ∈ Set.Icc (-1 : ℝ) 0, cutoff t = (t + 1) ^ 3 - 1 / 2 * (t + 1) ^ 4 - 1 / 2) ∧
      (∀ ε : ℝ, 0 < ε → ∀ t : ℝ, 0 ≤ t → UnifErgHW.Diffusion.psiEps ε t = ε * t) ∧
      ∀ ε : ℝ, 0 < ε → ∀ t : ℝ,
        deriv (deriv (UnifErgHW.Diffusion.psiEps ε)) t ≤ 3 / 2 * ε ^ 2 := by
  refine ⟨contDiff_cutoff, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine convexOn_univ_of_deriv2_nonneg (fun a => (hasDerivAt_cutoff a).differentiableAt) ?_ ?_
    · rw [deriv_cutoff]; exact fun a => (hasDerivAt_dpsi a).differentiableAt
    · intro x; simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply,
        id_eq]; rw [deriv_cutoff, deriv_dpsi]; exact ddpsi_nonneg x
  · intro t ht; simp [cutoff, ht, show ¬ (0 ≤ t) by intro h; linarith]
  · intro t ht; simp [cutoff, ht]
  · intro t ⟨h1, h2⟩; rw [cutoff_eq, cl_of_mid h1 h2, max_eq_right h2]; ring
  · intro ε hε t ht; unfold UnifErgHW.Diffusion.psiEps
    simp [cutoff, mul_nonneg hε.le ht]
  · intro ε hε t
    have h1 : deriv (UnifErgHW.Diffusion.psiEps ε) = fun s => ε * dpsi (ε * s) :=
      funext fun s => (hasDerivAt_psiEps ε s).deriv
    rw [h1, (hasDerivAt_dpsiEps ε t).deriv]
    have := ddpsi_le (ε * t)
    nlinarith [sq_nonneg ε]
