-- Prove2me | solution 1 for UnifErgHW.Diffusion.eq_2_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T19:16:57.793518+00:00
-- url     : https://prove2.me/submissions/936ce819-152c-4490-8c86-687a4c24f551

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

end UEHpsi

open UEHpsi UnifErgHW.Diffusion in
theorem solution {m : ℕ} (D : ManyServerQED.Scheduling.DiffusionData m) (ε θ : ℝ)
    (hε : 0 < ε) (hθ : 0 < θ) (μlo μhi : ℝ) (hlo : 0 < μlo)
    (hμ : ∀ i, μlo ≤ D.mu i ∧ D.mu i ≤ μhi) (x : EthierKurtz.SDEState m) :
    ε * min 1 θ / μhi * l1 x - m * max 1 (ε * θ) / (2 * μlo) ≤ PsiStar D ε θ x ∧
      PsiStar D ε θ x ≤ ε * max 1 θ / μlo * l1 x := by
  have hP : PsiStar D ε θ x = ∑ i, (ε * θ * cutoff (-(x i)) + cutoff (ε * x i)) / D.mu i := by
    simp only [PsiStar, Psi, PsiEps, psiEps, PiLp.neg_apply, Finset.mul_sum, add_div,
      Finset.sum_add_distrib, mul_div_assoc]
  have hl1 : l1 x = ∑ i, |x i| := rfl
  rw [hP, hl1]
  set M := max 1 (ε * θ)
  have hεθ : 0 < ε * θ := mul_pos hε hθ
  constructor
  · have e1 : ε * min 1 θ / μhi * ∑ i, |x i| - m * M / (2 * μlo) =
        ∑ i, (ε * min 1 θ / μhi * |x i| - M / (2 * μlo)) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]; simp; ring
    rw [e1]
    refine Finset.sum_le_sum fun i _ => ?_
    obtain ⟨h1, h2⟩ := hμ i
    have hμi : 0 < D.mu i := lt_of_lt_of_le hlo h1
    have key : ε * min 1 θ * |x i| - M / 2 ≤ ε * θ * cutoff (-(x i)) + cutoff (ε * x i) := by
      rcases le_total 0 (x i) with ha | ha
      · rw [cutoff_of_nonneg (mul_nonneg hε.le ha), abs_of_nonneg ha]
        have := le_cutoff (-(x i)); rw [max_eq_right (by linarith)] at this
        have hm1 : min 1 θ ≤ 1 := min_le_left _ _
        have hM : ε * θ ≤ M := le_max_right _ _
        nlinarith [mul_le_mul_of_nonneg_left hm1 (mul_nonneg hε.le ha)]
      · rw [cutoff_of_nonneg (by linarith : 0 ≤ -(x i)), abs_of_nonpos ha]
        have := le_cutoff (ε * x i); rw [max_eq_right (by nlinarith)] at this
        have hm1 : min 1 θ ≤ θ := min_le_right _ _
        have hM : 1 ≤ M := le_max_left _ _
        nlinarith [mul_le_mul_of_nonneg_left hm1 (mul_nonneg hε.le (neg_nonneg.mpr ha))]
    have hμhi : 0 < μhi := lt_of_lt_of_le hμi h2
    have hmin : 0 ≤ ε * min 1 θ * |x i| :=
      mul_nonneg (mul_nonneg hε.le (le_min zero_le_one hθ.le)) (abs_nonneg _)
    have hM0 : 0 ≤ M := le_trans zero_le_one (le_max_left _ _)
    calc ε * min 1 θ / μhi * |x i| - M / (2 * μlo)
        = ε * min 1 θ * |x i| / μhi - M / 2 / μlo := by ring
      _ ≤ ε * min 1 θ * |x i| / D.mu i - M / 2 / D.mu i := by
          gcongr
      _ = (ε * min 1 θ * |x i| - M / 2) / D.mu i := by ring
      _ ≤ _ := by gcongr
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    obtain ⟨h1, h2⟩ := hμ i
    have hμi : 0 < D.mu i := lt_of_lt_of_le hlo h1
    have key : ε * θ * cutoff (-(x i)) + cutoff (ε * x i) ≤ ε * max 1 θ * |x i| := by
      have c1 := cutoff_le (-(x i)); have c2 := cutoff_le (ε * x i)
      rcases le_total 0 (x i) with ha | ha
      · rw [max_eq_right (by linarith)] at c1; rw [max_eq_left (by positivity)] at c2
        rw [abs_of_nonneg ha]
        have hm1 : 1 ≤ max 1 θ := le_max_left _ _
        nlinarith [mul_le_mul_of_nonneg_left hm1 (mul_nonneg hε.le ha)]
      · rw [max_eq_left (by linarith)] at c1; rw [max_eq_right (by nlinarith)] at c2
        rw [abs_of_nonpos ha]
        have hm1 : θ ≤ max 1 θ := le_max_right _ _
        nlinarith [mul_le_mul_of_nonneg_left hm1 (mul_nonneg hε.le (neg_nonneg.mpr ha))]
    have h0 : 0 ≤ ε * max 1 θ * |x i| :=
      mul_nonneg (mul_nonneg hε.le (le_trans zero_le_one (le_max_left _ _))) (abs_nonneg _)
    calc (ε * θ * cutoff (-(x i)) + cutoff (ε * x i)) / D.mu i
        ≤ ε * max 1 θ * |x i| / D.mu i := by gcongr
      _ ≤ ε * max 1 θ * |x i| / μlo := by gcongr
      _ = ε * max 1 θ / μlo * |x i| := by ring
