-- Prove2me | solution 1 for UnifErgHW.Diffusion.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T19:25:06.792727+00:00
-- url     : https://prove2.me/submissions/5be689ca-69dd-43dc-ba87-ad6e1e1ba6eb

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
open UEHpsi UnifErgHW.Diffusion

lemma term_eq {m : ℕ} (D : ManyServerQED.Scheduling.DiffusionData m) (ϱ ε θ : ℝ) (c : EReal)
    (x : EthierKurtz.SDEState m) (u : Fin m → ℝ) (i : Fin m) :
    cf D ε θ i (x i) * driftTrunc D ϱ c (WithLp.ofLp x) u i =
      (ε * dpsi (ε * x i) - ε * θ * dpsi (-(x i))) *
        (-(ϱ / m) - x i + max (∑ j, x j) 0 * u i
          - D.theta i / D.mu i * max (∑ j, x j) 0 * u i
            * (if ((x i : ℝ) : EReal) ≤ c then 1 else 0)) := by
  have hμ := (D.mu_pos i).ne'
  simp only [cf, hs1, driftTrunc]
  field_simp
  ring

/-- per-coordinate bound on `K₀⁻` (with `s = 0`). -/
lemma coord_minus {m : ℕ} (hm : 0 < m) (ϱ ε θ : ℝ) (hϱ : 0 < ϱ) (hε : 0 < ε) (hθ : 0 < θ)
    (a : ℝ) :
    (ε * dpsi (ε * a) - ε * θ * dpsi (-a)) * (-(ϱ / m) - a) ≤
      ε * θ * ϱ / m + 1 / 2 + ε * θ / 2 - ε * min θ 1 * |a| := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨p0, p1⟩ := dpsi_mem (ε * a)
  obtain ⟨a0, a1⟩ := dpsi_mem (-a)
  have f1 := z_dpsi_ge (ε * a)
  have f2 := z_dpsi_ge (-a)
  have hρm : 0 < ϱ / m := div_pos hϱ hm'
  have hεθ : 0 < ε * θ := mul_pos hε hθ
  -- expand
  have e : (ε * dpsi (ε * a) - ε * θ * dpsi (-a)) * (-(ϱ / m) - a) =
      -(ϱ / m) * (ε * dpsi (ε * a)) + ε * θ * (ϱ / m) * dpsi (-a)
        - (ε * a) * dpsi (ε * a) - ε * θ * ((-a) * dpsi (-a)) := by ring
  rw [e]
  have t1 : -(ϱ / m) * (ε * dpsi (ε * a)) ≤ 0 := by
    have : 0 ≤ ε * dpsi (ε * a) := mul_nonneg hε.le p0
    nlinarith
  have t2 : ε * θ * (ϱ / m) * dpsi (-a) ≤ ε * θ * ϱ / m := by
    have : ε * θ * (ϱ / m) * dpsi (-a) ≤ ε * θ * (ϱ / m) * 1 :=
      mul_le_mul_of_nonneg_left a1 (by positivity)
    have h' : ε * θ * (ϱ / m) * 1 = ε * θ * ϱ / m := by ring
    linarith
  have t3 : ε * θ * (max (-a) 0 - 1 / 2) ≤ ε * θ * ((-a) * dpsi (-a)) :=
    mul_le_mul_of_nonneg_left f2 hεθ.le
  have hmax : ε * max a 0 = max (ε * a) 0 := by
    rcases le_total 0 a with h | h
    · rw [max_eq_left h, max_eq_left (mul_nonneg hε.le h)]
    · rw [max_eq_right h, max_eq_right (mul_nonpos_of_nonneg_of_nonpos hε.le h)]; ring
  have t4 : ε * min θ 1 * |a| ≤ ε * max a 0 + ε * θ * max (-a) 0 := by
    rcases le_total 0 a with h | h
    · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (by linarith)]
      have : min θ 1 * a ≤ 1 * a := mul_le_mul_of_nonneg_right (min_le_right _ _) h
      nlinarith
    · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (by linarith)]
      have : min θ 1 * (-a) ≤ θ * (-a) := mul_le_mul_of_nonneg_right (min_le_left _ _) (by linarith)
      nlinarith
  nlinarith

/-- per-coordinate bound on `K₀⁺`. -/
lemma coord_plus {m : ℕ} (D : ManyServerQED.Scheduling.DiffusionData m) (ϱ ε θ : ℝ)
    (hϱ : 0 < ϱ) (hm' : (0 : ℝ) < m) (hε : 0 < ε) (hθ : 0 < θ)
    (h215 : ∀ i, θ * max (D.theta i / D.mu i - 1) 0 ≤ 1) (c : EReal) (hc : 1 ≤ c)
    (s : ℝ) (hs : 0 ≤ s) (i : Fin m) (a ui : ℝ) (hu : 0 ≤ ui) :
    (ε * dpsi (ε * a) - ε * θ * dpsi (-a)) *
        (-(ϱ / m) - a + s * ui - D.theta i / D.mu i * s * ui
          * (if ((a : ℝ) : EReal) ≤ c then 1 else 0)) ≤
      -(ϱ / m) * (ε * dpsi (ε * a)) + ε * θ * ϱ / m + ε * θ * (1 / 2 - max (-a) 0)
        - (ε * dpsi (ε * a)) * a + ε * s * ui := by
  obtain ⟨p0, p1⟩ := dpsi_mem (ε * a)
  obtain ⟨a0, a1⟩ := dpsi_mem (-a)
  have f2 := z_dpsi_ge (-a)
  have hεθ : 0 < ε * θ := mul_pos hε hθ
  have hρm : 0 < ϱ / m := div_pos hϱ hm'
  set p := ε * dpsi (ε * a) with hp
  set q := dpsi (-a) with hq
  set β := D.theta i / D.mu i with hβ
  have hβ0 : 0 ≤ β := div_nonneg (D.theta_nonneg i) (D.mu_pos i).le
  have hp0 : 0 ≤ p := mul_nonneg hε.le p0
  have hp1 : p ≤ ε := by have := mul_le_mul_of_nonneg_left p1 hε.le; simpa [hp] using this
  -- Q ≤ ε
  have hQ : p - p * β * (if ((a : ℝ) : EReal) ≤ c then 1 else 0) - ε * θ * q
      + ε * θ * q * β * (if ((a : ℝ) : EReal) ≤ c then 1 else 0) ≤ ε := by
    split_ifs with hind
    · -- Q = (β - 1)(εθq - p)
      have hθβ := h215 i
      rcases le_total β 1 with hb | hb
      · have : (1 - β) * (p - ε * θ * q) ≤ (1 - β) * p :=
          mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
        have : (1 - β) * p ≤ p := by nlinarith
        nlinarith
      · rw [max_eq_left (by linarith)] at hθβ
        have h1 : (β - 1) * (ε * θ * q - p) ≤ (β - 1) * (ε * θ * q) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        have h2 : (β - 1) * (ε * θ * q) ≤ ε * (θ * (β - 1)) := by
          have : (β - 1) * (ε * θ * q) ≤ (β - 1) * (ε * θ * 1) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left a1 hεθ.le) (by linarith)
          nlinarith
        have h3 : ε * (θ * (β - 1)) ≤ ε * 1 := mul_le_mul_of_nonneg_left hθβ hε.le
        nlinarith
    · -- a > c ≥ 1, so q = 0
      have hac : c < ((a : ℝ) : EReal) := lt_of_not_ge hind
      have ha1 : (1 : ℝ) < a := by
        have : ((1 : ℝ) : EReal) < ((a : ℝ) : EReal) := lt_of_le_of_lt (by simpa using hc) hac
        exact_mod_cast this
      have : q = 0 := by rw [hq]; exact dpsi_of_le (by linarith)
      rw [this]; linarith
  have e : (p - ε * θ * q) *
        (-(ϱ / m) - a + s * ui - β * s * ui * (if ((a : ℝ) : EReal) ≤ c then 1 else 0)) =
      -(ϱ / m) * p + ε * θ * (ϱ / m) * q + ε * θ * ((-a) * q) * (-1) - p * a
        + s * ui * (p - p * β * (if ((a : ℝ) : EReal) ≤ c then 1 else 0) - ε * θ * q
          + ε * θ * q * β * (if ((a : ℝ) : EReal) ≤ c then 1 else 0)) := by ring
  rw [e]
  have t2 : ε * θ * (ϱ / m) * q ≤ ε * θ * ϱ / m := by
    have : ε * θ * (ϱ / m) * q ≤ ε * θ * (ϱ / m) * 1 :=
      mul_le_mul_of_nonneg_left a1 (by positivity)
    have h' : ε * θ * (ϱ / m) * 1 = ε * θ * ϱ / m := by ring
    linarith
  have t3 : ε * θ * (max (-a) 0 - 1 / 2) ≤ ε * θ * ((-a) * q) :=
    mul_le_mul_of_nonneg_left f2 hεθ.le
  have t5 : s * ui * (p - p * β * (if ((a : ℝ) : EReal) ≤ c then 1 else 0) - ε * θ * q
          + ε * θ * q * β * (if ((a : ℝ) : EReal) ≤ c then 1 else 0)) ≤ s * ui * ε :=
    mul_le_mul_of_nonneg_left hQ (mul_nonneg hs hu)
  nlinarith

end UEHlib

open UEHlib UEHpsi UnifErgHW.Diffusion in
theorem solution {m : ℕ} (hm : 0 < m) (D : ManyServerQED.Scheduling.DiffusionData m)
    (ϱ θ ε : ℝ) (hϱ : 0 < ϱ) (hθ : 0 < θ)
    (h215 : ∀ i, θ * max (D.theta i / D.mu i - 1) 0 ≤ 1) (hε : 0 < ε)
    (c : EReal) (hc : 1 ≤ c) :
    (∀ (x : EthierKurtz.SDEState m) (u : Fin m → ℝ), ∑ i, x i ≤ 0 →
      ⟪gradient (lyapV D ε θ) x, WithLp.toLp 2 (driftTrunc D ϱ c (WithLp.ofLp x) u)⟫ ≤
        ε * (θ * ϱ + m / (2 * ε) * (1 + ε * θ) - min θ 1 * l1 x) * lyapV D ε θ x) ∧
    ∀ x : EthierKurtz.SDEState m, 0 ≤ ∑ i, x i → ∀ u ∈ stdSimplex ℝ (Fin m),
      ⟪gradient (lyapV D ε θ) x, WithLp.toLp 2 (driftTrunc D ϱ c (WithLp.ofLp x) u)⟫ ≤
        -ε * (ϱ / m - θ * ϱ - θ * m / 2 + θ * negL1 x) * lyapV D ε θ x := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hV : ∀ x, 0 < lyapV D ε θ x := fun x => Real.exp_pos _
  constructor
  · intro x u hx
    rw [inner_gradient_V]
    have hs : max (∑ j, x j) 0 = 0 := max_eq_right hx
    have key : ∑ i, cf D ε θ i (x i) * (WithLp.toLp 2 (driftTrunc D ϱ c (WithLp.ofLp x) u)) i ≤
        ∑ i, (ε * θ * ϱ / m + 1 / 2 + ε * θ / 2 - ε * min θ 1 * |x i|) := by
      refine Finset.sum_le_sum fun i _ => ?_
      have := term_eq D ϱ ε θ c x u i
      simp only [PiLp.toLp_apply] at this ⊢
      rw [this, hs]
      have h2 := coord_minus hm ϱ ε θ hϱ hε hθ (x i)
      have e : (-(ϱ / m) - x i + 0 * u i - D.theta i / D.mu i * 0 * u i
          * (if ((x i : ℝ) : EReal) ≤ c then 1 else 0)) = -(ϱ / m) - x i := by ring
      rw [e]; exact h2
    have hsum : ∑ i : Fin m, (ε * θ * ϱ / m + 1 / 2 + ε * θ / 2 - ε * min θ 1 * |x i|) =
        ε * (θ * ϱ + m / (2 * ε) * (1 + ε * θ) - min θ 1 * l1 x) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, l1]
      field_simp
      ring
    rw [hsum] at key
    have := mul_le_mul_of_nonneg_left key (hV x).le
    linarith [mul_comm (lyapV D ε θ x) (ε * (θ * ϱ + m / (2 * ε) * (1 + ε * θ) - min θ 1 * l1 x))]
  · intro x hx u hu
    rw [inner_gradient_V]
    obtain ⟨hu0, hu1⟩ := hu
    set s := ∑ j, x j with hsdef
    have hs : max s 0 = s := max_eq_left hx
    have key : ∑ i, cf D ε θ i (x i) * (WithLp.toLp 2 (driftTrunc D ϱ c (WithLp.ofLp x) u)) i ≤
        ∑ i, (-(ϱ / m) * (ε * dpsi (ε * x i)) + ε * θ * ϱ / m + ε * θ * (1 / 2 - max (-(x i)) 0)
          - (ε * dpsi (ε * x i)) * x i + ε * s * u i) := by
      refine Finset.sum_le_sum fun i _ => ?_
      have := term_eq D ϱ ε θ c x u i
      simp only [PiLp.toLp_apply] at this ⊢
      rw [this, ← hsdef, hs]
      exact coord_plus D ϱ ε θ hϱ hm' hε hθ h215 c hc s hx i (x i) (u i) (hu0 i)
    -- bounds on sums
    have hP1 : ε ≤ ∑ i, ε * dpsi (ε * x i) := by
      obtain ⟨j, hj⟩ : ∃ j, 0 ≤ x j := by
        by_contra hcon
        push_neg at hcon
        have : ∑ j, x j < 0 := by
          have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm⟩, Finset.mem_univ _⟩
          calc ∑ j, x j < ∑ j : Fin m, (0 : ℝ) := Finset.sum_lt_sum_of_nonempty hne fun j _ => hcon j
            _ = 0 := by simp
        linarith
      have hj' : ε * dpsi (ε * x j) = ε := by rw [dpsi_of_nonneg (mul_nonneg hε.le hj)]; ring
      calc ε = ε * dpsi (ε * x j) := hj'.symm
        _ ≤ ∑ i, ε * dpsi (ε * x i) :=
          Finset.single_le_sum (f := fun i => ε * dpsi (ε * x i))
            (fun i _ => mul_nonneg hε.le (dpsi_mem _).1) (Finset.mem_univ j)
    have hP2 : ε * s ≤ ∑ i, (ε * dpsi (ε * x i)) * x i := by
      rw [hsdef, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have := z_dpsi_ge' (ε * x i)
      nlinarith
    have hsum : ∑ i, (-(ϱ / m) * (ε * dpsi (ε * x i)) + ε * θ * ϱ / m
          + ε * θ * (1 / 2 - max (-(x i)) 0) - (ε * dpsi (ε * x i)) * x i + ε * s * u i) =
        -(ϱ / m) * ∑ i, ε * dpsi (ε * x i) + ε * θ * ϱ + ε * θ * m / 2 - ε * θ * negL1 x
          - ∑ i, (ε * dpsi (ε * x i)) * x i + ε * s * ∑ i, u i := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, negL1]
      field_simp
      ring
    rw [hsum, hu1] at key
    have hρm : 0 < ϱ / m := div_pos hϱ hm'
    have key2 : ∑ i, cf D ε θ i (x i) * (WithLp.toLp 2 (driftTrunc D ϱ c (WithLp.ofLp x) u)) i ≤
        -ε * (ϱ / m - θ * ϱ - θ * m / 2 + θ * negL1 x) := by nlinarith
    have := mul_le_mul_of_nonneg_left key2 (hV x).le
    linarith [mul_comm (lyapV D ε θ x) (-ε * (ϱ / m - θ * ϱ - θ * m / 2 + θ * negL1 x))]
