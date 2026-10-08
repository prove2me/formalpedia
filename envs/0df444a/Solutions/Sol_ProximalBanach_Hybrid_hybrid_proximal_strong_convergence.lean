-- Prove2me | solution 1 for ProximalBanach.Hybrid.hybrid_proximal_strong_convergence
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-06T02:24:12.098+00:00
-- url     : https://prove2.me/submissions/d1cbb113-d53e-4e3b-be1e-1b9a6adfcabd

import Mathlib
import Definitions.Def_ProximalBanach_Hybrid_Basic

set_option autoImplicit false

/- Complete checked body: AttributedBanach -/
section

section
-- Prove2me | solution 1 for ProximalBanach.Hybrid.duality_uniformContinuousOn
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T13:20:10.573996+00:00
-- url     : https://prove2.me/submissions/2e56ddc8-f7aa-4add-9c91-dd485e79495a

set_option maxHeartbeats 1000000
open Filter Topology Set
namespace ProximalBanach.Hybrid
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem support_eval_le (x u : E) (_hx : ‖x‖=1)
    (ell : StrongDual ℝ E) (hell : ‖ell‖ ≤ 1) (helx : ell x=1) (t : ℝ) :
    t * ell u ≤ ‖x+t • u‖-1 := by
  have hh := (le_abs_self (ell (x+t • u))).trans (ell.le_opNorm (x+t • u))
  have hnorm := mul_le_mul_of_nonneg_right hell (norm_nonneg (x+t • u))
  simp only [map_add,map_smul,smul_eq_mul,helx] at hh
  nlinarith

 theorem smooth_support_value (D : E → E → ℝ)
    (hD : ∀ eps:ℝ, 0 < eps → ∃ δ:ℝ, 0 < δ ∧ ∀ x u:E, ‖x‖=1 → ‖u‖=1 →
      ∀ t:ℝ, t ≠ 0 → |t| < δ → |(‖x+t • u‖-‖x‖)/t-D x u| < eps)
    (x u : E) (hx : ‖x‖=1) (hu : ‖u‖=1)
    (ell : StrongDual ℝ E) (hell : ‖ell‖ ≤ 1) (helx : ell x=1) : ell u=D x u := by
  apply eq_of_forall_dist_le
  intro eps heps
  obtain ⟨δ,hδ,hmod⟩ := hD eps heps
  have ht : 0 < δ/2 := half_pos hδ
  have hpos := hmod x u hx hu (δ/2) (ne_of_gt ht) (by rw [abs_of_pos ht]; linarith)
  have hneg := hmod x u hx hu (-δ/2) (by linarith) (by rw [abs_of_neg (by linarith : -δ/2 < 0)]; linarith)
  have hp := support_eval_le x u hx ell hell helx (δ/2)
  have hn := support_eval_le x u hx ell hell helx (-δ/2)
  have hp' : ell u ≤ (‖x+(δ/2) • u‖-1)/(δ/2) := (le_div_iff₀ ht).mpr (by nlinarith only [hp])
  have hn' : (‖x+(-δ/2) • u‖-1)/(-δ/2) ≤ ell u :=
    (div_le_iff_of_neg (by linarith : -δ/2 < 0)).mpr (by nlinarith only [hn])
  rw [hx] at hpos hneg
  rw [Real.dist_eq,abs_le]
  obtain ⟨hp0,hp1⟩ := abs_lt.mp hpos
  obtain ⟨hn0,hn1⟩ := abs_lt.mp hneg
  constructor <;> linarith

 theorem smooth_support_uniform (hUS : IsUniformlySmooth E) (eps:ℝ) (heps : 0 < eps) :
    ∃ δ > 0, ∀ x y:E, ‖x‖=1 → ‖y‖=1 → ‖x-y‖ < δ →
      ∀ ell m : StrongDual ℝ E, ‖ell‖ ≤ 1 → ell x=1 → ‖m‖ ≤ 1 → m y=1 → ‖ell-m‖ < eps := by
  obtain ⟨D,hD⟩ := hUS
  obtain ⟨r,hr,hmod⟩ := hD (eps/8) (by positivity)
  let t := r/2
  have ht : 0 < t := half_pos hr
  refine ⟨eps*t/8,by positivity,?_⟩
  intro x y hx hy hxy ell m hell helx hm hmy
  have hop : ‖ell-m‖ ≤ eps/2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro u hu
    have hpx := hmod x u hx hu t (ne_of_gt ht) (by rw [abs_of_pos ht]; dsimp [t]; linarith)
    have hpy := hmod y u hy hu t (ne_of_gt ht) (by rw [abs_of_pos ht]; dsimp [t]; linarith)
    rw [← smooth_support_value D hD x u hx hu ell hell helx,hx] at hpx
    rw [← smooth_support_value D hD y u hy hu m hm hmy,hy] at hpy
    have hnorm : |‖x+t • u‖-‖y+t • u‖| ≤ ‖x-y‖ := by
      simpa only [add_sub_add_right_eq_sub] using abs_norm_sub_norm_le (x+t • u) (y+t • u)
    have hdiv : |(‖x+t • u‖-1)/t-(‖y+t • u‖-1)/t| ≤ eps/4 := by
      rw [← sub_div,sub_sub_sub_cancel_right,abs_div,abs_of_pos ht]
      apply (div_le_iff₀ ht).mpr
      have hab := hnorm.trans_lt hxy
      nlinarith only [hab,ht,heps]
    simp only [sub_apply,Real.norm_eq_abs]
    obtain ⟨hpx0,hpx1⟩ := abs_lt.mp hpx
    obtain ⟨hpy0,hpy1⟩ := abs_lt.mp hpy
    obtain ⟨hd0,hd1⟩ := abs_le.mp hdiv
    rw [abs_le]
    constructor <;> linarith
  linarith

private theorem normalized_support (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x)
    (x:E) (hx : 0 < ‖x‖) :
    ‖‖x‖⁻¹ • x‖=1 ∧ ‖‖x‖⁻¹ • J x‖=1 ∧ (‖x‖⁻¹ • J x) (‖x‖⁻¹ • x)=1 := by
  have hn : ‖J x‖=‖x‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hJ x).2
  refine ⟨?_,?_,?_⟩
  · simp [norm_smul,inv_mul_cancel₀ (ne_of_gt hx)]
  · simp [norm_smul,hn,inv_mul_cancel₀ (ne_of_gt hx)]
  · simp only [smul_apply,map_smul,smul_eq_mul,(hJ x).1]
    field_simp

 theorem duality_uniform_on_bounded (hUS : IsUniformlySmooth E) (J:E → StrongDual ℝ E)
    (hJ : ∀ x, J x ∈ dualityMap x) (B:Set E) (hB:Bornology.IsBounded B) :
    UniformContinuousOn J B := by
  obtain ⟨M0,hM0⟩ := hB.exists_norm_le
  let M := max M0 0
  have hM : 0 ≤ M := le_max_right _ _
  have hbound : ∀ x∈B, ‖x‖ ≤ M := fun x hx => (hM0 x hx).trans (le_max_left _ _)
  have hnorm : ∀ x:E, ‖J x‖=‖x‖ := fun x =>
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hJ x).2
  apply Metric.uniformContinuousOn_iff.mpr
  intro eps heps
  obtain ⟨eta,heta,hunit⟩ := smooth_support_uniform hUS (eps/(4*(M+1))) (by positivity)
  refine ⟨min (eps/8) (eta*eps/64),by positivity,?_⟩
  intro x hx y hy hxy
  rw [dist_eq_norm] at hxy ⊢
  have hxy1 : ‖x-y‖ < eps/8 := hxy.trans_le (min_le_left _ _)
  have hxy2 : ‖x-y‖ < eta*eps/64 := hxy.trans_le (min_le_right _ _)
  have habs : |‖x‖-‖y‖| ≤ ‖x-y‖ := abs_norm_sub_norm_le x y
  have hab := abs_le.mp habs
  by_cases hxsmall : ‖x‖ < eps/4
  · have hJb := norm_sub_le (J x) (J y)
    rw [hnorm x,hnorm y] at hJb
    linarith
  have hxlow : eps/4 ≤ ‖x‖ := le_of_not_gt hxsmall
  have hxpos : 0 < ‖x‖ := by linarith
  have hypos : 0 < ‖y‖ := by linarith
  let a := ‖x‖
  let b := ‖y‖
  let u := a⁻¹ • x
  let v := b⁻¹ • y
  let ell := a⁻¹ • J x
  let m := b⁻¹ • J y
  obtain ⟨hu,hell,helx⟩ := normalized_support J hJ x hxpos
  obtain ⟨hv,hm,hmy⟩ := normalized_support J hJ y hypos
  change ‖u‖=1 at hu
  change ‖v‖=1 at hv
  change ‖ell‖=1 at hell
  change ‖m‖=1 at hm
  change ell u=1 at helx
  change m v=1 at hmy
  have hau : a • u=x := by dsimp [u]; rw [smul_smul,mul_inv_cancel₀ (ne_of_gt hxpos),one_smul]
  have hbv : b • v=y := by dsimp [v]; rw [smul_smul,mul_inv_cancel₀ (ne_of_gt hypos),one_smul]
  have hal : a • ell=J x := by dsimp [ell]; rw [smul_smul,mul_inv_cancel₀ (ne_of_gt hxpos),one_smul]
  have hbm : b • m=J y := by dsimp [m]; rw [smul_smul,mul_inv_cancel₀ (ne_of_gt hypos),one_smul]
  have hsplit : a • (u-v)=(x-y)+(b-a) • v := by
    rw [smul_sub,sub_smul,← hau,← hbv]
    abel
  have huv : a*‖u-v‖ ≤ 2*‖x-y‖ := by
    have hh := norm_add_le (x-y) ((b-a) • v)
    rw [← hsplit,norm_smul,Real.norm_eq_abs,abs_of_pos hxpos] at hh
    rw [norm_smul,Real.norm_eq_abs,hv,mul_one,abs_sub_comm] at hh
    dsimp [a,b] at hh ⊢
    linarith
  have huvlt : ‖u-v‖ < eta := by
    have hnonneg := norm_nonneg (u-v)
    dsimp [a] at huv
    nlinarith only [huv,hxlow,hxy2,hnonneg,heta,heps]
  have hdual := hunit u v hu hv huvlt ell m hell.le helx hm.le hmy
  have hj : J x-J y=a • (ell-m)+(a-b) • m := by
    rw [← hal,← hbm]
    module
  have hestimate := norm_add_le (a • (ell-m)) ((a-b) • m)
  rw [← hj,norm_smul,Real.norm_eq_abs,abs_of_pos hxpos,norm_smul,Real.norm_eq_abs,hm,mul_one] at hestimate
  have hscaled : a*‖ell-m‖ < eps/4 := by
    have hh := mul_lt_mul_of_pos_left hdual hxpos
    have haM : a ≤ M := hbound x hx
    have hfrac : a*(eps/(4*(M+1))) ≤ eps/4 := by
      have hdiv : eps/(4*(M+1)) > 0 := by positivity
      have hm1 : a ≤ M+1 := by linarith
      calc
        _ ≤ (M+1)*(eps/(4*(M+1))) := mul_le_mul_of_nonneg_right hm1 hdiv.le
        _ = eps/4 := by field_simp
    exact hh.trans_le hfrac
  dsimp [a,b] at hestimate
  linarith
end ProximalBanach.Hybrid

namespace ProximalBanach.Hybrid

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- §2, p. 939, property 4 of the duality mapping: if `E` is uniformly smooth, then `J` is
uniformly norm-to-norm continuous on each bounded subset of `E`. -/
theorem _root_.checked_duality_uniformContinuousOn [CompleteSpace E] (hUS : IsUniformlySmooth E) (J : E → StrongDual ℝ E)
    (hJ : ∀ x, J x ∈ dualityMap x) (B : Set E) (hB : Bornology.IsBounded B) :
    UniformContinuousOn J B := by
  exact duality_uniform_on_bounded hUS J hJ B hB

end ProximalBanach.Hybrid
end

section
-- Prove2me | solution 1 for ProximalBanach.Hybrid.remark1_zeros_subset
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:15:25.176985+00:00
-- url     : https://prove2.me/submissions/bd2b9409-984a-4492-8876-a2e34dfd2b84


namespace ProximalBanach.Hybrid

open Filter Topology

theorem aux_rz_subgrad {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : StrongDual ℝ E) (p z : E) (hf : f ∈ dualityMap p) :
    2 * f (z - p) ≤ ‖z‖ ^ 2 - ‖p‖ ^ 2 := by
  obtain ⟨h1, h2⟩ := hf
  have h3 : f z ≤ ‖f‖ * ‖z‖ := by
    have := f.le_opNorm z
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  rw [map_sub, h1]
  nlinarith [sq_nonneg (‖f‖ - ‖z‖)]

theorem aux_rz_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hS : IsSmooth E) (p d : E) :
    ∃ D : ℝ, Tendsto (fun t : ℝ => (‖p + t • d‖ ^ 2 - ‖p‖ ^ 2) / t) (𝓝[≠] (0 : ℝ)) (𝓝 D) := by
  by_cases hp : p = 0
  · subst hp
    refine ⟨0, ?_⟩
    have hc : Tendsto (fun t : ℝ => t * ‖d‖ ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      have : Tendsto (fun t : ℝ => t * ‖d‖ ^ 2) (𝓝 (0 : ℝ)) (𝓝 (0 * ‖d‖ ^ 2)) :=
        (continuous_id.mul continuous_const).tendsto 0
      rw [zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine hc.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t ≠ 0 := ht
    simp only [zero_add, norm_zero, norm_smul, Real.norm_eq_abs]
    rw [mul_pow, sq_abs]
    field_simp
    ring
  by_cases hd : d = 0
  · subst hd
    refine ⟨0, ?_⟩
    simp only [smul_zero, add_zero, sub_self, zero_div]
    exact tendsto_const_nhds
  have ha : 0 < ‖p‖ := norm_pos_iff.2 hp
  have hb : 0 < ‖d‖ := norm_pos_iff.2 hd
  have hx : ‖‖p‖⁻¹ • p‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm]; exact inv_mul_cancel₀ ha.ne'
  have hy : ‖‖d‖⁻¹ • d‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm]; exact inv_mul_cancel₀ hb.ne'
  obtain ⟨L, hL⟩ := hS (‖p‖⁻¹ • p) (‖d‖⁻¹ • d) hx hy
  have hφ : Tendsto (fun t : ℝ => t * ‖d‖ / ‖p‖) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun t : ℝ => t * ‖d‖ / ‖p‖) (𝓝 (0 : ℝ)) (𝓝 (0 * ‖d‖ / ‖p‖)) :=
        ((continuous_id.mul continuous_const).div_const _).tendsto 0
      rw [zero_mul, zero_div] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact div_ne_zero (mul_ne_zero ht hb.ne') ha.ne'
  have h1 := hL.comp hφ
  have h2 : Tendsto (fun t : ℝ => ‖p + t • d‖ + ‖p‖) (𝓝[≠] (0 : ℝ)) (𝓝 (‖p‖ + ‖p‖)) := by
    have : Tendsto (fun t : ℝ => ‖p + t • d‖ + ‖p‖) (𝓝 (0 : ℝ))
        (𝓝 (‖p + (0 : ℝ) • d‖ + ‖p‖)) :=
      (((continuous_const.add (continuous_id.smul continuous_const)).norm).add
        continuous_const).tendsto 0
    rw [zero_smul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine ⟨‖d‖ * L * (‖p‖ + ‖p‖), ?_⟩
  have h3 := (h1.const_mul ‖d‖).mul h2
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : t ≠ 0 := ht
  have key : ‖p‖⁻¹ • p + (t * ‖d‖ / ‖p‖) • ‖d‖⁻¹ • d = ‖p‖⁻¹ • (p + t • d) := by
    rw [smul_add, smul_smul, smul_smul]
    congr 2
    field_simp
  have hn : ‖‖p‖⁻¹ • p + (t * ‖d‖ / ‖p‖) • ‖d‖⁻¹ • d‖ = ‖p‖⁻¹ * ‖p + t • d‖ := by
    rw [key, norm_smul, norm_inv, norm_norm]
  simp only [Function.comp_apply, hn, hx]
  field_simp
  ring

theorem aux_rz_proj {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hS : IsSmooth E) (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x) (x0 p d : E)
    (hmin : ∀ t : ℝ, 0 < t → t ≤ 1 →
      ‖p‖ ^ 2 - 2 * J x0 p ≤ ‖p + t • d‖ ^ 2 - 2 * J x0 (p + t • d)) :
    (J x0 - J p) d ≤ 0 := by
  obtain ⟨D, hD⟩ := aux_rz_deriv hS p d
  have hA : 2 * J x0 d ≤ D := by
    have hD' : Tendsto (fun t : ℝ => (‖p + t • d‖ ^ 2 - ‖p‖ ^ 2) / t) (𝓝[>] (0 : ℝ)) (𝓝 D) :=
      hD.mono_left (nhdsWithin_mono _ (fun t (ht : 0 < t) => ht.ne'))
    refine ge_of_tendsto hD' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    have h := hmin t ht.1 ht.2.le
    rw [map_add, map_smul, smul_eq_mul] at h
    rw [le_div_iff₀ ht.1]
    nlinarith
  have hB : D ≤ 2 * J p d := by
    have hD' : Tendsto (fun t : ℝ => (‖p + t • d‖ ^ 2 - ‖p‖ ^ 2) / t) (𝓝[<] (0 : ℝ)) (𝓝 D) :=
      hD.mono_left (nhdsWithin_mono _ (fun t (ht : t < 0) => ht.ne))
    refine le_of_tendsto hD' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : t < 0)
    have h := aux_rz_subgrad (J p) p (p + t • d) (hJ p)
    rw [add_sub_cancel_left, map_smul, smul_eq_mul] at h
    rw [div_le_iff_of_neg ht]
    nlinarith
  rw [sub_apply]
  linarith

theorem aux_rz_H {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E → Set (StrongDual ℝ E)) (hT : IsMonotoneOp T) (J : E → StrongDual ℝ E) (r : ℕ → ℝ)
    (x y : ℕ → E) (v : ℕ → StrongDual ℝ E) (hrun : IsHybridRun T J r x y v) (n : ℕ) :
    zeros T ⊆ halfH v y n := by
  intro w hw
  have h := hT (y n) w (v n) (hrun n).1 0 hw
  show v n (w - y n) ≤ 0
  rw [sub_zero] at h
  have : v n (w - y n) = - v n (y n - w) := by rw [← map_neg, neg_sub]
  linarith

theorem aux_rz_half {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : StrongDual ℝ E) (c p w : E) (hp : f (p - c) ≤ 0) (hw : f (w - c) ≤ 0) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    f (p + t • (w - p) - c) ≤ 0 := by
  have : p + t • (w - p) - c = (1 - t) • (p - c) + t • (w - c) := by
    simp only [sub_smul, one_smul, smul_sub]; abel
  rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  nlinarith [mul_nonneg ht0 (neg_nonneg.2 hw), mul_nonneg (sub_nonneg.2 ht1) (neg_nonneg.2 hp)]

end ProximalBanach.Hybrid

open ProximalBanach.Hybrid
open Filter Topology

theorem _root_.checked_remark1_zeros_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [StrictConvexSpace ℝ E] (_hR : IsReflexive E) (hS : IsSmooth E)
    (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x)
    (T : E → Set (StrongDual ℝ E)) (hT : IsMaximalMonotone T) (_hZ : (zeros T).Nonempty)
    (r : ℕ → ℝ) (_hr : ∀ n, 0 < r n) (x y : ℕ → E) (v : ℕ → StrongDual ℝ E)
    (hrun : IsHybridRun T J r x y v) :
    ∀ n : ℕ, zeros T ⊆ halfH v y n ∩ halfW J x n := by
  have hH := aux_rz_H T hT.1 J r x y v hrun
  intro n
  induction n with
  | zero =>
    intro w hw
    refine ⟨hH 0 hw, ?_⟩
    simp [halfW]
  | succ n ih =>
    intro w hw
    refine ⟨hH (n + 1) hw, ?_⟩
    obtain ⟨hpC, hmin⟩ := (hrun n).2.2
    have hwC := ih hw
    show (J (x 0) - J (x (n + 1))) (w - x (n + 1)) ≤ 0
    apply aux_rz_proj hS J hJ (x 0) (x (n + 1)) (w - x (n + 1))
    intro t ht0 ht1
    have hzC : x (n + 1) + t • (w - x (n + 1)) ∈ halfH v y n ∩ halfW J x n :=
      ⟨aux_rz_half (v n) (y n) (x (n + 1)) w hpC.1 hwC.1 t ht0.le ht1,
        aux_rz_half (J (x 0) - J (x n)) (x n) (x (n + 1)) w hpC.2 hwC.2 t ht0.le ht1⟩
    have := hmin _ hzC
    simp only [phi] at this
    linarith
end

section
-- Prove2me | solution 1 for ProximalBanach.Hybrid.prop2_sub_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T13:17:35.821376+00:00
-- url     : https://prove2.me/submissions/5c940d75-7581-476d-884a-857f7bf4c763

set_option maxHeartbeats 3000000
open Filter Topology Set
namespace ProximalBanach.Hybrid
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem dual_norm (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x)
    (x : E) : ‖J x‖ = ‖x‖ := by
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hJ x).2

private theorem phi_norm_gap (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x)
    (y z : E) : (‖y‖ - ‖z‖)^2 ≤ phi J y z := by
  have heval : J z y ≤ ‖z‖ * ‖y‖ :=
    (le_abs_self _).trans (by simpa [dual_norm J hJ z] using (J z).le_opNorm y)
  unfold phi
  nlinarith

 theorem phi_controls_distance [UniformConvexSpace E]
    (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x)
    (M eps : ℝ) (hM : 0 ≤ M) (heps : 0 < eps) :
    ∃ rho > 0, ∀ y z : E, ‖y‖ ≤ M → ‖z‖ ≤ M → phi J y z < rho → ‖y-z‖ < eps := by
  have hMp : 0 < M+1 := by linarith
  obtain ⟨δ0,hδ0,hmod⟩ := exists_forall_closed_ball_dist_add_le_two_sub E (div_pos heps hMp)
  let δ := min δ0 1
  have hδ : 0 < δ := lt_min hδ0 zero_lt_one
  let eta := min (eps/4) (δ*eps^2/(128*(M+1)))
  have heta : 0 < eta := by dsimp [eta]; positivity
  let rho := min (eta^2) (δ*eps^2/16)
  have hrho : 0 < rho := by dsimp [rho]; positivity
  refine ⟨rho,hrho,?_⟩
  intro y z hy hz hphi
  by_contra hclose
  have hsep : eps ≤ ‖y-z‖ := le_of_not_gt hclose
  let a := ‖y‖
  let b := ‖z‖
  let m := max a b
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have haM : a ≤ M := hy
  have hbM : b ≤ M := hz
  have ham : a ≤ m := le_max_left _ _
  have hbm : b ≤ m := le_max_right _ _
  have hmM : m ≤ M := max_le hy hz
  have hgap : (a-b)^2 < eta^2 :=
    (phi_norm_gap J hJ y z).trans_lt (hphi.trans_le (min_le_left _ _))
  have hab1 : -eta < a-b := by nlinarith [sq_nonneg (a-b+eta)]
  have hab2 : a-b < eta := by nlinarith [sq_nonneg (a-b-eta)]
  have hmet : m ≤ b+eta := max_le (by linarith) (by linarith)
  have hsub : ‖y-z‖ ≤ a+b := norm_sub_le y z
  have hmpos : 0 < m := by linarith
  have heta1 : eta ≤ eps/4 := min_le_left _ _
  have hblow : eps/4 ≤ b := by linarith
  have hmlow : eps/4 ≤ m := hblow.trans hbm
  have hyn : ‖m⁻¹ • y‖ ≤ 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hmpos]
    exact (inv_mul_le_one₀ hmpos).mpr ham
  have hzn : ‖m⁻¹ • z‖ ≤ 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hmpos]
    exact (inv_mul_le_one₀ hmpos).mpr hbm
  have hdist : eps/(M+1) ≤ ‖m⁻¹ • y - m⁻¹ • z‖ := by
    rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hmpos,← div_eq_inv_mul]
    apply (div_le_div_iff₀ hMp hmpos).mpr
    nlinarith
  have hadd := hmod hyn hzn hdist
  rw [← smul_add,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hmpos,← div_eq_inv_mul] at hadd
  have hsum : ‖y+z‖ ≤ (2-δ)*m := by
    have hh := (div_le_iff₀ hmpos).mp hadd
    have hδle : δ ≤ δ0 := min_le_left _ _
    nlinarith
  have heval : J z y + b^2 ≤ b*‖y+z‖ := by
    have h1 := (le_abs_self (J z (y+z))).trans ((J z).le_opNorm (y+z))
    simpa only [map_add,(hJ z).1,dual_norm J hJ z] using h1
  have hpair : J z y + b^2 ≤ b*((2-δ)*m) :=
    heval.trans (mul_le_mul_of_nonneg_left hsum hb)
  have hphi_lower : a^2+3*b^2-4*b*m+2*δ*b*m ≤ phi J y z := by
    dsimp [phi,a,b]
    dsimp [a,b] at hpair
    nlinarith
  have hbmup : b*m ≤ b*(b+eta) := mul_le_mul_of_nonneg_left hmet hb
  have habup : 0 ≤ b*(a-b+eta) := mul_nonneg hb (by linarith)
  have hbEta : b*eta ≤ M*eta := mul_le_mul_of_nonneg_right hbM heta.le
  have hbase : -6*M*eta ≤ a^2+3*b^2-4*b*m := by nlinarith [sq_nonneg (a-b)]
  have hbmlo : eps^2/16 ≤ b*m := by
    have hh := mul_le_mul hblow hmlow (by positivity : 0 ≤ eps/4) hb
    nlinarith
  have hbig := mul_le_mul_of_nonneg_left hbmlo (show 0 ≤ 2*δ by positivity)
  have hetascale : 128*(M+1)*eta ≤ δ*eps^2 :=
    by
    have hh : eta * (128*(M+1)) ≤ δ*eps^2 :=
      (le_div_iff₀ (show 0 < 128*(M+1) by positivity)).mp (min_le_right _ _)
    nlinarith
  have hsmall : 6*M*eta ≤ δ*eps^2/16 := by nlinarith [mul_nonneg hM heta.le]
  have hrhobd : rho ≤ δ*eps^2/16 := min_le_right _ _
  nlinarith

theorem phi_sub_tendsto_zero [UniformConvexSpace E]
    (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x)
    (y z : ℕ → E) (hφ : Tendsto (fun n => phi J (y n) (z n)) atTop (𝓝 0))
    (hb : Bornology.IsBounded (Set.range y) ∨ Bornology.IsBounded (Set.range z)) :
    Tendsto (fun n => y n-z n) atTop (𝓝 0) := by
  have hsmall : ∀ᶠ n in atTop, phi J (y n) (z n) < 1 :=
    hφ.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))
  have hgap : ∀ᶠ n in atTop, |‖y n‖-‖z n‖| < 1 := by
    filter_upwards [hsmall] with n hn
    have hg := (phi_norm_gap J hJ (y n) (z n)).trans_lt hn
    rw [abs_lt]
    constructor <;> nlinarith [sq_nonneg (‖y n‖-‖z n‖+1),sq_nonneg (‖y n‖-‖z n‖-1)]
  obtain ⟨M,hM,hbd⟩ : ∃ M:ℝ, 0 ≤ M ∧ ∀ᶠ n in atTop, ‖y n‖ ≤ M ∧ ‖z n‖ ≤ M := by
    rcases hb with hy | hz
    · obtain ⟨B,hB⟩ := hy.exists_norm_le
      refine ⟨max B 0+1,by positivity,?_⟩
      filter_upwards [hgap] with n hn
      have hbn := hB (y n) (Set.mem_range_self n)
      have hmax := le_max_left B 0
      obtain ⟨hlo,hhi⟩ := abs_lt.mp hn
      constructor <;> linarith
    · obtain ⟨B,hB⟩ := hz.exists_norm_le
      refine ⟨max B 0+1,by positivity,?_⟩
      filter_upwards [hgap] with n hn
      have hbn := hB (z n) (Set.mem_range_self n)
      have hmax := le_max_left B 0
      obtain ⟨hlo,hhi⟩ := abs_lt.mp hn
      constructor <;> linarith
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  obtain ⟨rho,hrho,hcontrol⟩ := phi_controls_distance J hJ M eps hM heps
  have hnear := hφ.eventually (gt_mem_nhds hrho)
  filter_upwards [hbd,hnear] with n hn hp
  simpa only [dist_zero_right] using hcontrol (y n) (z n) hn.1 hn.2 hp
end ProximalBanach.Hybrid

namespace ProximalBanach.Hybrid

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Proposition 2 (p. 940): in a uniformly convex smooth Banach space, if
`φ(y_n, z_n) → 0` and either `{y_n}` or `{z_n}` is bounded, then `y_n - z_n → 0`. -/
theorem _root_.checked_prop2_sub_tendsto_zero [CompleteSpace E] [UniformConvexSpace E] (_hS : IsSmooth E)
    (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x) (y z : ℕ → E)
    (hφ : Tendsto (fun n => phi J (y n) (z n)) atTop (𝓝 0))
    (hb : Bornology.IsBounded (Set.range y) ∨ Bornology.IsBounded (Set.range z)) :
    Tendsto (fun n => y n - z n) atTop (𝓝 0) := by
  exact phi_sub_tendsto_zero J hJ y z hφ hb

end ProximalBanach.Hybrid
end

end

/- Complete checked body: PhiGeometry -/
section

open Filter Topology Set
open ProximalBanach.Hybrid

namespace ProximalBanach.HybridProof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dual_norm_eq (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x)
    (x : E) : ‖J x‖ = ‖x‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hJ x).2

theorem phi_norm_lower (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x)
    (u v : E) : (‖u‖ - ‖v‖)^2 ≤ phi J u v := by
  have he := (J v).le_opNorm u
  rw [dual_norm_eq J hJ v, Real.norm_eq_abs] at he
  unfold phi
  nlinarith [le_abs_self (J v u)]

theorem phi_nonneg (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x)
    (u v : E) : 0 ≤ phi J u v :=
  (sq_nonneg _).trans (phi_norm_lower J hJ u v)

theorem phi_norm_upper (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x)
    (u v : E) : phi J u v ≤ (‖u‖ + ‖v‖)^2 := by
  have he := (J v).le_opNorm u
  rw [dual_norm_eq J hJ v, Real.norm_eq_abs] at he
  unfold phi
  nlinarith [neg_abs_le (J v u)]

theorem phi_self (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x)
    (u : E) : phi J u u = 0 := by
  unfold phi
  rw [(hJ u).1]
  ring

theorem phi_continuous_left (J : E → StrongDual ℝ E) (v : E) :
    Continuous (fun u => phi J u v) := by
  unfold phi
  exact ((continuous_norm.pow 2).sub ((J v).continuous.const_mul 2)).add continuous_const

theorem phi_midpoint_identity (J : E → StrongDual ℝ E)
    (hJ : ∀ x, J x ∈ dualityMap x) (x0 u v : E) :
    phi J u x0 + phi J v x0 - 2 * phi J (midpoint ℝ u v) x0 =
      phi J u (midpoint ℝ u v) + phi J v (midpoint ℝ u v) := by
  have hm : u + v = (2 : ℝ) • midpoint ℝ u v := by
    simp [midpoint_eq_smul_add, smul_smul, invOf_eq_inv]
  have hJm := (hJ (midpoint ℝ u v)).1
  have ha := congrArg (J (midpoint ℝ u v)) hm
  have hb := congrArg (J x0) hm
  simp only [map_add, map_smul, smul_eq_mul] at ha hb
  unfold phi
  nlinarith

theorem phi_three_point (J : E → StrongDual ℝ E)
    (hJ : ∀ x, J x ∈ dualityMap x) (a b c : E) :
    phi J a b + phi J b c - phi J a c = 2 * (J c - J b) (a - b) := by
  simp only [phi, sub_apply, map_sub, (hJ b).1]
  ring

theorem phi_symmetric_sum (J : E → StrongDual ℝ E)
    (hJ : ∀ x, J x ∈ dualityMap x) (a b : E) :
    phi J a b + phi J b a = 2 * (J a - J b) (a - b) := by
  simp only [phi, sub_apply, map_sub, (hJ a).1, (hJ b).1]
  ring

theorem uniformly_smooth_isSmooth (hUS : IsUniformlySmooth E) : IsSmooth E := by
  obtain ⟨D, hD⟩ := hUS
  intro x y hx hy
  refine ⟨D x y, Metric.tendsto_nhdsWithin_nhds.2 ?_⟩
  intro ε hε
  obtain ⟨δ, hδ, hc⟩ := hD ε hε
  refine ⟨δ, hδ, fun t ht htd => ?_⟩
  simpa only [Real.dist_eq, sub_zero] using hc x y hx hy t ht (by simpa only [Real.dist_eq, sub_zero] using htd)

end ProximalBanach.HybridProof

end

/- Complete checked body: MidpointMinimization -/
section

open Filter Topology Set

namespace ProximalBanach.HybridProof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Small midpoint deficit forces bounded pairs to be close. -/
def MidpointControl (F : E → ℝ) : Prop :=
  ∀ M : ℝ, 0 ≤ M → ∀ ε : ℝ, 0 < ε → ∃ δ > 0,
    ∀ u v : E, ‖u‖ ≤ M → ‖v‖ ≤ M →
      F u + F v - 2 * F (midpoint ℝ u v) < δ → ‖u - v‖ < ε

theorem minimizing_cauchy {F : E → ℝ} (hF : MidpointControl F)
    {C : Set E} (hC : Convex ℝ C) {a M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ u ∈ C, ‖u‖ ≤ M) (hlower : ∀ u ∈ C, a ≤ F u)
    (u : ℕ → E) (hu : ∀ n, u n ∈ C)
    (hlim : Tendsto (fun n => F (u n)) atTop (𝓝 a)) : CauchySeq u := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨δ, hδ, hcontrol⟩ := hF M hM ε hε
  have he : ∀ᶠ n in atTop, F (u n) < a + δ / 2 :=
    hlim.eventually (gt_mem_nhds (by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.1 he
  refine ⟨N, fun i hi j hj => ?_⟩
  have hm := hlower _ (hC.midpoint_mem (hu i) (hu j))
  have hsmall : F (u i) + F (u j) - 2 * F (midpoint ℝ (u i) (u j)) < δ := by
    have := hN i hi
    have := hN j hj
    linarith
  simpa only [dist_eq_norm] using hcontrol (u i) (u j)
    (hbound _ (hu i)) (hbound _ (hu j)) hsmall

theorem exists_minimizer_of_midpoint [CompleteSpace E] {F : E → ℝ}
    (hF : Continuous F) (hcontrol : MidpointControl F)
    {C : Set E} (hne : C.Nonempty) (hclosed : IsClosed C) (hconv : Convex ℝ C)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ u ∈ C, ‖u‖ ≤ M)
    (hlower : BddBelow (F '' C)) : ∃ q ∈ C, ∀ u ∈ C, F q ≤ F u := by
  classical
  obtain ⟨a, _ha, halim, haC⟩ := exists_seq_tendsto_sInf (hne.image F) hlower
  have hex : ∀ n, ∃ u ∈ C, F u = a n := fun n => haC n
  choose u hu hua using hex
  have hulim : Tendsto (fun n => F (u n)) atTop (𝓝 (sInf (F '' C))) := by
    simpa only [hua] using halim
  have hmin : ∀ x ∈ C, sInf (F '' C) ≤ F x :=
    fun x hx => csInf_le hlower ⟨x, hx, rfl⟩
  have huc := minimizing_cauchy hcontrol hconv hM hbound hmin u hu hulim
  obtain ⟨q, hq⟩ := cauchySeq_tendsto_of_complete huc
  have hqC : q ∈ C := hclosed.mem_of_tendsto hq (Eventually.of_forall hu)
  have hval : F q = sInf (F '' C) := tendsto_nhds_unique (hF.tendsto q |>.comp hq) hulim
  refine ⟨q, hqC, fun x hx => ?_⟩
  rw [hval]
  exact hmin x hx

theorem nested_minimizers_cauchy {F : E → ℝ} (hcontrol : MidpointControl F)
    (C : ℕ → Set E) (hconv : ∀ n, Convex ℝ (C n)) (hnest : Antitone C)
    (q : ℕ → E) (hq : ∀ n, q n ∈ C n)
    (hmin : ∀ n u, u ∈ C n → F (q n) ≤ F u)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ n, ‖q n‖ ≤ M)
    (hbdd : BddAbove (range (fun n => F (q n)))) : CauchySeq q := by
  have hmono : Monotone (fun n => F (q n)) := by
    intro i j hij
    exact hmin i (q j) (hnest hij (hq j))
  have hlim := tendsto_atTop_ciSup hmono hbdd
  have hreal := Metric.cauchySeq_iff.1 hlim.cauchySeq
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨δ, hδ, hc⟩ := hcontrol M hM ε hε
  obtain ⟨N, hN⟩ := hreal δ hδ
  refine ⟨N, fun i hi j hj => ?_⟩
  have hdefect : F (q i) + F (q j) - 2 * F (midpoint ℝ (q i) (q j)) < δ := by
    rcases le_total i j with hij | hji
    · have hmid := hmin i _ (hconv i |>.midpoint_mem (hq i) (hnest hij (hq j)))
      have hd := hN j hj i hi
      rw [Real.dist_eq] at hd
      have := (abs_lt.1 hd).2
      linarith
    · have hmid := hmin j _ (hconv j |>.midpoint_mem (hnest hji (hq i)) (hq j))
      have hd := hN i hi j hj
      rw [Real.dist_eq] at hd
      have := (abs_lt.1 hd).2
      linarith
  simpa only [dist_eq_norm] using hc (q i) (q j) (hbound i) (hbound j) hdefect

theorem nested_minimizers_limit [CompleteSpace E] {F : E → ℝ}
    (hcontrol : MidpointControl F) (C : ℕ → Set E)
    (hclosed : ∀ n, IsClosed (C n)) (hconv : ∀ n, Convex ℝ (C n))
    (hnest : Antitone C) (q : ℕ → E) (hq : ∀ n, q n ∈ C n)
    (hmin : ∀ n u, u ∈ C n → F (q n) ≤ F u)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ n, ‖q n‖ ≤ M)
    (hbdd : BddAbove (range (fun n => F (q n)))) :
    ∃ z, Tendsto q atTop (𝓝 z) ∧ ∀ n, z ∈ C n := by
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete
    (nested_minimizers_cauchy hcontrol C hconv hnest q hq hmin hM hbound hbdd)
  refine ⟨z, hz, fun n => ?_⟩
  exact (hclosed n).mem_of_tendsto hz
    (eventually_atTop.2 ⟨n, fun k hk => hnest hk (hq k)⟩)

end ProximalBanach.HybridProof

end

/- Complete checked body: PhiMidpoint -/
section

open ProximalBanach.Hybrid

namespace ProximalBanach.HybridProof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [UniformConvexSpace E]

theorem phi_midpoint_control (J : E → StrongDual ℝ E)
    (hJ : ∀ x, J x ∈ dualityMap x) (x0 : E) :
    MidpointControl (fun u => phi J u x0) := by
  intro M hM ε hε
  obtain ⟨δ, hδ, hc⟩ := phi_controls_distance J hJ M (ε / 2) hM (by positivity)
  refine ⟨δ, hδ, fun u v hu hv hdef => ?_⟩
  let m := midpoint ℝ u v
  have hm : ‖m‖ ≤ M := by
    have h := (convex_closedBall (0 : E) M).midpoint_mem
      (show u ∈ Metric.closedBall (0 : E) M by simpa using hu)
      (show v ∈ Metric.closedBall (0 : E) M by simpa using hv)
    simpa only [Metric.mem_closedBall, dist_zero_right] using h
  rw [phi_midpoint_identity J hJ] at hdef
  have hu' : ‖u-m‖ < ε / 2 := hc u m hu hm (by have := phi_nonneg J hJ v m; linarith)
  have hv' : ‖v-m‖ < ε / 2 := hc v m hv hm (by have := phi_nonneg J hJ u m; linarith)
  have h := norm_sub_le (u-m) (v-m)
  have he : u-m-(v-m) = u-v := by abel
  rw [he] at h
  linarith

end ProximalBanach.HybridProof

end

/- Complete checked body: RunBounds -/
section

open Filter Topology Set
open ProximalBanach.Hybrid

namespace ProximalBanach.HybridProof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem zeros_in_halfspaces (hS : IsSmooth E)
    (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x)
    (T : E → Set (StrongDual ℝ E)) (hT : IsMonotoneOp T)
    (r : ℕ → ℝ) (x y : ℕ → E) (v : ℕ → StrongDual ℝ E)
    (hrun : IsHybridRun T J r x y v) :
    ∀ n, zeros T ⊆ halfH v y n ∩ halfW J x n := by
  have hH := aux_rz_H T hT J r x y v hrun
  intro n
  induction n with
  | zero =>
    intro w hw
    refine ⟨hH 0 hw, ?_⟩
    simp [halfW]
  | succ n ih =>
    intro w hw
    refine ⟨hH (n + 1) hw, ?_⟩
    obtain ⟨hpC, hmin⟩ := (hrun n).2.2
    have hwC := ih hw
    show (J (x 0) - J (x (n + 1))) (w - x (n + 1)) ≤ 0
    apply aux_rz_proj hS J hJ (x 0) (x (n + 1)) (w - x (n + 1))
    intro t ht0 ht1
    have hzC : x (n + 1) + t • (w - x (n + 1)) ∈ halfH v y n ∩ halfW J x n :=
      ⟨aux_rz_half (v n) (y n) (x (n + 1)) w hpC.1 hwC.1 t ht0.le ht1,
        aux_rz_half (J (x 0) - J (x n)) (x n) (x (n + 1)) w hpC.2 hwC.2 t ht0.le ht1⟩
    have := hmin _ hzC
    simp only [phi] at this
    linarith

theorem run_upper_bound (hUS : IsUniformlySmooth E)
    (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x)
    (T : E → Set (StrongDual ℝ E)) (hT : IsMonotoneOp T)
    (r : ℕ → ℝ) (x y : ℕ → E) (v : ℕ → StrongDual ℝ E)
    (hrun : IsHybridRun T J r x y v) :
    ∀ n z, z ∈ zeros T → phi J (x n) (x 0) ≤ phi J z (x 0) := by
  intro n z hz
  cases n with
  | zero => rw [phi_self J hJ]; exact phi_nonneg J hJ z (x 0)
  | succ n =>
    exact (hrun n).2.2.2 z
      (zeros_in_halfspaces (uniformly_smooth_isSmooth hUS) J hJ T hT r x y v hrun n hz)

theorem run_bounded (hUS : IsUniformlySmooth E)
    (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x)
    (T : E → Set (StrongDual ℝ E)) (hT : IsMonotoneOp T) (hZ : (zeros T).Nonempty)
    (r : ℕ → ℝ) (x y : ℕ → E) (v : ℕ → StrongDual ℝ E)
    (hrun : IsHybridRun T J r x y v) : ∃ M ≥ 0, ∀ n, ‖x n‖ ≤ M := by
  obtain ⟨w, hw⟩ := hZ
  refine ⟨2 * ‖x 0‖ + ‖w‖, by positivity, fun n => ?_⟩
  have h := (phi_norm_lower J hJ (x n) (x 0)).trans
    ((run_upper_bound hUS J hJ T hT r x y v hrun n w hw).trans
      (phi_norm_upper J hJ w (x 0)))
  nlinarith [norm_nonneg (x n), norm_nonneg (x 0), norm_nonneg w]

theorem run_phi_step (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x)
    (T : E → Set (StrongDual ℝ E)) (r : ℕ → ℝ)
    (x y : ℕ → E) (v : ℕ → StrongDual ℝ E)
    (hrun : IsHybridRun T J r x y v) (n : ℕ) :
    phi J (x (n+1)) (x n) + phi J (x n) (x 0) ≤ phi J (x (n+1)) (x 0) := by
  have hw : (J (x 0) - J (x n)) (x (n+1) - x n) ≤ 0 := (hrun n).2.2.1.2
  have hi := phi_three_point J hJ (x (n+1)) (x n) (x 0)
  linarith

theorem run_adjacent_tendsto [UniformConvexSpace E]
    (hUS : IsUniformlySmooth E)
    (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x)
    (T : E → Set (StrongDual ℝ E)) (hT : IsMonotoneOp T) (hZ : (zeros T).Nonempty)
    (r : ℕ → ℝ) (x y : ℕ → E) (v : ℕ → StrongDual ℝ E)
    (hrun : IsHybridRun T J r x y v) :
    Tendsto (fun n => x (n+1) - x n) atTop (𝓝 0) := by
  obtain ⟨w, hw⟩ := hZ
  have hm : Monotone (fun n => phi J (x n) (x 0)) := by
    apply monotone_nat_of_le_succ
    intro n
    have := run_phi_step J hJ T r x y v hrun n
    have := phi_nonneg J hJ (x (n+1)) (x n)
    linarith
  have hb : BddAbove (range (fun n => phi J (x n) (x 0))) :=
    ⟨phi J w (x 0), by rintro _ ⟨n, rfl⟩; exact run_upper_bound hUS J hJ T hT r x y v hrun n w hw⟩
  have hlim := tendsto_atTop_ciSup hm hb
  have hdiff := (hlim.comp (tendsto_add_atTop_nat 1)).sub hlim
  simp only [Function.comp_apply, sub_self] at hdiff
  have hp : Tendsto (fun n => phi J (x (n+1)) (x n)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdiff
    · exact fun n => phi_nonneg J hJ _ _
    · intro n
      have := run_phi_step J hJ T r x y v hrun n
      linarith
  obtain ⟨M, _hM, hM⟩ := run_bounded hUS J hJ T hT ⟨w,hw⟩ r x y v hrun
  apply phi_sub_tendsto_zero J hJ _ _ hp
  right
  rw [isBounded_iff_forall_norm_le]
  exact ⟨M, by rintro _ ⟨n,rfl⟩; exact hM n⟩

end ProximalBanach.HybridProof

end

/- Complete checked body: ResolventBounds -/
section

open Filter Topology Set
open ProximalBanach.Hybrid

namespace ProximalBanach.HybridProof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem resolvent_identity (J : E → StrongDual ℝ E)
    (T : E → Set (StrongDual ℝ E)) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (x y : ℕ → E) (v : ℕ → StrongDual ℝ E)
    (hrun : IsHybridRun T J r x y v) (n : ℕ) :
    J (x n) - J (y n) = r n • v n := by
  have h := congrArg (fun u : StrongDual ℝ E => r n • u) (hrun n).2.1
  simp only [smul_add, smul_smul, mul_inv_cancel₀ (hr n).ne', one_smul, smul_zero] at h
  have he := eq_neg_of_add_eq_zero_left h
  simpa only [neg_sub] using he.symm

theorem resolvent_phi_bound (J : E → StrongDual ℝ E)
    (hJ : ∀ x, J x ∈ dualityMap x)
    (T : E → Set (StrongDual ℝ E)) (hT : IsMonotoneOp T)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (x y : ℕ → E) (v : ℕ → StrongDual ℝ E)
    (hrun : IsHybridRun T J r x y v) (w : E) (hw : w ∈ zeros T) (n : ℕ) :
    phi J w (y n) + phi J (y n) (x n) ≤ phi J w (x n) := by
  have hi := phi_three_point J hJ w (y n) (x n)
  rw [resolvent_identity J T r hr x y v hrun n, smul_apply, smul_eq_mul] at hi
  have hh : v n (w - y n) ≤ 0 := aux_rz_H T hT J r x y v hrun n hw
  have := mul_nonpos_of_nonneg_of_nonpos (hr n).le hh
  linarith

theorem run_y_bounded (hUS : IsUniformlySmooth E)
    (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x)
    (T : E → Set (StrongDual ℝ E)) (hT : IsMonotoneOp T) (hZ : (zeros T).Nonempty)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (x y : ℕ → E) (v : ℕ → StrongDual ℝ E)
    (hrun : IsHybridRun T J r x y v) : ∃ M ≥ 0, ∀ n, ‖y n‖ ≤ M := by
  obtain ⟨M, hM, hx⟩ := run_bounded hUS J hJ T hT hZ r x y v hrun
  obtain ⟨w, hw⟩ := hZ
  refine ⟨2 * ‖w‖ + M, by positivity, fun n => ?_⟩
  have hp := resolvent_phi_bound J hJ T hT r hr x y v hrun w hw n
  have hl := phi_norm_lower J hJ w (y n)
  have hu := phi_norm_upper J hJ w (x n)
  have hn := phi_nonneg J hJ (y n) (x n)
  have hh := hx n
  nlinarith [norm_nonneg w, norm_nonneg (x n), norm_nonneg (y n)]

theorem resolvent_phi_step (J : E → StrongDual ℝ E)
    (hJ : ∀ x, J x ∈ dualityMap x)
    (T : E → Set (StrongDual ℝ E)) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (x y : ℕ → E) (v : ℕ → StrongDual ℝ E)
    (hrun : IsHybridRun T J r x y v) (n : ℕ) :
    phi J (y n) (x n) ≤
      2 * (‖x n‖ + ‖y n‖) * ‖x (n+1) - x n‖ := by
  let A := J (x n) - J (y n)
  have hh : A (x (n+1) - y n) ≤ 0 := by
    dsimp [A]
    rw [resolvent_identity J T r hr x y v hrun n, smul_apply, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (hr n).le (hrun n).2.2.1.1
  have he : A (x n-y n) = A (x n-x (n+1)) + A (x (n+1)-y n) := by
    rw [← map_add]
    congr 1
    abel
  have hb := (le_abs_self (A (x n-x (n+1)))).trans (A.le_opNorm _)
  rw [norm_sub_rev (x n) (x (n+1))] at hb
  have hA : ‖A‖ ≤ ‖x n‖ + ‖y n‖ := by
    simpa only [A, dual_norm_eq J hJ] using norm_sub_le (J (x n)) (J (y n))
  have hs := phi_symmetric_sum J hJ (x n) (y n)
  have hn := phi_nonneg J hJ (x n) (y n)
  have hc := mul_le_mul_of_nonneg_right hA (norm_nonneg (x (n+1)-x n))
  change phi J (x n) (y n) + phi J (y n) (x n) = 2 * A (x n-y n) at hs
  nlinarith

end ProximalBanach.HybridProof

end

/- Complete checked body: RunResiduals -/
section

open Filter Topology Set
open ProximalBanach.Hybrid

namespace ProximalBanach.HybridProof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [UniformConvexSpace E]

theorem run_primal_residual (hUS : IsUniformlySmooth E)
    (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x)
    (T : E → Set (StrongDual ℝ E)) (hT : IsMonotoneOp T) (hZ : (zeros T).Nonempty)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (x y : ℕ → E) (v : ℕ → StrongDual ℝ E)
    (hrun : IsHybridRun T J r x y v) :
    Tendsto (fun n => x n - y n) atTop (𝓝 0) := by
  obtain ⟨M, hM, hx⟩ := run_bounded hUS J hJ T hT hZ r x y v hrun
  obtain ⟨N, hN, hy⟩ := run_y_bounded hUS J hJ T hT hZ r hr x y v hrun
  have hstep := (run_adjacent_tendsto hUS J hJ T hT hZ r x y v hrun).norm
  simp only [norm_zero] at hstep
  have hb := hstep.const_mul (2 * (M+N))
  simp only [mul_zero] at hb
  have hp : Tendsto (fun n => phi J (y n) (x n)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    · exact fun n => phi_nonneg J hJ _ _
    · intro n
      refine (resolvent_phi_step J hJ T r hr x y v hrun n).trans ?_
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add (hx n) (hy n)) (by norm_num)) (norm_nonneg _)
  have hbounded : Bornology.IsBounded (range x) :=
    isBounded_iff_forall_norm_le.2 ⟨M, by rintro _ ⟨n,rfl⟩; exact hx n⟩
  have h := (phi_sub_tendsto_zero J hJ y x hp (Or.inr hbounded)).neg
  simpa only [neg_sub, neg_zero] using h

theorem run_dual_residual (hUS : IsUniformlySmooth E)
    (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x)
    (T : E → Set (StrongDual ℝ E)) (hT : IsMonotoneOp T) (hZ : (zeros T).Nonempty)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (x y : ℕ → E) (v : ℕ → StrongDual ℝ E)
    (hrun : IsHybridRun T J r x y v) :
    Tendsto (fun n => J (x n) - J (y n)) atTop (𝓝 0) := by
  obtain ⟨M, hM, hx⟩ := run_bounded hUS J hJ T hT hZ r x y v hrun
  obtain ⟨N, hN, hy⟩ := run_y_bounded hUS J hJ T hT hZ r hr x y v hrun
  have hu := duality_uniform_on_bounded hUS J hJ
    (Metric.closedBall (0 : E) (M+N)) Metric.isBounded_closedBall
  have hp := (run_primal_residual hUS J hJ T hT hZ r hr x y v hrun).norm
  simp only [norm_zero] at hp
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨δ, hδ, hc⟩ := Metric.uniformContinuousOn_iff.1 hu ε hε
  filter_upwards [hp.eventually (gt_mem_nhds hδ)] with n hn
  have hxn : x n ∈ Metric.closedBall (0 : E) (M+N) := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (hx n).trans (le_add_of_nonneg_right hN)
  have hyn : y n ∈ Metric.closedBall (0 : E) (M+N) := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (hy n).trans (le_add_of_nonneg_left hM)
  simpa only [dist_zero_right, dist_eq_norm, sub_zero] using hc (x n) hxn (y n) hyn
    (by simpa only [dist_eq_norm] using hn)

theorem run_graph_residual (hUS : IsUniformlySmooth E)
    (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x)
    (T : E → Set (StrongDual ℝ E)) (hT : IsMonotoneOp T) (hZ : (zeros T).Nonempty)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hlim : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, c ≤ r n)
    (x y : ℕ → E) (v : ℕ → StrongDual ℝ E)
    (hrun : IsHybridRun T J r x y v) : Tendsto v atTop (𝓝 0) := by
  obtain ⟨c, hc, hcr⟩ := hlim
  have hd := (run_dual_residual hUS J hJ T hT hZ r hr x y v hrun).norm
  simp only [norm_zero] at hd
  have hb := hd.const_mul c⁻¹
  simp only [mul_zero] at hb
  apply Metric.tendsto_nhds.2
  intro ε hε
  filter_upwards [hcr, hb.eventually (gt_mem_nhds hε)] with n hn hεn
  have he := congrArg norm (resolvent_identity J T r hr x y v hrun n)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hr n)] at he
  have hle : ‖v n‖ ≤ c⁻¹ * ‖J (x n)-J (y n)‖ := by
    rw [he, inv_mul_eq_div, le_div_iff₀ hc]
    nlinarith [norm_nonneg (v n)]
  simpa only [dist_zero_right] using hle.trans_lt hεn

end ProximalBanach.HybridProof

end

/- Complete checked body: ConvexTailHulls -/
section

open Filter Topology Set

namespace ProximalBanach.HybridProof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def tailHull (x : ℕ → E) (n : ℕ) : Set E :=
  closure (convexHull ℝ (x '' Ici n))

theorem mem_tailHull (x : ℕ → E) {n k : ℕ} (hnk : n ≤ k) : x k ∈ tailHull x n :=
  subset_closure (subset_convexHull ℝ _ ⟨k, hnk, rfl⟩)

theorem tailHull_nonempty (x : ℕ → E) (n : ℕ) : (tailHull x n).Nonempty :=
  ⟨x n, mem_tailHull x le_rfl⟩

theorem tailHull_closed (x : ℕ → E) (n : ℕ) : IsClosed (tailHull x n) := isClosed_closure

theorem tailHull_convex (x : ℕ → E) (n : ℕ) : Convex ℝ (tailHull x n) :=
  (convex_convexHull ℝ _).closure

theorem tailHull_antitone (x : ℕ → E) : Antitone (tailHull x) := by
  intro i j hij
  exact closure_mono (convexHull_mono (image_mono (Ici_subset_Ici.mpr hij)))

theorem tailHull_norm_le (x : ℕ → E) {M : ℝ} (hx : ∀ k, ‖x k‖ ≤ M)
    (n : ℕ) : ∀ u ∈ tailHull x n, ‖u‖ ≤ M := by
  have hs : x '' Ici n ⊆ Metric.closedBall (0 : E) M := by
    rintro _ ⟨k, _hk, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx k
  have hc := closure_minimal (convexHull_min hs (convex_closedBall (0 : E) M))
    Metric.isClosed_closedBall
  intro u hu
  simpa only [Metric.mem_closedBall, dist_zero_right] using hc hu

theorem tailHull_subset_of_eventually (x : ℕ → E) {C : Set E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C)
    (he : ∀ᶠ n in atTop, x n ∈ C) : ∃ N, tailHull x N ⊆ C := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 he
  refine ⟨N, closure_minimal (convexHull_min ?_ hconv) hclosed⟩
  rintro _ ⟨k, hk, rfl⟩
  exact hN k hk

theorem convergence_of_tail_minima [CompleteSpace E] {F : E → ℝ}
    (hF : Continuous F) (hcontrol : MidpointControl F) (hpos : ∀ u, 0 ≤ F u)
    (x : ℕ → E) {M : ℝ} (hM : 0 ≤ M) (hx : ∀ k, ‖x k‖ ≤ M)
    {Z : Set E} (hZ : Z.Nonempty)
    (hupper : ∀ n z, z ∈ Z → F (x n) ≤ F z)
    (hidentify : ∀ z, (∀ n, z ∈ tailHull x n) → z ∈ Z) :
    ∃ z ∈ Z, Tendsto x atTop (𝓝 z) ∧ ∀ w ∈ Z, F z ≤ F w := by
  classical
  have hex : ∀ n, ∃ q ∈ tailHull x n, ∀ u ∈ tailHull x n, F q ≤ F u := by
    intro n
    apply exists_minimizer_of_midpoint hF hcontrol (tailHull_nonempty x n)
      (tailHull_closed x n) (tailHull_convex x n) hM (tailHull_norm_le x hx n)
    exact ⟨0, by rintro _ ⟨u, _hu, rfl⟩; exact hpos u⟩
  choose q hq hmin using hex
  have hqbound : ∀ n, ‖q n‖ ≤ M := fun n => tailHull_norm_le x hx n _ (hq n)
  obtain ⟨w, hw⟩ := hZ
  have hbdd : BddAbove (range (fun n => F (q n))) := by
    refine ⟨F w, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (hmin n _ (mem_tailHull x le_rfl)).trans (hupper n w hw)
  obtain ⟨z, hqz, hzC⟩ := nested_minimizers_limit hcontrol (tailHull x)
    (tailHull_closed x) (tailHull_convex x) (tailHull_antitone x)
    q hq hmin hM hqbound hbdd
  have hz : z ∈ Z := hidentify z hzC
  have hFlim : Tendsto (fun n => F (x n)) atTop (𝓝 (F z)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le (hF.continuousAt.tendsto.comp hqz)
      tendsto_const_nhds
    · exact fun n => hmin n _ (mem_tailHull x le_rfl)
    · exact fun n => hupper n z hz
  have hgap : Tendsto (fun n => F (x n) - F (q n)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, sub_self] using hFlim.sub (hF.continuousAt.tendsto.comp hqz)
  have hdist : Tendsto (fun n => x n - q n) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ, hδ, hc⟩ := hcontrol M hM ε hε
    have he : ∀ᶠ n in atTop, F (x n) - F (q n) < δ :=
      hgap.eventually (gt_mem_nhds hδ)
    obtain ⟨N, hN⟩ := eventually_atTop.1 he
    refine ⟨N, fun n hn => ?_⟩
    have hm := hmin n _ ((tailHull_convex x n).midpoint_mem
      (mem_tailHull x le_rfl) (hq n))
    have hdef : F (x n) + F (q n) - 2 * F (midpoint ℝ (x n) (q n)) < δ := by
      have := hN n hn
      linarith
    simpa only [Real.dist_eq, sub_zero, abs_norm] using hc _ _ (hx n) (hqbound n) hdef
  have hxz : Tendsto x atTop (𝓝 z) := by
    have hh := hdist.add hqz
    simpa only [sub_add_cancel, zero_add] using hh
  refine ⟨z, hz, hxz, fun u hu => ?_⟩
  exact le_of_tendsto hFlim (Eventually.of_forall (fun n => hupper n u hu))

end ProximalBanach.HybridProof

end

/- Complete checked body: TailIdentification -/
section

open Filter Topology Set
open ProximalBanach.Hybrid

namespace ProximalBanach.HybridProof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem zero_of_minty (T : E → Set (StrongDual ℝ E)) (hT : IsMaximalMonotone T)
    (z : E) (hz : ∀ a b, b ∈ T a → b (z-a) ≤ 0) : z ∈ zeros T := by
  let U : E → Set (StrongDual ℝ E) := fun a => {b | b ∈ T a ∨ a=z ∧ b=0}
  have hU : IsMonotoneOp U := by
    intro a c b hb d hd
    rcases hb with hb | ⟨rfl,rfl⟩
    · rcases hd with hd | ⟨rfl,rfl⟩
      · exact hT.1 a c b hb d hd
      · simp only [sub_zero]
        have hh := hz a b hb
        have he : b (a-c) = -b (c-a) := by rw [← map_neg, neg_sub]
        linarith
    · rcases hd with hd | ⟨rfl,rfl⟩
      · simpa only [zero_sub, neg_apply, neg_nonneg] using hz c d hd
      · simp
  have he : U=T := hT.2 U hU (fun a b hb => Or.inl hb)
  have hm : (0 : StrongDual ℝ E) ∈ U z := Or.inr ⟨rfl,rfl⟩
  rw [he] at hm
  exact hm

theorem tailHull_zero [UniformConvexSpace E]
    (hUS : IsUniformlySmooth E)
    (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x)
    (T : E → Set (StrongDual ℝ E)) (hT : IsMaximalMonotone T) (hZ : (zeros T).Nonempty)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hlim : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, c ≤ r n)
    (x y : ℕ → E) (v : ℕ → StrongDual ℝ E)
    (hrun : IsHybridRun T J r x y v) (z : E) (hz : ∀ n, z ∈ tailHull x n) :
    z ∈ zeros T := by
  apply zero_of_minty T hT z
  intro a b hb
  obtain ⟨M, hM, hy⟩ := run_y_bounded hUS J hJ T hT.1 hZ r hr x y v hrun
  have hp := (run_primal_residual hUS J hJ T hT.1 hZ r hr x y v hrun).norm
  have hv := (run_graph_residual hUS J hJ T hT.1 hZ r hr hlim x y v hrun).norm
  simp only [norm_zero] at hp hv
  have he := (hp.const_mul ‖b‖).add (hv.mul_const (M+‖a‖))
  simp only [mul_zero, zero_mul, zero_add] at he
  have hbnd : ∀ n, b (x n-a) ≤ ‖b‖ * ‖x n-y n‖ + ‖v n‖ * (M+‖a‖) := by
    intro n
    have hmon := hT.1 (y n) a (v n) (hrun n).1 b hb
    simp only [sub_apply] at hmon
    have hvb := (le_abs_self (v n (y n-a))).trans ((v n).le_opNorm _)
    have hbb := (le_abs_self (b (x n-y n))).trans (b.le_opNorm _)
    have hya := (norm_sub_le (y n) a).trans (add_le_add (hy n) le_rfl)
    have hmul := mul_le_mul_of_nonneg_left hya (norm_nonneg (v n))
    have hid : b (x n-a) = b (x n-y n) + b (y n-a) := by
      rw [← map_add]
      congr 1
      abel
    linarith
  by_contra! hpos
  let ε := b (z-a) / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hevent : ∀ᶠ n in atTop, b (x n) ≤ b a + ε := by
    filter_upwards [he.eventually (gt_mem_nhds hε)] with n hn
    have hh := hbnd n
    rw [map_sub] at hh
    linarith
  have hc : IsClosed {u : E | b u ≤ b a+ε} := isClosed_le b.continuous continuous_const
  have hvx : Convex ℝ {u : E | b u ≤ b a+ε} := by
    exact (convex_Iic (b a+ε)).linear_preimage b.toLinearMap
  obtain ⟨N, hN⟩ := tailHull_subset_of_eventually x hc hvx hevent
  have hh : b z ≤ b a+ε := hN (hz N)
  dsimp [ε] at hh
  rw [map_sub] at hh hpos
  linarith

end ProximalBanach.HybridProof

end

/- Complete checked body: BanachRoot -/
section

namespace ProximalBanach.Hybrid

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Theorem 8 (p. 942): let `E` be uniformly convex and uniformly smooth and `T` maximal
monotone with `T⁻¹0 ≠ ∅`. If `r_n > 0` and `liminf r_n > 0`, then every run `{x_n}` of (3.1)
converges strongly to `Q_{T⁻¹0} x_0`. -/
theorem hybrid_proximal_strong_convergence [UniformConvexSpace E]
    (hUS : IsUniformlySmooth E) (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x)
    (T : E → Set (StrongDual ℝ E)) (hT : IsMaximalMonotone T) (hZ : (zeros T).Nonempty)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hlim : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, c ≤ r n)
    (x y : ℕ → E) (v : ℕ → StrongDual ℝ E) (hrun : IsHybridRun T J r x y v) :
    ∃ z : E, IsGenProj J (zeros T) (x 0) z ∧ Tendsto x atTop (𝓝 z) := by
  obtain ⟨M, hM, hx⟩ := ProximalBanach.HybridProof.run_bounded
    hUS J hJ T hT.1 hZ r x y v hrun
  obtain ⟨z, hz, hconv, hmin⟩ := ProximalBanach.HybridProof.convergence_of_tail_minima
    (ProximalBanach.HybridProof.phi_continuous_left J (x 0))
    (ProximalBanach.HybridProof.phi_midpoint_control J hJ (x 0))
    (fun u => ProximalBanach.HybridProof.phi_nonneg J hJ u (x 0))
    x hM hx hZ
    (ProximalBanach.HybridProof.run_upper_bound hUS J hJ T hT.1 r x y v hrun)
    (ProximalBanach.HybridProof.tailHull_zero hUS J hJ T hT hZ r hr hlim x y v hrun)
  exact ⟨z, ⟨hz, hmin⟩, hconv⟩

end ProximalBanach.Hybrid

end

open ProximalBanach.Hybrid
open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem solution [UniformConvexSpace E]
    (hUS : IsUniformlySmooth E) (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x)
    (T : E → Set (StrongDual ℝ E)) (hT : IsMaximalMonotone T) (hZ : (zeros T).Nonempty)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hlim : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, c ≤ r n)
    (x y : ℕ → E) (v : ℕ → StrongDual ℝ E) (hrun : IsHybridRun T J r x y v) :
    ∃ z : E, IsGenProj J (zeros T) (x 0) z ∧ Tendsto x atTop (𝓝 z) := by
  exact ProximalBanach.Hybrid.hybrid_proximal_strong_convergence hUS J hJ T hT hZ r hr hlim x y v hrun

#print axioms ProximalBanach.Hybrid.hybrid_proximal_strong_convergence
#print axioms solution
