-- Prove2me | solution 1 for ProximalBanach.Hybrid.duality_uniformContinuousOn
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T13:20:10.573996+00:00
-- url     : https://prove2.me/submissions/2e56ddc8-f7aa-4add-9c91-dd485e79495a

import Definitions.Def_ProximalBanach_Hybrid_Basic
set_option maxHeartbeats 1000000
open Filter Topology Set
namespace ProximalBanach.Hybrid
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem support_eval_le (x u : E) (hx : ‖x‖=1)
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
    simp only [ContinuousLinearMap.sub_apply,Real.norm_eq_abs]
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
  · simp [norm_smul,abs_of_pos hx,inv_mul_cancel₀ (ne_of_gt hx)]
  · simp [norm_smul,hn,abs_of_pos hx,inv_mul_cancel₀ (ne_of_gt hx)]
  · simp only [ContinuousLinearMap.smul_apply,map_smul,smul_eq_mul,(hJ x).1]
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
        _ = eps/4 := by field_simp <;> ring
    exact hh.trans_le hfrac
  dsimp [a,b] at hestimate
  linarith
end ProximalBanach.Hybrid

namespace ProximalBanach.Hybrid

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- §2, p. 939, property 4 of the duality mapping: if `E` is uniformly smooth, then `J` is
uniformly norm-to-norm continuous on each bounded subset of `E`. -/
theorem _root_.solution (hUS : IsUniformlySmooth E) (J : E → StrongDual ℝ E)
    (hJ : ∀ x, J x ∈ dualityMap x) (B : Set E) (hB : Bornology.IsBounded B) :
    UniformContinuousOn J B := by
  exact duality_uniform_on_bounded hUS J hJ B hB

end ProximalBanach.Hybrid
