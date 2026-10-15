-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_complex_stirling
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-14T12:17:22.344333+00:00
-- url     : https://prove2.me/submissions/e3a2ddbe-f006-4eb2-bda3-7c9047d0b6eb

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex Set MeasureTheory
namespace RHHighStirling
noncomputable def B2 (w : ℂ) : ℂ := w^2-w+1/6
noncomputable def B3 (w : ℂ) : ℂ := w^3-3/2*w^2+1/2*w
noncomputable def B4 (w : ℂ) : ℂ := w^4-2*w^3+w^2-1/30
noncomputable def H (z w : ℂ) : ℂ :=
  -(z+1/2)*Complex.log (z+w)+(z+w)-B2 w/(2*(z+w))-
    B3 w/(6*(z+w)^2)-B4 w/(12*(z+w)^3)
lemma primitive_derivative (z w : ℂ) (hp : 0<(z+w).re) :
    HasDerivAt (H z) (B4 w/(4*(z+w)^4)) w := by
  have hn : z+w≠0 := fun h => by simp [h] at hp
  have hz : HasDerivAt (fun s : ℂ => z+s) 1 w := (hasDerivAt_id w).const_add z
  have hl := (Complex.hasDerivAt_log (show z+w∈slitPlane from Or.inl hp)).comp w hz
  have hb2 : HasDerivAt B2 (2*w-1) w := by
    convert (((hasDerivAt_id w).pow 2).sub (hasDerivAt_id w)).add_const (1/6) using 1 <;>
      (try funext s) <;> norm_num [B2] <;> (first | rfl | ring)
  have hb3 : HasDerivAt B3 (3*w^2-3*w+1/2) w := by
    convert (((hasDerivAt_id w).pow 3).sub (((hasDerivAt_id w).pow 2).const_mul (3/2))).add
      ((hasDerivAt_id w).const_mul (1/2)) using 1 <;> (try funext s) <;> norm_num [B3] <;> (first | rfl | ring)
  have hb4 : HasDerivAt B4 (4*w^3-6*w^2+2*w) w := by
    convert ((((hasDerivAt_id w).pow 4).sub (((hasDerivAt_id w).pow 3).const_mul 2)).add
      ((hasDerivAt_id w).pow 2)).sub_const (1/30) using 1 <;> (try funext s) <;> norm_num [B4] <;> (first | rfl | ring)
  have h1 := hb2.div (hz.const_mul 2) (mul_ne_zero (by norm_num) hn)
  have h2 := hb3.div ((hz.pow 2).const_mul 6)
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 hn))
  have h3 := hb4.div ((hz.pow 3).const_mul 12)
    (mul_ne_zero (by norm_num) (pow_ne_zero 3 hn))
  have hh := ((((hl.const_mul (-(z+1/2))).add hz).sub h1).sub h2).sub h3
  convert hh using 1 <;> (try funext s) <;>
    (try dsimp [H,B2,B3,B4]) <;>
    (first | rfl | (field_simp [hn]; ring))
lemma cell_integral (z : ℂ) (hz : 0<z.re) :
    (∫ x : ℝ in 0..1, B4 (x:ℂ)/(4*(z+(x:ℂ))^4))=H z 1-H z 0 := by
  have hn (x : ℝ) (hx : x ∈ Icc 0 1) : z+(x:ℂ)≠0 := by
    have hp : 0<(z+(x:ℂ)).re := by simp only [add_re,ofReal_re]; linarith [hx.1]
    intro he
    simp [he] at hp
  have hnum : Continuous (fun x : ℝ => B4 (x:ℂ)) := by unfold B4; fun_prop
  have hden : Continuous (fun x : ℝ => 4*(z+(x:ℂ))^4) := by fun_prop
  have hcont : ContinuousOn (fun x : ℝ => B4 (x:ℂ)/(4*(z+(x:ℂ))^4)) (Icc 0 1) :=
    hnum.continuousOn.div hden.continuousOn
      (fun x hx => mul_ne_zero (by norm_num) (pow_ne_zero 4 (hn x hx)))
  have hi : IntervalIntegrable (fun x : ℝ => B4 (x:ℂ)/(4*(z+(x:ℂ))^4)) volume 0 1 :=
    (show ContinuousOn (fun x : ℝ => B4 (x:ℂ)/(4*(z+(x:ℂ))^4)) (uIcc 0 1) by
      simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using hcont).intervalIntegrable
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=fun x : ℝ => H z (x:ℂ)) _ hi
  intro x hx
  have hx' : x ∈ Icc (0:ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using hx
  have hp : 0<(z+(x:ℂ)).re := by simp only [add_re,ofReal_re]; linarith [hx'.1]
  exact (primitive_derivative z (x:ℂ) hp).comp_ofReal
noncomputable def L (z : ℂ) : ℂ :=
  (z-1/2)*Complex.log z-z+1/(12*z)-1/(360*z^3)
lemma stirling_cell_step (z : ℂ) (hz : 0<z.re) :
    L (z+1)-L z-Complex.log z=
      -(∫ x : ℝ in 0..1, B4 (x:ℂ)/(4*(z+(x:ℂ))^4)) := by
  have hn : z≠0 := fun h => by simp [h] at hz
  have hn1 : z+1≠0 := by
    intro he
    have hi := congrArg Complex.re he
    simp only [add_re,one_re,zero_re] at hi
    linarith
  rw [cell_integral z hz]
  dsimp [L,H,B2,B3,B4]
  norm_num
  field_simp [hn,hn1]
  ring
noncomputable def Icell (z : ℂ) : ℂ :=
  ∫ x : ℝ in 0..1, B4 (x:ℂ)/(4*(z+(x:ℂ))^4)
lemma finite_log_sum (z : ℂ) (hz : 0<z.re) (N : Nat) :
    (∑ k ∈ Finset.range N, Complex.log (z+(k:ℂ)))=
      L (z+(N:ℂ))-L z+∑ k ∈ Finset.range N, Icell (z+(k:ℂ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hp : 0<(z+(N:ℂ)).re := by
      simp only [add_re,natCast_re]
      linarith [Nat.cast_nonneg (α:=ℝ) N]
    have hs := stirling_cell_step (z+(N:ℂ)) hp
    change L ((z+(N:ℂ))+1)-L (z+(N:ℂ))-Complex.log (z+(N:ℂ))=-Icell (z+(N:ℂ)) at hs
    have he : z+((N+1:Nat):ℂ)=(z+(N:ℂ))+1 := by push_cast; ring
    rw [Finset.sum_range_succ,Finset.sum_range_succ,ih,he]
    linear_combination -hs
lemma bernoulli_four_bound {x : ℝ} (hx : x ∈ Icc 0 1) : ‖B4 (x:ℂ)‖≤1/30 := by
  let y := x*(1-x)
  have hy : 0≤y := mul_nonneg hx.1 (by linarith [hx.2])
  have hy1 : y≤1/4 := by dsimp [y]; nlinarith [sq_nonneg (x-1/2)]
  have hy2 : y^2≤(1/4:ℝ)^2 := by gcongr
  have he : B4 (x:ℂ)=((y^2-1/30:ℝ):ℂ) := by
    dsimp [B4,y]
    push_cast
    ring
  rw [he,Complex.norm_real,Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg y]
lemma cell_norm_le (z : ℂ) (hb : 0<z.im) : ‖Icell z‖≤1/(120*z.im^4) := by
  have hpoint : ∀ x ∈ Set.uIoc (0:ℝ) 1,
      ‖B4 (x:ℂ)/(4*(z+(x:ℂ))^4)‖≤1/(120*z.im^4) := by
    intro x hx
    have hx' : x ∈ Icc (0:ℝ) 1 := by
      simp only [uIoc_of_le (by norm_num : (0:ℝ)≤1)] at hx
      exact ⟨hx.1.le,hx.2⟩
    have hn : z.im≤‖z+(x:ℂ)‖ := by
      simpa only [add_im,ofReal_im,add_zero,abs_of_pos hb] using Complex.abs_im_le_norm (z+(x:ℂ))
    calc
      _ = ‖B4 (x:ℂ)‖/(4*‖z+(x:ℂ)‖^4) := by
        rw [norm_div,norm_mul,norm_pow]
        norm_num
      _ ≤ (1/30)/(4*z.im^4) := by
        gcongr
        exact bernoulli_four_bound hx'
      _ = _ := by ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  simpa [Icell] using hi
lemma cell_norm_le_nat (z : ℂ) (hz : 0<z.re) (k : Nat) (hk : 0<k) :
    ‖Icell (z+(k:ℂ))‖≤1/(120*(k:ℝ)^4) := by
  have hk' : 0<(k:ℝ) := by exact_mod_cast hk
  have hpoint : ∀ x ∈ Set.uIoc (0:ℝ) 1,
      ‖B4 (x:ℂ)/(4*((z+(k:ℂ))+(x:ℂ))^4)‖≤1/(120*(k:ℝ)^4) := by
    intro x hx
    have hx' : x ∈ Icc (0:ℝ) 1 := by
      simp only [uIoc_of_le (by norm_num : (0:ℝ)≤1)] at hx
      exact ⟨hx.1.le,hx.2⟩
    have hr : (k:ℝ)≤((z+(k:ℂ))+(x:ℂ)).re := by
      simp only [add_re,natCast_re,ofReal_re]
      linarith [hx'.1]
    have hn := hr.trans (Complex.re_le_norm _)
    calc
      _ = ‖B4 (x:ℂ)‖/(4*‖(z+(k:ℂ))+(x:ℂ)‖^4) := by
        rw [norm_div,norm_mul,norm_pow]
        norm_num
      _ ≤ (1/30)/(4*(k:ℝ)^4) := by gcongr; exact bernoulli_four_bound hx'
      _ = _ := by ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  simpa [Icell] using hi
lemma reciprocal_four_step (x : ℝ) (hx : 0<x) :
    1/(x+1)^4≤1/(3*x^3)-1/(3*(x+1)^3) := by
  have hx1 : 0<x+1 := by linarith
  have hp : 0<3*x^3*(x+1)^4 := by positivity
  apply (mul_le_mul_iff_left₀ hp).mp
  field_simp [hx.ne',hx1.ne']
  nlinarith [sq_nonneg x]
lemma shifted_four_sum (x : ℝ) (hx : 0<x) (M : Nat) :
    (∑ k ∈ Finset.range M, 1/(x+(k:ℝ)+1)^4)≤
      1/(3*x^3)-1/(3*(x+(M:ℝ))^3) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hp : 0<x+(M:ℝ) := by positivity
    have ht := reciprocal_four_step (x+(M:ℝ)) hp
    rw [Finset.sum_range_succ]
    have h := add_le_add ih ht
    calc
      _ ≤ (1/(3*x^3)-1/(3*(x+(M:ℝ))^3))+
          (1/(3*(x+(M:ℝ))^3)-1/(3*(x+(M:ℝ)+1)^3)) := h
      _ = _ := by push_cast; ring
lemma four_tail_sum (x : ℝ) (hx : 0<x) (M : Nat) :
    (∑ k ∈ Finset.range M, 1/(x+(k:ℝ))^4)≤1/x^4+1/(3*x^3) := by
  cases M with
  | zero => simp; positivity
  | succ M =>
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero,add_zero,Nat.cast_add,Nat.cast_one]
    have hs := shifted_four_sum x hx M
    have hp : 0≤1/(3*(x+(M:ℝ))^3) := by positivity
    have hsum : (∑ k ∈ Finset.range M, 1/(x+((k:ℝ)+1))^4)≤1/(3*x^3) := by
      simpa only [add_assoc] using hs.trans (sub_le_self _ hp)
    linarith
lemma finite_cell_norm_sum (z : ℂ) (hz : 0<z.re) (hb : 1≤z.im) (M : Nat) :
    (∑ k ∈ Finset.range M, ‖Icell (z+(k:ℂ))‖)≤1/(36*z.im^3) := by
  let b := z.im
  let N := Nat.ceil b
  have hb0 : 0<b := by dsimp [b]; linarith
  have hNlo : b≤(N:ℝ) := Nat.le_ceil b
  have hNhi : (N:ℝ)≤2*b := by
    have h := Nat.ceil_lt_add_one hb0.le
    dsimp [N]
    linarith
  have hN1 : 1≤N := Nat.one_le_ceil_iff.mpr hb0
  have hNp : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hh : (∑ k ∈ Finset.range N, ‖Icell (z+(k:ℂ))‖)≤1/(60*b^3) := by
    calc
      _ ≤ ∑ k ∈ Finset.range N, 1/(120*b^4) := by
        apply Finset.sum_le_sum
        intro k hk
        simpa [b] using cell_norm_le (z+(k:ℂ)) (by simpa using hb0)
      _ = (N:ℝ)/(120*b^4) := by simp; ring
      _ ≤ (2*b)/(120*b^4) := by gcongr
      _ = 1/(60*b^3) := by field_simp; ring
  by_cases hMN : M≤N
  · calc
      _ ≤ ∑ k ∈ Finset.range M, 1/(120*b^4) := by
        apply Finset.sum_le_sum
        intro k hk
        simpa [b] using cell_norm_le (z+(k:ℂ)) (by simpa using hb0)
      _ = (M:ℝ)/(120*b^4) := by simp; ring
      _ ≤ (2*b)/(120*b^4) := by
        have hm' : (M:ℝ)≤(N:ℝ) := by exact_mod_cast hMN
        have hm'' := hm'.trans hNhi
        gcongr
      _ = 1/(60*b^3) := by field_simp; ring
      _ ≤ 1/(36*b^3) := by gcongr <;> norm_num
  · have hNM : N≤M := by omega
    have hm : M=N+(M-N) := by omega
    rw [hm,Finset.sum_range_add]
    have ht : (∑ k ∈ Finset.range (M-N), ‖Icell (z+((N+k:Nat):ℂ))‖)≤1/(90*b^3) := by
      calc
        _ ≤ ∑ k ∈ Finset.range (M-N), 1/(120*((N+k:Nat):ℝ)^4) := by
          apply Finset.sum_le_sum
          intro k hk
          exact cell_norm_le_nat z hz (N+k) (by omega)
        _ = (1/120)*∑ k ∈ Finset.range (M-N), 1/((N:ℝ)+(k:ℝ))^4 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          push_cast
          have hp : 0<(N:ℝ)+(k:ℝ) := by positivity
          field_simp [hp.ne'] <;> ring
        _ ≤ (1/120)*(1/(N:ℝ)^4+1/(3*(N:ℝ)^3)) :=
          mul_le_mul_of_nonneg_left (four_tail_sum (N:ℝ) hNp (M-N)) (by norm_num)
        _ ≤ (1/120)*(1/b^4+1/(3*b^3)) := by gcongr
        _ ≤ (1/120)*(1/b^3+1/(3*b^3)) := by
          gcongr <;> norm_num
        _ = 1/(90*b^3) := by ring
    have h := add_le_add hh ht
    have he : 1/(60*b^3)+1/(90*b^3)=1/(36*b^3) := by ring
    simpa only [he,b] using h
noncomputable def Remainder (z : ℂ) : ℂ := ∑' k : Nat, Icell (z+(k:ℂ))
lemma remainder_summable (z : ℂ) (hz : 0<z.re) (hb : 1≤z.im) :
    Summable (fun k : Nat => Icell (z+(k:ℂ))) := by
  have hn : Summable (fun k : Nat => ‖Icell (z+(k:ℂ))‖) :=
    summable_of_sum_range_le (fun k => norm_nonneg _) (finite_cell_norm_sum z hz hb)
  exact hn.of_norm
lemma remainder_norm_le (z : ℂ) (hz : 0<z.re) (hb : 1≤z.im) :
    ‖Remainder z‖≤1/(36*z.im^3) := by
  have hn : Summable (fun k : Nat => ‖Icell (z+(k:ℂ))‖) :=
    summable_of_sum_range_le (fun k => norm_nonneg _) (finite_cell_norm_sum z hz hb)
  exact (norm_tsum_le_tsum_norm hn).trans
    (Real.tsum_le_of_sum_range_le (fun k => norm_nonneg _) (finite_cell_norm_sum z hz hb))
lemma finite_product (z : ℂ) (hz : 0<z.re) (N : Nat) :
    (∏ k ∈ Finset.range N, (z+(k:ℂ)))=
      Complex.exp (L (z+(N:ℂ))-L z+∑ k ∈ Finset.range N, Icell (z+(k:ℂ))) := by
  rw [←finite_log_sum z hz N,Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro k hk
  have hp : 0<(z+(k:ℂ)).re := by
    simp only [add_re,natCast_re]
    linarith [Nat.cast_nonneg (α:=ℝ) k]
  have hn : z+(k:ℂ)≠0 := fun h => by simp [h] at hp
  exact (Complex.exp_log hn).symm
end RHHighStirling
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex Filter Set
open scoped Topology
namespace RHHighStirling
lemma log_one_ratio :
    Tendsto (fun w : ℂ => Complex.log (1+w)/w) (𝓝[≠] 0) (𝓝 1) := by
  have hd : HasDerivAt (fun w : ℂ => Complex.log (1+w)) 1 0 := by
    have hl : HasDerivAt Complex.log 1 (1+(0:ℂ)) := by
      simpa using Complex.hasDerivAt_log Complex.one_mem_slitPlane
    convert! hl.comp (0 : ℂ) ((hasDerivAt_id (0:ℂ)).const_add 1) using 1 <;> simp [Function.comp_def]
  simpa [smul_eq_mul,div_eq_mul_inv,mul_comm] using hd.tendsto_slope_zero
lemma scaled_log_limit (z : ℂ) (hz : 0<z.re) :
    Tendsto (fun n : Nat => ((n:ℂ)+z+1/2)*Complex.log (1+(z+1)/(n:ℂ)))
      atTop (𝓝 (z+1)) := by
  have hz1 : z+1≠0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [add_re,one_re,zero_re] at hr
    linarith
  let w : Nat → ℂ := fun n => (z+1)/(n:ℂ)
  have hw : Tendsto w atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat (z+1)
  have hne : ∀ᶠ n in atTop, w n ∈ ({(0:ℂ)}:Set ℂ)ᶜ := by
    filter_upwards [eventually_ge_atTop (1:Nat)] with n hn
    have hn0 : (n:ℂ)≠0 := by exact_mod_cast (show n≠0 by omega)
    exact div_ne_zero hz1 hn0
  have hww : Tendsto w atTop (𝓝[≠] 0) := tendsto_nhdsWithin_iff.mpr ⟨hw,hne⟩
  have hr := log_one_ratio.comp hww
  have hc : Tendsto (fun n : Nat => (z+1)+(z+1)*(z+1/2)/(n:ℂ)) atTop (𝓝 (z+1)) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat ((z+1)*(z+1/2)))
  have hp := hc.mul hr
  have he : ∀ᶠ (n : Nat) in atTop,
      ((z+1)+(z+1)*(z+1/2)/(n:ℂ))*(Complex.log (1+w n)/w n)=
      ((n:ℂ)+z+1/2)*Complex.log (1+(z+1)/(n:ℂ)) := by
    filter_upwards [eventually_ge_atTop (1:Nat)] with n hn
    have hn0 : (n:ℂ)≠0 := by exact_mod_cast (show n≠0 by omega)
    dsimp [w]
    field_simp [hz1,hn0]
    ring
  simpa using hp.congr' he
end RHHighStirling
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex Filter Set
open scoped Topology
namespace RHHighStirling
noncomputable def D (z : ℂ) (n : Nat) : ℂ :=
  z+1-((n:ℂ)+z+1/2)*Complex.log (1+(z+1)/(n:ℂ))
    -1/(12*(z+(n:ℂ)+1))+1/(360*(z+(n:ℂ)+1)^3)
lemma shifted_reciprocal_limit (z : ℂ) :
    Tendsto (fun n : Nat => 1/(z+(n:ℂ)+1)) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : Nat => 1/(n:ℂ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hw : Tendsto (fun n : Nat => 1+(z+1)/(n:ℂ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (z+1))
  have h := hn.div hw (by norm_num)
  have he : ∀ᶠ (n : Nat) in atTop,
      (1/(n:ℂ))/(1+(z+1)/(n:ℂ))=1/(z+(n:ℂ)+1) := by
    filter_upwards [eventually_ge_atTop (1:Nat)] with n hnn
    have hn0 : (n:ℂ)≠0 := by exact_mod_cast (show n≠0 by omega)
    field_simp [hn0]
    <;> ring
  simpa using h.congr' he
lemma D_limit (z : ℂ) (hz : 0<z.re) : Tendsto (D z) atTop (𝓝 0) := by
  have hc : Tendsto (fun _ : Nat => z+1) atTop (𝓝 (z+1)) := tendsto_const_nhds
  have h1 := hc.sub (scaled_log_limit z hz)
  have h2 := (shifted_reciprocal_limit z).const_mul (1/12:ℂ)
  have h3 := ((shifted_reciprocal_limit z).pow 3).const_mul (1/360:ℂ)
  have he (n : Nat) : D z n = (z+1-((n:ℂ)+z+1/2)*Complex.log (1+(z+1)/(n:ℂ)))
      -(1/12:ℂ)*(1/(z+(n:ℂ)+1))+(1/360:ℂ)*(1/(z+(n:ℂ)+1))^3 := by
    dsimp [D]
    simp only [div_mul_eq_div_mul_one_div,div_pow]
    ring
  change Tendsto (fun n : Nat => D z n) atTop (𝓝 0)
  simp_rw [he]
  simpa using (h1.sub h2).add h3
lemma stirling_pos (n : Nat) (hn : 0<n) : 0<Stirling.stirlingSeq n := by
  unfold Stirling.stirlingSeq
  positivity
lemma sqrt_exp (x : ℝ) (hx : 0<x) : Real.sqrt x = Real.exp (Real.log x/2) := by
  rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos hx]
  congr 1
  ring
lemma log_shift (z : ℂ) (hz : 0<z.re) (n : Nat) (hn : 0<n) :
    Complex.log (z+(n:ℂ)+1)=(Real.log (n:ℝ):ℂ)+Complex.log (1+(z+1)/(n:ℂ)) := by
  have hn0 : (n:ℂ)≠0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
  have hp : 0<(z+(n:ℂ)+1).re := by
    simp only [add_re,one_re,natCast_re]
    positivity
  have hw : 1+(z+1)/(n:ℂ)≠0 := by
    intro h
    have he : (n:ℂ)*(1+(z+1)/(n:ℂ))=z+(n:ℂ)+1 := by field_simp;ring
    rw [h,mul_zero] at he
    simp [←he] at hp
  rw [←Complex.log_ofReal_mul (show 0<(n:ℝ) by exact_mod_cast hn) hw]
  congr 1
  push_cast
  field_simp
  ring
lemma prefactor_eq (z : ℂ) (hz : 0<z.re) (n : Nat) (hn : 0<n) :
    (n:ℂ)^z*(n.factorial:ℂ)*Complex.exp (-L (z+((n+1:Nat):ℂ)))=
      (Real.sqrt 2:ℂ)*(Stirling.stirlingSeq n:ℂ)*Complex.exp (D z n) := by
  have hnR : 0<(n:ℝ) := by exact_mod_cast hn
  have hn0 : (n:ℂ)≠0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
  have hfR : 0<(n.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hs := stirling_pos n hn
  have hl := congrArg (fun x : ℝ => (x:ℂ)) (Stirling.log_stirlingSeq_formula n)
  push_cast at hl
  have hlog2 : Real.log (2*(n:ℝ))=Real.log 2+Real.log (n:ℝ) :=
    Real.log_mul (by norm_num) hnR.ne'
  have hlogdiv : Real.log ((n:ℝ)/Real.exp 1)=Real.log (n:ℝ)-1 := by
    rw [Real.log_div hnR.ne' (Real.exp_pos 1).ne',Real.log_exp]
  rw [hlog2,hlogdiv] at hl
  push_cast at hl
  rw [Complex.cpow_def_of_ne_zero hn0]
  have hfac : (n.factorial:ℂ)=Complex.exp (Real.log (n.factorial:ℝ):ℂ) := by
    rw [←Complex.ofReal_exp,Real.exp_log hfR]
    norm_cast
  have hsq : (Real.sqrt 2:ℂ)=Complex.exp ((Real.log 2:ℂ)/2) := by
    rw [sqrt_exp 2 (by norm_num),Complex.ofReal_exp]
    congr 1
    push_cast
    rfl
  have hst : (Stirling.stirlingSeq n:ℂ)=Complex.exp (Real.log (Stirling.stirlingSeq n):ℂ) := by
    rw [←Complex.ofReal_exp,Real.exp_log hs]
  rw [hfac,hsq,hst,←Complex.exp_add,←Complex.exp_add,←Complex.exp_add,←Complex.exp_add]
  congr 1
  rw [Complex.natCast_log,hl]
  unfold L D
  push_cast
  simp only [←add_assoc]
  rw [log_shift z hz n hn]
  push_cast
  ring
end RHHighStirling
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex Filter Set
open scoped Topology
namespace RHHighStirling
lemma gamma_seq_factor (z : ℂ) (hz : 0<z.re) (n : Nat) (hn : 0<n) :
    Complex.GammaSeq z n =
      (Real.sqrt 2:ℂ)*(Stirling.stirlingSeq n:ℂ)*Complex.exp (D z n)*
        Complex.exp (L z-∑ k ∈ Finset.range (n+1), Icell (z+(k:ℂ))) := by
  rw [←prefactor_eq z hz n hn,Complex.GammaSeq,finite_product z hz (n+1)]
  rw [div_eq_mul_inv,←Complex.exp_neg]
  have he : -(L (z+((n+1:Nat):ℂ))-L z+∑ k ∈ Finset.range (n+1), Icell (z+(k:ℂ)))=
      -L (z+((n+1:Nat):ℂ))+(L z-∑ k ∈ Finset.range (n+1), Icell (z+(k:ℂ))) := by ring
  rw [he,Complex.exp_add]
  ring
lemma Gamma_eq_stirling_remainder (z : ℂ) (hz : 0<z.re) (hb : 1≤z.im) :
    Complex.Gamma z=(Real.sqrt (2*Real.pi):ℂ)*Complex.exp (L z-Remainder z) := by
  have hs := Stirling.tendsto_stirlingSeq_sqrt_pi.ofReal
  have hd := (D_limit z hz).cexp
  have hsum : Tendsto (fun n : Nat => ∑ k ∈ Finset.range (n+1), Icell (z+(k:ℂ)))
      atTop (𝓝 (Remainder z)) :=
    (remainder_summable z hz hb).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hc : Tendsto (fun _ : Nat => L z) atTop (𝓝 (L z)) := tendsto_const_nhds
  have hr := (hc.sub hsum).cexp
  have hconst : Tendsto (fun _ : Nat => (Real.sqrt 2:ℂ)) atTop (𝓝 (Real.sqrt 2:ℂ)) := tendsto_const_nhds
  have hf := (((hconst.mul hs).mul hd).mul hr)
  have hft : Tendsto (Complex.GammaSeq z) atTop
      (𝓝 ((Real.sqrt 2:ℂ)*(Real.sqrt Real.pi:ℂ)*Complex.exp (L z-Remainder z))) := by
    have he : ∀ᶠ (n : Nat) in atTop,
        (Real.sqrt 2:ℂ)*(Stirling.stirlingSeq n:ℂ)*Complex.exp (D z n)*
          Complex.exp (L z-∑ k ∈ Finset.range (n+1), Icell (z+(k:ℂ)))=Complex.GammaSeq z n := by
      filter_upwards [eventually_ge_atTop (1:Nat)] with n hn
      exact (gamma_seq_factor z hz n (by omega)).symm
    simpa using hf.congr' he
  have he := tendsto_nhds_unique (Complex.GammaSeq_tendsto_Gamma z) hft
  rw [←Complex.ofReal_mul,←Real.sqrt_mul (by norm_num : (0:ℝ)≤2)] at he
  exact he
noncomputable def L0 (z : ℂ) : ℂ :=
  (z-1/2)*Complex.log z-z+(Real.log (2*Real.pi):ℂ)/2+1/(12*z)
noncomputable def rho (z : ℂ) : ℂ := -1/(360*z^3)-Remainder z
lemma rho_norm (z : ℂ) (hz : 0<z.re) (hb : 1≤z.im) :
    ‖rho z‖≤1/z.im^3 := by
  have hb0 : 0<z.im := by linarith
  have hzn : z.im≤‖z‖ := (le_abs_self z.im).trans (Complex.abs_im_le_norm z)
  have hzp : 0<‖z‖ := hb0.trans_le hzn
  have hi : ‖(1:ℂ)/(360*z^3)‖≤1/(360*z.im^3) := by
    rw [norm_div,norm_mul,norm_pow]
    norm_num
    gcongr
  have hr := remainder_norm_le z hz hb
  calc
    ‖rho z‖ = ‖-((1:ℂ)/(360*z^3))-Remainder z‖ := by
      congr 1
      unfold rho
      ring
    _ ≤ ‖-((1:ℂ)/(360*z^3))‖+‖Remainder z‖ := norm_sub_le _ _
    _ = ‖(1:ℂ)/(360*z^3)‖+‖Remainder z‖ := by rw [norm_neg]
    _ ≤ 1/(360*z.im^3)+1/(36*z.im^3) := add_le_add hi hr
    _ ≤ 1/z.im^3 := by field_simp; nlinarith [pow_pos hb0 3]
lemma Gamma_eq_approx (z : ℂ) (hz : 0<z.re) (hb : 1≤z.im) :
    Complex.Gamma z=Complex.exp (L0 z+rho z) := by
  rw [Gamma_eq_stirling_remainder z hz hb]
  have hp : 0<2*Real.pi := by positivity
  have hs : (Real.sqrt (2*Real.pi):ℂ)=Complex.exp ((Real.log (2*Real.pi):ℂ)/2) := by
    rw [sqrt_exp _ hp,Complex.ofReal_exp]
    congr 1
    push_cast
    rfl
  rw [hs,←Complex.exp_add]
  congr 1
  unfold L L0 rho
  ring
lemma Gamma_approx_error (z : ℂ) (hz : 0<z.re) (hb : 1≤z.im) :
    ‖Complex.Gamma z-Complex.exp (L0 z)‖≤2*‖Complex.Gamma z‖/z.im^3 := by
  have hr := rho_norm z hz hb
  have hsmall : ‖-rho z‖≤1 := by
    rw [norm_neg]
    apply hr.trans
    have hp : 1≤z.im^3 := one_le_pow₀ hb
    exact (div_le_one (by positivity)).mpr hp
  have he : Complex.Gamma z-Complex.exp (L0 z)=
      Complex.Gamma z*(1-Complex.exp (-rho z)) := by
    rw [Gamma_eq_approx z hz hb]
    rw [mul_sub, mul_one,←Complex.exp_add]
    congr 1
    congr 1
    ring
  rw [he,norm_mul]
  calc
    ‖Complex.Gamma z‖*‖1-Complex.exp (-rho z)‖ ≤ ‖Complex.Gamma z‖*(2*‖rho z‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [norm_sub_rev,norm_neg] using Complex.norm_exp_sub_one_le hsmall
    _ ≤ ‖Complex.Gamma z‖*(2*(1/z.im^3)) := by gcongr
    _ = 2*‖Complex.Gamma z‖/z.im^3 := by ring
end RHHighStirling

theorem solution :
  (∀ (z : ℂ), 0<z.re → 1≤z.im →
    ∃ ρ : ℂ, ‖ρ‖≤1/z.im^3 ∧
      Complex.Gamma z=Complex.exp ((z-1/2)*Complex.log z-z+(Real.log (2*Real.pi):ℂ)/2+1/(12*z)+ρ)) ∧
  (∀ (z : ℂ), 0<z.re → 1≤z.im →
    ‖Complex.Gamma z-Complex.exp ((z-1/2)*Complex.log z-z+(Real.log (2*Real.pi):ℂ)/2+1/(12*z))‖≤2*‖Complex.Gamma z‖/z.im^3) := by
  constructor
  · intro z hz hb
    exact ⟨RHHighStirling.rho z, RHHighStirling.rho_norm z hz hb,
      RHHighStirling.Gamma_eq_approx z hz hb⟩
  · intro z hz hb
    exact RHHighStirling.Gamma_approx_error z hz hb
