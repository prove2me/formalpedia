-- Prove2me | solution 1 for TaoFivePrimes.schoenfeld_psi_error_middle_of_rh_million
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T17:10:11.499991+00:00
-- url     : https://prove2.me/submissions/58a480d4-4cf0-48bd-913a-7e366b2319ef

import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_PowerQuarterWeights
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_NumericalLowZeroReciprocal
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_ShiftedLogarithmicTail
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_SharpNumericalZeroTail
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_NumericalZeroTail
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_ImprovedRegion

set_option autoImplicit false
set_option maxHeartbeats 2000000
open DusartSmoothing Complex Set

private def H : ℝ := 1000000

private lemma high_reciprocal_num :
    (2 * Real.log (H / (2 * Real.pi)) + 1) / (8 * Real.pi * H^2) +
      (18 * Real.log H + 179) / H^3 ≤ (114/10^14:ℝ) := by
  have hl := ExplicitPNT.DusartTable1.Modules.NumericalZeroTail.1 H 14
    (by norm_num [H]) (by norm_num [H])
  have hb := ExplicitPNT.DusartTable1.Modules.SharpNumericalZeroTail.2.1 H 14
    (by norm_num [H]) (by norm_num) (by simpa using hl)
  apply hb.trans
  norm_num [H]

private lemma low_absolute_weight (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ)
    (hγ : ∀ ρ ∈ Z, |ρ.im| ≤ H) :
    (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * (1 / |ρ.im|)) ≤ 40 := by
  classical
  let W : ℝ → ℝ := fun t => if t ≤ H then 1/t else 0
  have hpos (S : Finset ℂ) (hS : ∀ ρ ∈ S, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im) :
      (∑ ρ ∈ S, (RvM.zeroMult ρ : ℝ) * W ρ.im) ≤ 20 := by
    let F := S.filter (fun ρ => ρ.im ≤ H)
    have hF : ∀ ρ ∈ F, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im := by
      intro ρ hρ
      exact hS ρ (Finset.mem_filter.mp hρ).1
    have hγF : ∀ ρ ∈ F, ρ.im ≤ (566245491/500:ℝ) := by
      intro ρ hρ
      have h := (Finset.mem_filter.mp hρ).2
      dsimp [H] at h
      linarith
    have hh := ExplicitPNT.DusartTable1.Modules.NumericalLowZeroReciprocal.2.1 F hF hγF
    simpa only [F, W, Finset.sum_filter, mul_ite, mul_zero] using hh
  have hh := ExplicitPNT.DusartTable1.Modules.PowerQuarterWeights.1 W 20 hpos Z hZ
  have he : (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * W |ρ.im|) =
      ∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * (1 / |ρ.im|) := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    simp only [W, if_pos (hγ ρ hρ)]
  rw [he] at hh
  norm_num at hh ⊢
  exact hh

private lemma high_absolute_weight (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ)
    (hγ : ∀ ρ ∈ Z, H < |ρ.im|) :
    (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * (1 / |ρ.im|^3)) ≤ 228 / 10^14 := by
  classical
  let W : ℝ → ℝ := fun t => if H < t then 1/t^3 else 0
  have hpos (S : Finset ℂ) (hS : ∀ ρ ∈ S, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im) :
      (∑ ρ ∈ S, (RvM.zeroMult ρ : ℝ) * W ρ.im) ≤ (114/10^14:ℝ) := by
    let F := S.filter (fun ρ => H < ρ.im)
    have hF : ∀ ρ ∈ F, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im := by
      intro ρ hρ
      exact hS ρ (Finset.mem_filter.mp hρ).1
    have hh := ExplicitPNT.DusartTable1.Modules.ShiftedLogarithmicTail.2 F hF H
      (by norm_num [H]) (fun ρ hρ => (Finset.mem_filter.mp hρ).2)
    have hb := hh.trans high_reciprocal_num
    simpa only [F, W, Finset.sum_filter, mul_ite, mul_zero] using hb
  have hh := ExplicitPNT.DusartTable1.Modules.PowerQuarterWeights.1 W
    (114/10^14:ℝ) hpos Z hZ
  have he : (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * W |ρ.im|) =
      ∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * (1 / |ρ.im|^3) := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    simp only [W, if_pos (hγ ρ hρ)]
  rw [he] at hh
  nlinarith only [hh]

private lemma low_zero_on_line (ρ : ℂ) (hρ : RvM.IsNontrivialZero ρ)
    (hγ : |ρ.im| ≤ H)
    (hRH : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      0 ≤ s.im → s.im ≤ H → s.re = 1/2) :
    ρ.re = 1/2 := by
  by_cases hi : 0 ≤ ρ.im
  · exact hRH ρ hρ.1 hρ.2.1 hρ.2.2 hi ((le_abs_self _).trans hγ)
  · have hneg : ρ.im < 0 := lt_of_not_ge hi
    have hz : riemannZeta (starRingEnd ℂ ρ) = 0 := by
      rw [riemannZeta_conj, hρ.1, map_zero]
    have hh := hRH (starRingEnd ℂ ρ) hz (by simpa using hρ.2.1)
      (by simpa using hρ.2.2) (by simpa using neg_nonneg.mpr hneg.le)
      (by simpa [Complex.conj_im, abs_of_neg hneg] using hγ)
    simpa using hh

private lemma smoothed_zero_norm_split (a h z : ℝ) (ha : 1 ≤ a) (hh : 0 < h)
    (haz : a + 2*h ≤ z)
    (hRH : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      0 ≤ s.im → s.im ≤ H → s.re = 1/2) :
    (∑' ρ : NontrivialZetaZero,
      ‖(RvM.zeroMult ρ.val : ℂ) * smoothedZeroKernel a h ρ.val‖) ≤
      40 * Real.sqrt z + (4*z^(23/8:ℝ)/h^2) * (228 / 10^14 : ℝ) := by
  classical
  have hz : 0 < z := by linarith
  have hterm_low (ρ : NontrivialZetaZero) (hγ : |ρ.val.im| ≤ H) :
      ‖(RvM.zeroMult ρ.val : ℂ) * smoothedZeroKernel a h ρ.val‖ ≤
        Real.sqrt z * ((RvM.zeroMult ρ.val : ℝ) * (1 / |ρ.val.im|)) := by
    have hρ := ρ.property
    have hβ := low_zero_on_line ρ.val hρ hγ hRH
    have hi : 0 < |ρ.val.im| := by
      have hv := RvM.nontrivial_zero_abs_height ρ.val hρ
      linarith [Real.pi_pos]
    have hp (y : ℝ) (hy : y ∈ Set.Icc a (a + 2*h)) :
        ‖(y : ℂ)^ρ.val‖ ≤ Real.sqrt z := by
      have hy0 : 0 < y := by linarith [hy.1]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hy0, hβ, ←Real.sqrt_eq_rpow]
      exact Real.sqrt_le_sqrt (hy.2.trans haz)
    have hk := norm_smoothedZeroKernel_low a h (Real.sqrt z) hh (Real.sqrt_nonneg z)
      ρ.val hρ.2.1 hi hp
    rw [norm_mul, Complex.norm_natCast]
    have hm := mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg (RvM.zeroMult ρ.val))
    simpa only [div_eq_mul_inv, one_mul, mul_assoc, mul_left_comm, mul_comm] using hm
  have hterm_high (ρ : NontrivialZetaZero) (hγ : H < |ρ.val.im|) :
      ‖(RvM.zeroMult ρ.val : ℂ) * smoothedZeroKernel a h ρ.val‖ ≤
        (4*z^(23/8:ℝ)/h^2) * ((RvM.zeroMult ρ.val : ℝ) * (1 / |ρ.val.im|^3)) := by
    have hρ := ρ.property
    have hβ : ρ.val.re ≤ (7/8:ℝ) := by
      by_contra! hβ
      exact ExplicitPNT.DusartTable1.Modules.ImprovedRegion.1 ρ.val hβ hρ.1
    have hi : 0 < |ρ.val.im| := by dsimp [H] at hγ; linarith
    let M : ℝ := z^(7/8:ℝ)
    have hM : 0 ≤ M := Real.rpow_nonneg hz.le _
    have hp (y : ℝ) (hy : y ∈ Set.Icc a (a + 2*h)) : ‖(y : ℂ)^ρ.val‖ ≤ M := by
      have hy0 : 0 < y := by linarith [hy.1]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hy0]
      exact (Real.rpow_le_rpow_of_exponent_le (ha.trans hy.1) hβ).trans
        (Real.rpow_le_rpow hy0.le (hy.2.trans haz) (by norm_num))
    have hk := norm_smoothedZeroKernel_high a h M (by linarith) hh hM ρ.val hi hp
    have hpow : M*z^2 = z^(23/8:ℝ) := by
      dsimp [M]
      rw [←Real.rpow_two, ←Real.rpow_add hz]
      norm_num
    have hk' : ‖smoothedZeroKernel a h ρ.val‖ ≤
        (4*z^(23/8:ℝ)/h^2)*(1/|ρ.val.im|^3) := by
      calc
        _ ≤ 4*M*(a+2*h)^2/(h^2*|ρ.val.im|^3) := hk
        _ ≤ 4*M*z^2/(h^2*|ρ.val.im|^3) := by gcongr
        _ = (4*z^(23/8:ℝ)/h^2)*(1/|ρ.val.im|^3) := by rw [←hpow]; ring
    rw [norm_mul, Complex.norm_natCast]
    have hm := mul_le_mul_of_nonneg_left hk' (Nat.cast_nonneg (RvM.zeroMult ρ.val))
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hm
  apply Real.tsum_le_of_sum_le (fun ρ => norm_nonneg _)
  intro S
  let L := S.filter (fun ρ : NontrivialZetaZero => |ρ.val.im| ≤ H)
  let U := S.filter (fun ρ : NontrivialZetaZero => ¬|ρ.val.im| ≤ H)
  let ZL : Finset ℂ := L.image (fun ρ => ρ.val)
  let ZU : Finset ℂ := U.image (fun ρ => ρ.val)
  have hZL : ∀ ρ ∈ ZL, RvM.IsNontrivialZero ρ := by
    intro ρ hρ
    obtain ⟨τ, _, rfl⟩ := Finset.mem_image.mp hρ
    exact τ.property
  have hγL : ∀ ρ ∈ ZL, |ρ.im| ≤ H := by
    intro ρ hρ
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hρ
    exact (Finset.mem_filter.mp hτ).2
  have hZU : ∀ ρ ∈ ZU, RvM.IsNontrivialZero ρ := by
    intro ρ hρ
    obtain ⟨τ, _, rfl⟩ := Finset.mem_image.mp hρ
    exact τ.property
  have hγU : ∀ ρ ∈ ZU, H < |ρ.im| := by
    intro ρ hρ
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hρ
    exact lt_of_not_ge (Finset.mem_filter.mp hτ).2
  have hL := low_absolute_weight ZL hZL hγL
  dsimp [ZL] at hL
  rw [Finset.sum_image (fun a _ b _ he => Subtype.val_injective he)] at hL
  have hU := high_absolute_weight ZU hZU hγU
  dsimp [ZU] at hU
  rw [Finset.sum_image (fun a _ b _ he => Subtype.val_injective he)] at hU
  have hsumL : (∑ ρ ∈ L, ‖(RvM.zeroMult ρ.val : ℂ) * smoothedZeroKernel a h ρ.val‖) ≤
      Real.sqrt z * 40 := by
    calc
      _ ≤ ∑ ρ ∈ L, Real.sqrt z * ((RvM.zeroMult ρ.val : ℝ) * (1/|ρ.val.im|)) :=
        Finset.sum_le_sum (fun ρ hρ => hterm_low ρ (Finset.mem_filter.mp hρ).2)
      _ = Real.sqrt z * (∑ ρ ∈ L, (RvM.zeroMult ρ.val : ℝ) * (1/|ρ.val.im|)) := by rw [Finset.mul_sum]
      _ ≤ Real.sqrt z * 40 := mul_le_mul_of_nonneg_left hL (Real.sqrt_nonneg z)
  have hsumU : (∑ ρ ∈ U, ‖(RvM.zeroMult ρ.val : ℂ) * smoothedZeroKernel a h ρ.val‖) ≤
      (4*z^(23/8:ℝ)/h^2) * (228/10^14:ℝ) := by
    calc
      _ ≤ ∑ ρ ∈ U, (4*z^(23/8:ℝ)/h^2) * ((RvM.zeroMult ρ.val : ℝ) * (1/|ρ.val.im|^3)) :=
        Finset.sum_le_sum (fun ρ hρ => hterm_high ρ (lt_of_not_ge (Finset.mem_filter.mp hρ).2))
      _ = (4*z^(23/8:ℝ)/h^2) * (∑ ρ ∈ U, (RvM.zeroMult ρ.val : ℝ) * (1/|ρ.val.im|^3)) := by rw [Finset.mul_sum]
      _ ≤ (4*z^(23/8:ℝ)/h^2) * (228/10^14:ℝ) := mul_le_mul_of_nonneg_left hU (by positivity)
  have hsplit := Finset.sum_filter_add_sum_filter_not S
    (fun ρ : NontrivialZetaZero => |ρ.val.im| ≤ H)
    (fun ρ => ‖(RvM.zeroMult ρ.val : ℂ) * smoothedZeroKernel a h ρ.val‖)
  change (∑ ρ ∈ L, _) + (∑ ρ ∈ U, _) = _ at hsplit
  linarith only [hsumL, hsumU, hsplit]

private lemma double_average_split (a h z : ℝ) (ha : 1 ≤ a) (hh : 0 < h)
    (haz : a+2*h ≤ z)
    (hRH : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      0 ≤ s.im → s.im ≤ H → s.re = 1/2) :
    |doubleBoxAverage Chebyshev.psi a h - (a+h)| ≤
      2 + 40*Real.sqrt z + (4*z^(23/8:ℝ)/h^2)*(228/10^14:ℝ) + 512*z^(3/2:ℝ)/h^2 := by
  have hp := doubleBoxAverage_psi_error_zero_sum a h ha hh
  have hs := smoothed_zero_norm_split a h z ha hh haz hRH
  have hr : 512*(a+2*h)^(3/2:ℝ)/h^2 ≤ 512*z^(3/2:ℝ)/h^2 := by gcongr
  linarith only [hp,hs,hr]

private lemma exp_lower_23 : (9600000000:ℝ) ≤ Real.exp 23 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7182818283) Real.exp_one_gt_d9.le 23
  rw [←Real.exp_nat_mul] at hp
  norm_num at hp ⊢
  linarith

private lemma exp_lower_24 : (26000000000:ℝ) ≤ Real.exp 24 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7182818283) Real.exp_one_gt_d9.le 24
  rw [←Real.exp_nat_mul] at hp
  norm_num at hp ⊢
  linarith

private lemma exp_lower_30 : (10000000000000:ℝ) ≤ Real.exp 30 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7182818283) Real.exp_one_gt_d9.le 30
  rw [←Real.exp_nat_mul] at hp
  norm_num at hp ⊢
  linarith

private lemma psi_error_rh_smoothed (y : ℝ) (hy : (9600000000:ℝ) ≤ y)
    (hRH : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      0 ≤ s.im → s.im ≤ H → s.re = 1/2) :
    |Chebyshev.psi y - y| ≤ 2 + (4001/100:ℝ)*Real.sqrt y +
      (154/10^6:ℝ)*y + (513*10^8:ℝ)/Real.sqrt y := by
  have hypos : 0 < y := by linarith
  let h : ℝ := y/10000
  let z : ℝ := (5001/5000:ℝ)*y
  have hh : 0 < h := by dsimp [h]; positivity
  have hz : 0 < z := by dsimp [z]; positivity
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hypos
  have hs2 : (Real.sqrt y)^2 = y := Real.sq_sqrt hypos.le
  have hz2 : (Real.sqrt z)^2 = z := Real.sq_sqrt hz.le
  have hsqrtz : Real.sqrt z ≤ (10001/10000:ℝ)*Real.sqrt y := by
    have hz0 := Real.sqrt_nonneg z
    dsimp [z] at hz2
    nlinarith only [hz2,hs2,hz0,hs]
  have hlow : 40*Real.sqrt z ≤ (4001/100:ℝ)*Real.sqrt y := by
    nlinarith only [hsqrtz,hs]
  have hroot_eq : (z^(1/8:ℝ))^8 = z := by
    rw [←Real.rpow_natCast, ←Real.rpow_mul hz.le]
    norm_num
  have hroot17 : (17:ℝ) ≤ z^(1/8:ℝ) := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8:ℕ) ≠ 0) (Real.rpow_nonneg hz.le _)
    rw [hroot_eq]
    dsimp [z]
    nlinarith only [hy]
  have hroot3 : z^(23/8:ℝ)*z^(1/8:ℝ) = z^3 := by
    rw [←Real.rpow_add hz]
    norm_num [Real.rpow_natCast]
  have hpow : z^(23/8:ℝ) ≤ z^3/17 := by
    apply (le_div_iff₀ (by norm_num : (0:ℝ) < 17)).2
    have hm := mul_nonneg (Real.rpow_nonneg hz.le (23/8:ℝ))
      (sub_nonneg.2 hroot17)
    nlinarith only [hm,hroot3]
  have hhigh : (4*z^(23/8:ℝ)/h^2)*(228/10^14:ℝ) ≤ (54/10^6:ℝ)*y := by
    calc
      _ ≤ (4*(z^3/17)/h^2)*(228/10^14:ℝ) := by gcongr
      _ ≤ _ := by
        dsimp [h,z]
        have hyne : y ≠ 0 := ne_of_gt hypos
        field_simp
        nlinarith only [hypos]
  have hzpow : z^(3/2:ℝ) = z*Real.sqrt z := by
    rw [show (3/2:ℝ) = 1 + 1/2 by norm_num, Real.rpow_add hz, Real.rpow_one, ←Real.sqrt_eq_rpow]
  have hnum : 512*z*Real.sqrt z ≤ 513*y*Real.sqrt y := by
    have hm := mul_le_mul_of_nonneg_left hsqrtz (show (0:ℝ) ≤ 512*z by positivity)
    dsimp [z] at hm ⊢
    nlinarith only [hm,hypos,hs]
  have hrem0 : 512*z^(3/2:ℝ)/h^2 ≤ 513*y*Real.sqrt y/h^2 := by
    rw [hzpow]
    exact div_le_div_of_nonneg_right (by simpa only [mul_assoc] using hnum) (sq_nonneg h)
  have hid : 513*y*Real.sqrt y/h^2 = (513*10^8:ℝ)/Real.sqrt y := by
    dsimp [h]
    field_simp
    have hm := congrArg (fun u : ℝ => y*u) hs2
    nlinarith only [hm,hs2]
  rw [hid] at hrem0
  let E : ℝ := 2 + 40*Real.sqrt z + (4*z^(23/8:ℝ)/h^2)*(228/10^14:ℝ) +
    512*z^(3/2:ℝ)/h^2
  have hEt : E ≤ 2+(4001/100:ℝ)*Real.sqrt y+(54/10^6:ℝ)*y+(513*10^8:ℝ)/Real.sqrt y := by
    dsimp [E]
    linarith only [hlow,hhigh,hrem0]
  have hzlow : y-2*h+2*h ≤ z := by dsimp [z]; linarith
  have hzhigh : y+2*h ≤ z := by dsimp [h,z]; linarith
  have hposlow : 1 ≤ y-2*h := by dsimp [h]; linarith
  have hLo := double_average_split (y-2*h) h z hposlow hh hzlow hRH
  have hHi := double_average_split y h z (by linarith) hh hzhigh hRH
  have hc : y-2*h+h = y-h := by ring
  rw [hc] at hLo
  have hpsi := psi_error_of_double_average_errors y h E hh hLo hHi
  dsimp [h] at hpsi
  linarith only [hpsi,hEt]

private lemma budget_case1 (y : ℝ) (hy : (9600000000:ℝ) ≤ y) :
    2 + (4001/100:ℝ)*Real.sqrt y + (154/10^6:ℝ)*y +
      (513*10^8:ℝ)/Real.sqrt y ≤ y / 960 := by
  have hs : (97000:ℝ) ≤ Real.sqrt y := by
    have hh := Real.sqrt_le_sqrt (show (97000:ℝ)^2 ≤ y by nlinarith only [hy])
    norm_num at hh
    exact hh
  have hspos : 0 < Real.sqrt y := by linarith
  have hs2 : (Real.sqrt y)^2 = y := Real.sq_sqrt (by linarith)
  have hm := mul_nonneg (Real.sqrt_nonneg y) (show 0 ≤ Real.sqrt y - 97000 by linarith)
  have hl : (4001/100:ℝ)*Real.sqrt y ≤ (42/100000:ℝ)*y := by
    nlinarith only [hs2, hm]
  have hprod : (9600000000:ℝ)*97000 ≤ y*Real.sqrt y :=
    mul_le_mul hy hs (by norm_num) (by linarith)
  have hr : (513*10^8:ℝ)/Real.sqrt y ≤ (56/10^6:ℝ)*y := by
    apply (div_le_iff₀ hspos).2
    nlinarith only [hprod]
  have htwo : (2:ℝ) ≤ y / 10^9 := by nlinarith only [hy]
  linarith only [hl,hr,htwo,hy]

private lemma budget_case2 (y : ℝ) (hy : (26000000000:ℝ) ≤ y) :
    2 + (4001/100:ℝ)*Real.sqrt y + (154/10^6:ℝ)*y +
      (513*10^8:ℝ)/Real.sqrt y ≤ y / 1200 := by
  have hs : (160000:ℝ) ≤ Real.sqrt y := by
    have hh := Real.sqrt_le_sqrt (show (160000:ℝ)^2 ≤ y by nlinarith only [hy])
    norm_num at hh
    exact hh
  have hspos : 0 < Real.sqrt y := by linarith
  have hs2 : (Real.sqrt y)^2 = y := Real.sq_sqrt (by linarith)
  have hm := mul_nonneg (Real.sqrt_nonneg y) (show 0 ≤ Real.sqrt y - 160000 by linarith)
  have hl : (4001/100:ℝ)*Real.sqrt y ≤ (26/100000:ℝ)*y := by
    nlinarith only [hs2, hm]
  have hprod : (26000000000:ℝ)*160000 ≤ y*Real.sqrt y :=
    mul_le_mul hy hs (by norm_num) (by linarith)
  have hr : (513*10^8:ℝ)/Real.sqrt y ≤ (13/10^6:ℝ)*y := by
    apply (div_le_iff₀ hspos).2
    nlinarith only [hprod]
  have htwo : (2:ℝ) ≤ y / 10^9 := by nlinarith only [hy]
  linarith only [hl,hr,htwo,hy]

private lemma budget_case3 (y : ℝ) (hy : (10000000000000:ℝ) ≤ y) :
    2 + (4001/100:ℝ)*Real.sqrt y + (154/10^6:ℝ)*y +
      (513*10^8:ℝ)/Real.sqrt y ≤ y / 5440 := by
  have hs : (3000000:ℝ) ≤ Real.sqrt y := by
    have hh := Real.sqrt_le_sqrt (show (3000000:ℝ)^2 ≤ y by nlinarith only [hy])
    norm_num at hh
    exact hh
  have hspos : 0 < Real.sqrt y := by linarith
  have hs2 : (Real.sqrt y)^2 = y := Real.sq_sqrt (by linarith)
  have hm := mul_nonneg (Real.sqrt_nonneg y) (show 0 ≤ Real.sqrt y - 3000000 by linarith)
  have hl : (4001/100:ℝ)*Real.sqrt y ≤ (14/10^6:ℝ)*y := by
    nlinarith only [hs2, hm]
  have hprod : (10000000000000:ℝ)*3000000 ≤ y*Real.sqrt y :=
    mul_le_mul hy hs (by norm_num) (by linarith)
  have hr : (513*10^8:ℝ)/Real.sqrt y ≤ (1/10^8:ℝ)*y := by
    apply (div_le_iff₀ hspos).2
    nlinarith only [hprod]
  have htwo : (2:ℝ) ≤ y / 10^9 := by nlinarith only [hy]
  linarith only [hl,hr,htwo,hy]

theorem solution
    (hRH : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      0 ≤ s.im → s.im ≤ 10 ^ 6 → s.re = 1/2)
    (y : ℝ) (hy : Real.exp 23 ≤ y) (hY : y < Real.exp 136) :
    |Chebyshev.psi y - y| ≤ y / (40 * Real.log y) := by
  have hRH' : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      0 ≤ s.im → s.im ≤ H → s.re = 1/2 := by
    intro s hz hre hre1 him hH
    apply hRH s hz hre hre1 him
    dsimp [H] at hH
    norm_num at hH ⊢
    exact hH
  have hy0 : 0 < y := (Real.exp_pos 23).trans_le hy
  have hlog : 0 < Real.log y := Real.log_pos (by linarith [exp_lower_23.trans hy])
  have hlog136 : Real.log y < 136 := by
    have hh := Real.log_lt_log hy0 hY
    simpa using hh
  have hpsi := psi_error_rh_smoothed y (exp_lower_23.trans hy) hRH'
  by_cases hy24 : y < Real.exp 24
  · have hlog24 : Real.log y ≤ 24 := by
      have hh := Real.log_lt_log hy0 hy24
      exact (by simpa using hh : Real.log y < 24).le
    have hb := budget_case1 y (exp_lower_23.trans hy)
    have hdiv : y / 960 ≤ y / (40*Real.log y) := by
      apply div_le_div_of_nonneg_left hy0.le (by positivity)
      linarith
    exact hpsi.trans (hb.trans hdiv)
  · have hy24' : Real.exp 24 ≤ y := le_of_not_gt hy24
    by_cases hy30 : y < Real.exp 30
    · have hlog30 : Real.log y ≤ 30 := by
        have hh := Real.log_lt_log hy0 hy30
        exact (by simpa using hh : Real.log y < 30).le
      have hb := budget_case2 y (exp_lower_24.trans hy24')
      have hdiv : y / 1200 ≤ y / (40*Real.log y) := by
        apply div_le_div_of_nonneg_left hy0.le (by positivity)
        linarith
      exact hpsi.trans (hb.trans hdiv)
    · have hy30' : Real.exp 30 ≤ y := le_of_not_gt hy30
      have hb := budget_case3 y (exp_lower_30.trans hy30')
      have hdiv : y / 5440 ≤ y / (40*Real.log y) := by
        apply div_le_div_of_nonneg_left hy0.le (by positivity)
        linarith
      exact hpsi.trans (hb.trans hdiv)
