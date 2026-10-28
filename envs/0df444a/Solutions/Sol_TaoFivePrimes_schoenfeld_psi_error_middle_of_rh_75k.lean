-- Prove2me | solution 1 for TaoFivePrimes.schoenfeld_psi_error_middle_of_rh_75k
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:07:32.317672+00:00
-- url     : https://prove2.me/submissions/918f9dc5-582b-409b-979e-ea28a290ce49

/- Derived from the checked 100,000-height smoothing reduction. The explicit formula and zero-count bounds are credited in its source. -/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_PowerQuarterWeights
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_LowZeroReciprocal
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_ShiftedLogarithmicTail
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_SharpNumericalZeroTail
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_NumericalZeroTail
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_ImprovedRegion

set_option autoImplicit false
set_option maxHeartbeats 2000000
open DusartSmoothing Complex Set

private def H : ℝ := 75000

private lemma log_ratio_le : Real.log (H / (2*Real.pi)) ≤ 19/2 := by
  have he9 : (8100:ℝ) ≤ Real.exp 9 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7182818283) Real.exp_one_gt_d9.le 9
    rw [← Real.exp_nat_mul] at hp
    norm_num at hp ⊢
    linarith
  have hehalf : (3/2:ℝ) ≤ Real.exp (1/2) := by
    linarith [Real.add_one_le_exp (1/2)]
  have hp := mul_le_mul he9 hehalf (by norm_num) (Real.exp_nonneg 9)
  have he : Real.exp 9 * Real.exp (1/2) = Real.exp (19/2) := by
    rw [←Real.exp_add]
    congr 1
    ring
  rw [he] at hp
  have hratio : H/(2*Real.pi) ≤ (12000:ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2*Real.pi)).2
    dsimp [H]
    nlinarith [Real.pi_gt_d2]
  have harg : 0 < H/(2*Real.pi) := by dsimp [H]; positivity
  apply (Real.log_le_iff_le_exp harg).2
  linarith

private lemma high_reciprocal_num :
    (2 * Real.log (H / (2 * Real.pi)) + 1) / (8 * Real.pi * H^2) +
      (18 * Real.log H + 179) / H^3 ≤ (287/(2*10^12):ℝ) := by
  have hl := ExplicitPNT.DusartTable1.Modules.NumericalZeroTail.1 H 12
    (by norm_num [H]) (by norm_num [H])
  norm_num at hl
  have hratio := log_ratio_le
  have hp : (25:ℝ) ≤ 8*Real.pi := by nlinarith [Real.pi_gt_d2]
  have h1 : (2*Real.log (H/(2*Real.pi))+1)/(8*Real.pi*H^2) ≤ (4/5:ℝ)/H^2 := by
    apply (div_le_iff₀ (by dsimp [H]; positivity : 0 < 8*Real.pi*H^2)).2
    dsimp [H] at *
    norm_num at *
    nlinarith only [hratio,hp]
  have h2 : (18*Real.log H+179)/H^3 ≤ (395:ℝ)/H^3 := by
    apply div_le_div_of_nonneg_right (by linarith) (by dsimp [H]; positivity)
  dsimp [H] at h1 h2 ⊢
  norm_num at h1 h2 ⊢
  linarith only [h1,h2]

private lemma log14_le_three : Real.log 14 ≤ 3 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7)
    (show (2.7:ℝ) ≤ Real.exp 1 by linarith [Real.exp_one_gt_d9]) 3
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  apply (Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 14)).2
  linarith

private lemma low_reciprocal_num :
    (Real.log (H / (2 * Real.pi)))^2 / (4 * Real.pi) - 1 / (4 * Real.pi) +
        (9 * Real.log 14 + 91) / 14 ≤ (313/20:ℝ) := by
  have harg : 1 ≤ H/(2*Real.pi) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*Real.pi)).2
    dsimp [H]
    nlinarith [Real.pi_lt_four]
  have hlo : 0 ≤ Real.log (H/(2*Real.pi)) := Real.log_nonneg harg
  have hsq := pow_le_pow_left₀ hlo log_ratio_le 2
  have hratio : (Real.log (H/(2*Real.pi)))^2 / (4*Real.pi) ≤ (36/5:ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 4*Real.pi)).2
    nlinarith only [hsq, Real.pi_gt_d2]
  have hpos : 0 ≤ 1/(4*Real.pi) := by positivity
  linarith [log14_le_three]

private lemma low_absolute_weight (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ)
    (hγ : ∀ ρ ∈ Z, |ρ.im| ≤ H) :
    (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * (1 / |ρ.im|)) ≤ (313/10:ℝ) := by
  classical
  let W : ℝ → ℝ := fun t => if t ≤ H then 1/t else 0
  have hpos (S : Finset ℂ) (hS : ∀ ρ ∈ S, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im) :
      (∑ ρ ∈ S, (RvM.zeroMult ρ : ℝ) * W ρ.im) ≤ (313/20:ℝ) := by
    let F := S.filter (fun ρ => ρ.im ≤ H)
    have hF : ∀ ρ ∈ F, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im := by
      intro ρ hρ
      exact hS ρ (Finset.mem_filter.mp hρ).1
    have hh := ExplicitPNT.DusartTable1.Modules.LowZeroReciprocal F hF H (by norm_num [H])
      (fun ρ hρ => (Finset.mem_filter.mp hρ).2)
    have hs : (∑ ρ ∈ F, (RvM.zeroMult ρ : ℝ) * (1 / ρ.im)) ≤ (313/20:ℝ) := hh.trans low_reciprocal_num
    simpa only [F, W, Finset.sum_filter, mul_ite, mul_zero] using hs
  have hh := ExplicitPNT.DusartTable1.Modules.PowerQuarterWeights.1 W (313/20:ℝ) hpos Z hZ
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
    (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * (1 / |ρ.im|^3)) ≤ 287 / 10^12 := by
  classical
  let W : ℝ → ℝ := fun t => if H < t then 1/t^3 else 0
  have hpos (S : Finset ℂ) (hS : ∀ ρ ∈ S, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im) :
      (∑ ρ ∈ S, (RvM.zeroMult ρ : ℝ) * W ρ.im) ≤ (287/(2*10^12):ℝ) := by
    let F := S.filter (fun ρ => H < ρ.im)
    have hF : ∀ ρ ∈ F, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im := by
      intro ρ hρ
      exact hS ρ (Finset.mem_filter.mp hρ).1
    have hh := ExplicitPNT.DusartTable1.Modules.ShiftedLogarithmicTail.2 F hF H
      (by norm_num [H]) (fun ρ hρ => (Finset.mem_filter.mp hρ).2)
    have hb := hh.trans high_reciprocal_num
    simpa only [F, W, Finset.sum_filter, mul_ite, mul_zero] using hb
  have hh := ExplicitPNT.DusartTable1.Modules.PowerQuarterWeights.1 W
    (287/(2*10^12):ℝ) hpos Z hZ
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
      (313/10:ℝ) * Real.sqrt z + (4*z^(23/8:ℝ)/h^2) * (287 / 10^12 : ℝ) := by
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
      Real.sqrt z * (313/10:ℝ) := by
    calc
      _ ≤ ∑ ρ ∈ L, Real.sqrt z * ((RvM.zeroMult ρ.val : ℝ) * (1/|ρ.val.im|)) :=
        Finset.sum_le_sum (fun ρ hρ => hterm_low ρ (Finset.mem_filter.mp hρ).2)
      _ = Real.sqrt z * (∑ ρ ∈ L, (RvM.zeroMult ρ.val : ℝ) * (1/|ρ.val.im|)) := by rw [Finset.mul_sum]
      _ ≤ Real.sqrt z * (313/10:ℝ) := mul_le_mul_of_nonneg_left hL (Real.sqrt_nonneg z)
  have hsumU : (∑ ρ ∈ U, ‖(RvM.zeroMult ρ.val : ℂ) * smoothedZeroKernel a h ρ.val‖) ≤
      (4*z^(23/8:ℝ)/h^2) * (287/10^12:ℝ) := by
    calc
      _ ≤ ∑ ρ ∈ U, (4*z^(23/8:ℝ)/h^2) * ((RvM.zeroMult ρ.val : ℝ) * (1/|ρ.val.im|^3)) :=
        Finset.sum_le_sum (fun ρ hρ => hterm_high ρ (lt_of_not_ge (Finset.mem_filter.mp hρ).2))
      _ = (4*z^(23/8:ℝ)/h^2) * (∑ ρ ∈ U, (RvM.zeroMult ρ.val : ℝ) * (1/|ρ.val.im|^3)) := by rw [Finset.mul_sum]
      _ ≤ (4*z^(23/8:ℝ)/h^2) * (287/10^12:ℝ) := mul_le_mul_of_nonneg_left hU (by positivity)
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
      2 + (313/10:ℝ)*Real.sqrt z + (4*z^(23/8:ℝ)/h^2)*(287/10^12:ℝ) + 512*z^(3/2:ℝ)/h^2 := by
  have hp := doubleBoxAverage_psi_error_zero_sum a h ha hh
  have hs := smoothed_zero_norm_split a h z ha hh haz hRH
  have hr : 512*(a+2*h)^(3/2:ℝ)/h^2 ≤ 512*z^(3/2:ℝ)/h^2 := by gcongr
  linarith only [hp,hs,hr]


private lemma psi_error_rh_smoothed (y D R K : ℝ) (hy : (9743000000:ℝ) ≤ y)
    (hD : 2000 ≤ D) (hR : 0 < R) (hRy : R^8 ≤ y)
    (hK : 4*(1001/1000:ℝ)^3*(287/10^12:ℝ)*D^2/R ≤ K)
    (hRH : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      0 ≤ s.im → s.im ≤ H → s.re = 1/2) :
    |Chebyshev.psi y - y| ≤ 2 + (3132/100:ℝ)*Real.sqrt y +
      (K + 1/D)*y + (513*D^2)/Real.sqrt y := by
  have hypos : 0 < y := by linarith
  have hDpos : 0 < D := by linarith
  let h : ℝ := y/D
  let z : ℝ := (1001/1000:ℝ)*y
  have hh : 0 < h := by dsimp [h]; positivity
  have hz : 0 < z := by dsimp [z]; positivity
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hypos
  have hs2 : (Real.sqrt y)^2 = y := Real.sq_sqrt hypos.le
  have hz2 : (Real.sqrt z)^2 = z := Real.sq_sqrt hz.le
  have hsqrtz : Real.sqrt z ≤ (2001/2000:ℝ)*Real.sqrt y := by
    have hz0 := Real.sqrt_nonneg z
    dsimp [z] at hz2
    nlinarith only [hz2,hs2,hz0,hs]
  have hlow : (313/10:ℝ)*Real.sqrt z ≤ (3132/100:ℝ)*Real.sqrt y := by
    nlinarith only [hsqrtz,hs]
  have hroot_eq : (z^(1/8:ℝ))^8 = z := by
    rw [←Real.rpow_natCast, ←Real.rpow_mul hz.le]
    norm_num
  have hroot : R ≤ z^(1/8:ℝ) := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8:ℕ) ≠ 0) (Real.rpow_nonneg hz.le _)
    rw [hroot_eq]
    dsimp [z]
    nlinarith only [hRy,hypos]
  have hroot3 : z^(23/8:ℝ)*z^(1/8:ℝ) = z^3 := by
    rw [←Real.rpow_add hz]
    norm_num [Real.rpow_natCast]
  have hpow : z^(23/8:ℝ) ≤ z^3/R := by
    apply (le_div_iff₀ hR).2
    have hm := mul_nonneg (Real.rpow_nonneg hz.le (23/8:ℝ))
      (sub_nonneg.2 hroot)
    nlinarith only [hm,hroot3]
  have hhigh : (4*z^(23/8:ℝ)/h^2)*(287/10^12:ℝ) ≤ K*y := by
    calc
      _ ≤ (4*(z^3/R)/h^2)*(287/10^12:ℝ) := by gcongr
      _ ≤ _ := by
        dsimp [h,z]
        have hm := mul_le_mul_of_nonneg_right hK hypos.le
        field_simp at hm ⊢
        nlinarith only [hm,hypos,hDpos,hR]
  have hzpow : z^(3/2:ℝ) = z*Real.sqrt z := by
    rw [show (3/2:ℝ) = 1 + 1/2 by norm_num, Real.rpow_add hz, Real.rpow_one, ←Real.sqrt_eq_rpow]
  have hnum : 512*z*Real.sqrt z ≤ 513*y*Real.sqrt y := by
    have hm := mul_le_mul_of_nonneg_left hsqrtz (show (0:ℝ) ≤ 512*z by positivity)
    dsimp [z] at hm ⊢
    nlinarith only [hm,hypos,hs]
  have hrem0 : 512*z^(3/2:ℝ)/h^2 ≤ 513*y*Real.sqrt y/h^2 := by
    rw [hzpow]
    exact div_le_div_of_nonneg_right (by simpa only [mul_assoc] using hnum) (sq_nonneg h)
  have hid : 513*y*Real.sqrt y/h^2 = (513*D^2)/Real.sqrt y := by
    dsimp [h]
    field_simp
    have hm := congrArg (fun u : ℝ => y*D^2*u) hs2
    nlinarith only [hm,hs2]
  rw [hid] at hrem0
  let E : ℝ := 2 + (313/10:ℝ)*Real.sqrt z + (4*z^(23/8:ℝ)/h^2)*(287/10^12:ℝ) +
    512*z^(3/2:ℝ)/h^2
  have hEt : E ≤ 2+(3132/100:ℝ)*Real.sqrt y+K*y+(513*D^2)/Real.sqrt y := by
    dsimp [E]
    linarith only [hlow,hhigh,hrem0]
  have hzlow : y-2*h+2*h ≤ z := by dsimp [z]; linarith
  have hzhigh : y+2*h ≤ z := by
    dsimp [h,z]
    have hd : (1:ℝ)/D ≤ 1/2000 := by
      exact one_div_le_one_div_of_le (by norm_num) hD
    have hm := mul_le_mul_of_nonneg_left hd hypos.le
    simp only [mul_one_div] at hm
    linarith
  have hposlow : 1 ≤ y-2*h := by
    dsimp [h]
    have hd : (1:ℝ)/D ≤ 1/2000 := by
      exact one_div_le_one_div_of_le (by norm_num) hD
    have hm := mul_le_mul_of_nonneg_left hd hypos.le
    simp only [mul_one_div] at hm
    linarith
  have hLo := double_average_split (y-2*h) h z hposlow hh hzlow hRH
  have hHi := double_average_split y h z (by linarith) hh hzhigh hRH
  have hc : y-2*h+h = y-h := by ring
  rw [hc] at hLo
  have hpsi := psi_error_of_double_average_errors y h E hh hLo hHi
  dsimp [h] at hpsi
  have hEq : y/D = (1/D)*y := by ring
  rw [hEq] at hpsi
  linarith only [hpsi,hEt]

private lemma exp_lower_23 : (9743000000:ℝ) ≤ Real.exp 23 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7182818283) Real.exp_one_gt_d9.le 23
  rw [←Real.exp_nat_mul] at hp
  norm_num at hp ⊢
  linarith

private lemma exp_lower_24 : (26000000000:ℝ) ≤ Real.exp 24 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7182818283) Real.exp_one_gt_d9.le 24
  rw [←Real.exp_nat_mul] at hp
  norm_num at hp ⊢
  linarith

private lemma exp_lower_26 : (190000000000:ℝ) ≤ Real.exp 26 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7182818283) Real.exp_one_gt_d9.le 26
  rw [←Real.exp_nat_mul] at hp
  norm_num at hp ⊢
  linarith

private lemma exp_lower_30 : (10000000000000:ℝ) ≤ Real.exp 30 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7182818283) Real.exp_one_gt_d9.le 30
  rw [←Real.exp_nat_mul] at hp
  norm_num at hp ⊢
  linarith

private lemma exp_lower_40 : (200000000000000000:ℝ) ≤ Real.exp 40 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7182818283) Real.exp_one_gt_d9.le 40
  rw [←Real.exp_nat_mul] at hp
  norm_num at hp ⊢
  linarith

private lemma exp_lower_60 : (100000000000000000000000000:ℝ) ≤ Real.exp 60 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7182818283) Real.exp_one_gt_d9.le 60
  rw [←Real.exp_nat_mul] at hp
  norm_num at hp ⊢
  linarith

private lemma exp_lower_231 : (10760000000:ℝ) ≤ Real.exp (231/10) := by
  have he : (221/200:ℝ) ≤ Real.exp (1/10) := by
    have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 1/10 by norm_num) 3
    norm_num [Finset.sum_range_succ] at h
    exact h
  have hm := mul_le_mul exp_lower_23 he (by norm_num) (Real.exp_nonneg 23)
  have hid : Real.exp 23 * Real.exp (1/10) = Real.exp (231/10) := by
    rw [←Real.exp_add]
    congr 1
    ring
  rw [hid] at hm
  linarith

private lemma exp_lower_234 : (14400000000:ℝ) ≤ Real.exp (117/5) := by
  have he : (37/25:ℝ) ≤ Real.exp (2/5) := by
    have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 2/5 by norm_num) 3
    norm_num [Finset.sum_range_succ] at h
    exact h
  have hm := mul_le_mul exp_lower_23 he (by norm_num) (Real.exp_nonneg 23)
  have hid : Real.exp 23 * Real.exp (2/5) = Real.exp (117/5) := by
    rw [←Real.exp_add]
    congr 1
    ring
  rw [hid] at hm
  linarith

private lemma budget_case1 (y : ℝ) (hy : (9743000000:ℝ) ≤ y) :
    2 + (3132/100:ℝ)*Real.sqrt y + (261/10^6 + 1/2000:ℝ)*y +
      (513*2000^2:ℝ)/Real.sqrt y ≤ y / 924 := by
  have hs : (98700:ℝ) ≤ Real.sqrt y := by
    have hh := Real.sqrt_le_sqrt (show (98700:ℝ)^2 ≤ y by nlinarith only [hy])
    norm_num at hh
    exact hh
  have hspos : 0 < Real.sqrt y := by linarith
  have hs2 : (Real.sqrt y)^2 = y := Real.sq_sqrt (by linarith)
  have hm := mul_nonneg (Real.sqrt_nonneg y) (show 0 ≤ Real.sqrt y - 98700 by linarith)
  have hl : (3132/100:ℝ)*Real.sqrt y ≤ (3174/10^7:ℝ)*y := by
    nlinarith only [hs2, hm]
  have hprod : (9743000000:ℝ)*98700 ≤ y*Real.sqrt y :=
    mul_le_mul hy hs (by norm_num) (by linarith)
  have hr : (513*2000^2:ℝ)/Real.sqrt y ≤ (22/10^7:ℝ)*y := by
    apply (div_le_iff₀ hspos).2
    nlinarith only [hprod]
  have htwo : (2:ℝ) ≤ y / 10^9 := by nlinarith only [hy]
  linarith only [hl,hr,htwo,hy]

private lemma budget_case2 (y : ℝ) (hy : (10760000000:ℝ) ≤ y) :
    2 + (3132/100:ℝ)*Real.sqrt y + (258/10^6 + 1/2000:ℝ)*y +
      (513*2000^2:ℝ)/Real.sqrt y ≤ y / 936 := by
  have hs : (103700:ℝ) ≤ Real.sqrt y := by
    have hh := Real.sqrt_le_sqrt (show (103700:ℝ)^2 ≤ y by nlinarith only [hy])
    norm_num at hh
    exact hh
  have hspos : 0 < Real.sqrt y := by linarith
  have hs2 : (Real.sqrt y)^2 = y := Real.sq_sqrt (by linarith)
  have hm := mul_nonneg (Real.sqrt_nonneg y) (show 0 ≤ Real.sqrt y - 103700 by linarith)
  have hl : (3132/100:ℝ)*Real.sqrt y ≤ (303/10^6:ℝ)*y := by
    nlinarith only [hs2, hm]
  have hprod : (10760000000:ℝ)*103700 ≤ y*Real.sqrt y :=
    mul_le_mul hy hs (by norm_num) (by linarith)
  have hr : (513*2000^2:ℝ)/Real.sqrt y ≤ (2/10^6:ℝ)*y := by
    apply (div_le_iff₀ hspos).2
    nlinarith only [hprod]
  have htwo : (2:ℝ) ≤ y / 10^9 := by nlinarith only [hy]
  linarith only [hl,hr,htwo,hy]

private lemma budget_case3 (y : ℝ) (hy : (14400000000:ℝ) ≤ y) :
    2 + (3132/100:ℝ)*Real.sqrt y + (248/10^6 + 1/2000:ℝ)*y +
      (513*2000^2:ℝ)/Real.sqrt y ≤ y / 960 := by
  have hs : (120000:ℝ) ≤ Real.sqrt y := by
    have hh := Real.sqrt_le_sqrt (show (120000:ℝ)^2 ≤ y by nlinarith only [hy])
    norm_num at hh
    exact hh
  have hspos : 0 < Real.sqrt y := by linarith
  have hs2 : (Real.sqrt y)^2 = y := Real.sq_sqrt (by linarith)
  have hm := mul_nonneg (Real.sqrt_nonneg y) (show 0 ≤ Real.sqrt y - 120000 by linarith)
  have hl : (3132/100:ℝ)*Real.sqrt y ≤ (261/10^6:ℝ)*y := by
    nlinarith only [hs2, hm]
  have hprod : (14400000000:ℝ)*120000 ≤ y*Real.sqrt y :=
    mul_le_mul hy hs (by norm_num) (by linarith)
  have hr : (513*2000^2:ℝ)/Real.sqrt y ≤ (12/10^7:ℝ)*y := by
    apply (div_le_iff₀ hspos).2
    nlinarith only [hprod]
  have htwo : (2:ℝ) ≤ y / 10^9 := by nlinarith only [hy]
  linarith only [hl,hr,htwo,hy]

private lemma budget_case4 (y : ℝ) (hy : (26000000000:ℝ) ≤ y) :
    2 + (3132/100:ℝ)*Real.sqrt y + (231/10^6 + 1/2000:ℝ)*y +
      (513*2000^2:ℝ)/Real.sqrt y ≤ y / 1040 := by
  have hs : (160000:ℝ) ≤ Real.sqrt y := by
    have hh := Real.sqrt_le_sqrt (show (160000:ℝ)^2 ≤ y by nlinarith only [hy])
    norm_num at hh
    exact hh
  have hspos : 0 < Real.sqrt y := by linarith
  have hs2 : (Real.sqrt y)^2 = y := Real.sq_sqrt (by linarith)
  have hm := mul_nonneg (Real.sqrt_nonneg y) (show 0 ≤ Real.sqrt y - 160000 by linarith)
  have hl : (3132/100:ℝ)*Real.sqrt y ≤ (196/10^6:ℝ)*y := by
    nlinarith only [hs2, hm]
  have hprod : (26000000000:ℝ)*160000 ≤ y*Real.sqrt y :=
    mul_le_mul hy hs (by norm_num) (by linarith)
  have hr : (513*2000^2:ℝ)/Real.sqrt y ≤ (1/10^6:ℝ)*y := by
    apply (div_le_iff₀ hspos).2
    nlinarith only [hprod]
  have htwo : (2:ℝ) ≤ y / 10^9 := by nlinarith only [hy]
  linarith only [hl,hr,htwo,hy]

private lemma budget_case5 (y : ℝ) (hy : (190000000000:ℝ) ≤ y) :
    2 + (3132/100:ℝ)*Real.sqrt y + (288/10^6 + 1/2500:ℝ)*y +
      (513*2500^2:ℝ)/Real.sqrt y ≤ y / 1200 := by
  have hs : (435000:ℝ) ≤ Real.sqrt y := by
    have hh := Real.sqrt_le_sqrt (show (435000:ℝ)^2 ≤ y by nlinarith only [hy])
    norm_num at hh
    exact hh
  have hspos : 0 < Real.sqrt y := by linarith
  have hs2 : (Real.sqrt y)^2 = y := Real.sq_sqrt (by linarith)
  have hm := mul_nonneg (Real.sqrt_nonneg y) (show 0 ≤ Real.sqrt y - 435000 by linarith)
  have hl : (3132/100:ℝ)*Real.sqrt y ≤ (72/10^6:ℝ)*y := by
    nlinarith only [hs2, hm]
  have hprod : (190000000000:ℝ)*435000 ≤ y*Real.sqrt y :=
    mul_le_mul hy hs (by norm_num) (by linarith)
  have hr : (513*2500^2:ℝ)/Real.sqrt y ≤ (1/10^6:ℝ)*y := by
    apply (div_le_iff₀ hspos).2
    nlinarith only [hprod]
  have htwo : (2:ℝ) ≤ y / 10^9 := by nlinarith only [hy]
  linarith only [hl,hr,htwo,hy]

private lemma budget_case6 (y : ℝ) (hy : (10000000000000:ℝ) ≤ y) :
    2 + (3132/100:ℝ)*Real.sqrt y + (260/10^6 + 1/3000:ℝ)*y +
      (513*3000^2:ℝ)/Real.sqrt y ≤ y / 1600 := by
  have hs : (3000000:ℝ) ≤ Real.sqrt y := by
    have hh := Real.sqrt_le_sqrt (show (3000000:ℝ)^2 ≤ y by nlinarith only [hy])
    norm_num at hh
    exact hh
  have hspos : 0 < Real.sqrt y := by linarith
  have hs2 : (Real.sqrt y)^2 = y := Real.sq_sqrt (by linarith)
  have hm := mul_nonneg (Real.sqrt_nonneg y) (show 0 ≤ Real.sqrt y - 3000000 by linarith)
  have hl : (3132/100:ℝ)*Real.sqrt y ≤ (11/10^6:ℝ)*y := by
    nlinarith only [hs2, hm]
  have hprod : (10000000000000:ℝ)*3000000 ≤ y*Real.sqrt y :=
    mul_le_mul hy hs (by norm_num) (by linarith)
  have hr : (513*3000^2:ℝ)/Real.sqrt y ≤ (1/10^9:ℝ)*y := by
    apply (div_le_iff₀ hspos).2
    nlinarith only [hprod]
  have htwo : (2:ℝ) ≤ y / 10^9 := by nlinarith only [hy]
  linarith only [hl,hr,htwo,hy]

private lemma budget_case7 (y : ℝ) (hy : (200000000000000000:ℝ) ≤ y) :
    2 + (3132/100:ℝ)*Real.sqrt y + (132/10^6 + 1/4000:ℝ)*y +
      (513*4000^2:ℝ)/Real.sqrt y ≤ y / 2400 := by
  have hs : (400000000:ℝ) ≤ Real.sqrt y := by
    have hh := Real.sqrt_le_sqrt (show (400000000:ℝ)^2 ≤ y by nlinarith only [hy])
    norm_num at hh
    exact hh
  have hspos : 0 < Real.sqrt y := by linarith
  have hs2 : (Real.sqrt y)^2 = y := Real.sq_sqrt (by linarith)
  have hm := mul_nonneg (Real.sqrt_nonneg y) (show 0 ≤ Real.sqrt y - 400000000 by linarith)
  have hl : (3132/100:ℝ)*Real.sqrt y ≤ (1/10^6:ℝ)*y := by
    nlinarith only [hs2, hm]
  have hprod : (200000000000000000:ℝ)*400000000 ≤ y*Real.sqrt y :=
    mul_le_mul hy hs (by norm_num) (by linarith)
  have hr : (513*4000^2:ℝ)/Real.sqrt y ≤ (1/10^9:ℝ)*y := by
    apply (div_le_iff₀ hspos).2
    nlinarith only [hprod]
  have htwo : (2:ℝ) ≤ y / 10^9 := by nlinarith only [hy]
  linarith only [hl,hr,htwo,hy]

private lemma budget_case8 (y : ℝ) (hy : (100000000000000000000000000:ℝ) ≤ y) :
    2 + (3132/100:ℝ)*Real.sqrt y + (67/10^6 + 1/10000:ℝ)*y +
      (513*10000^2:ℝ)/Real.sqrt y ≤ y / 5440 := by
  have hs : (10000000000000:ℝ) ≤ Real.sqrt y := by
    have hh := Real.sqrt_le_sqrt (show (10000000000000:ℝ)^2 ≤ y by nlinarith only [hy])
    norm_num at hh
    exact hh
  have hspos : 0 < Real.sqrt y := by linarith
  have hs2 : (Real.sqrt y)^2 = y := Real.sq_sqrt (by linarith)
  have hm := mul_nonneg (Real.sqrt_nonneg y) (show 0 ≤ Real.sqrt y - 10000000000000 by linarith)
  have hl : (3132/100:ℝ)*Real.sqrt y ≤ (1/10^9:ℝ)*y := by
    nlinarith only [hs2, hm]
  have hprod : (100000000000000000000000000:ℝ)*10000000000000 ≤ y*Real.sqrt y :=
    mul_le_mul hy hs (by norm_num) (by linarith)
  have hr : (513*10000^2:ℝ)/Real.sqrt y ≤ (1/10^9:ℝ)*y := by
    apply (div_le_iff₀ hspos).2
    nlinarith only [hprod]
  have htwo : (2:ℝ) ≤ y / 10^9 := by nlinarith only [hy]
  linarith only [hl,hr,htwo,hy]

theorem solution
    (hRH : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      0 ≤ s.im → s.im ≤ 75000 → s.re = 1/2)
    (y : ℝ) (hy : Real.exp 23 ≤ y) (hY : y < Real.exp 136) :
    |Chebyshev.psi y - y| ≤ y / (40 * Real.log y) := by
  have hRH' : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      0 ≤ s.im → s.im ≤ H → s.re = 1/2 := by
    intro s hz hre hre1 him hH
    apply hRH s hz hre hre1 him
    simpa [H] using hH
  have hy0 : 0 < y := (Real.exp_pos 23).trans_le hy
  have hlog : 0 < Real.log y := Real.log_pos (by linarith [exp_lower_23.trans hy])
  have hyA : (9743000000:ℝ) ≤ y := exp_lower_23.trans hy
  by_cases hcut0 : y < Real.exp (231/10)
  · have hlogN : Real.log y ≤ (231/10:ℝ) := by
      have hh := Real.log_lt_log hy0 hcut0
      exact (by simpa using hh : Real.log y < (231/10:ℝ)).le
    have hA : (9743000000:ℝ) ≤ y := exp_lower_23.trans hy
    have hs := psi_error_rh_smoothed y 2000 (177/10) (261/10^6) hyA
      (by norm_num) (by norm_num) (by nlinarith only [hA]) (by norm_num) hRH'
    have hb := budget_case1 y hA
    have hdiv : y / 924 ≤ y / (40*Real.log y) := by
      apply div_le_div_of_nonneg_left hy0.le (by positivity)
      linarith
    exact hs.trans (hb.trans hdiv)
  · have hcut0' : Real.exp (231/10) ≤ y := le_of_not_gt hcut0
    by_cases hcut1 : y < Real.exp (117/5)
    · have hlogN : Real.log y ≤ (117/5:ℝ) := by
        have hh := Real.log_lt_log hy0 hcut1
        exact (by simpa using hh : Real.log y < (117/5:ℝ)).le
      have hA : (10760000000:ℝ) ≤ y := exp_lower_231.trans hcut0'
      have hs := psi_error_rh_smoothed y 2000 (179/10) (258/10^6) hyA
        (by norm_num) (by norm_num) (by nlinarith only [hA]) (by norm_num) hRH'
      have hb := budget_case2 y hA
      have hdiv : y / 936 ≤ y / (40*Real.log y) := by
        apply div_le_div_of_nonneg_left hy0.le (by positivity)
        linarith
      exact hs.trans (hb.trans hdiv)
    · have hcut1' : Real.exp (117/5) ≤ y := le_of_not_gt hcut1
      by_cases hcut2 : y < Real.exp (24)
      · have hlogN : Real.log y ≤ (24:ℝ) := by
          have hh := Real.log_lt_log hy0 hcut2
          exact (by simpa using hh : Real.log y < (24:ℝ)).le
        have hA : (14400000000:ℝ) ≤ y := exp_lower_234.trans hcut1'
        have hs := psi_error_rh_smoothed y 2000 (93/5) (248/10^6) hyA
          (by norm_num) (by norm_num) (by nlinarith only [hA]) (by norm_num) hRH'
        have hb := budget_case3 y hA
        have hdiv : y / 960 ≤ y / (40*Real.log y) := by
          apply div_le_div_of_nonneg_left hy0.le (by positivity)
          linarith
        exact hs.trans (hb.trans hdiv)
      · have hcut2' : Real.exp (24) ≤ y := le_of_not_gt hcut2
        by_cases hcut3 : y < Real.exp (26)
        · have hlogN : Real.log y ≤ (26:ℝ) := by
            have hh := Real.log_lt_log hy0 hcut3
            exact (by simpa using hh : Real.log y < (26:ℝ)).le
          have hA : (26000000000:ℝ) ≤ y := exp_lower_24.trans hcut2'
          have hs := psi_error_rh_smoothed y 2000 (20) (231/10^6) hyA
            (by norm_num) (by norm_num) (by nlinarith only [hA]) (by norm_num) hRH'
          have hb := budget_case4 y hA
          have hdiv : y / 1040 ≤ y / (40*Real.log y) := by
            apply div_le_div_of_nonneg_left hy0.le (by positivity)
            linarith
          exact hs.trans (hb.trans hdiv)
        · have hcut3' : Real.exp (26) ≤ y := le_of_not_gt hcut3
          by_cases hcut4 : y < Real.exp (30)
          · have hlogN : Real.log y ≤ (30:ℝ) := by
              have hh := Real.log_lt_log hy0 hcut4
              exact (by simpa using hh : Real.log y < (30:ℝ)).le
            have hA : (190000000000:ℝ) ≤ y := exp_lower_26.trans hcut3'
            have hs := psi_error_rh_smoothed y 2500 (25) (288/10^6) hyA
              (by norm_num) (by norm_num) (by nlinarith only [hA]) (by norm_num) hRH'
            have hb := budget_case5 y hA
            have hdiv : y / 1200 ≤ y / (40*Real.log y) := by
              apply div_le_div_of_nonneg_left hy0.le (by positivity)
              linarith
            exact hs.trans (hb.trans hdiv)
          · have hcut4' : Real.exp (30) ≤ y := le_of_not_gt hcut4
            by_cases hcut5 : y < Real.exp (40)
            · have hlogN : Real.log y ≤ (40:ℝ) := by
                have hh := Real.log_lt_log hy0 hcut5
                exact (by simpa using hh : Real.log y < (40:ℝ)).le
              have hA : (10000000000000:ℝ) ≤ y := exp_lower_30.trans hcut4'
              have hs := psi_error_rh_smoothed y 3000 (40) (260/10^6) hyA
                (by norm_num) (by norm_num) (by nlinarith only [hA]) (by norm_num) hRH'
              have hb := budget_case6 y hA
              have hdiv : y / 1600 ≤ y / (40*Real.log y) := by
                apply div_le_div_of_nonneg_left hy0.le (by positivity)
                linarith
              exact hs.trans (hb.trans hdiv)
            · have hcut5' : Real.exp (40) ≤ y := le_of_not_gt hcut5
              by_cases hcut6 : y < Real.exp (60)
              · have hlogN : Real.log y ≤ (60:ℝ) := by
                  have hh := Real.log_lt_log hy0 hcut6
                  exact (by simpa using hh : Real.log y < (60:ℝ)).le
                have hA : (200000000000000000:ℝ) ≤ y := exp_lower_40.trans hcut5'
                have hs := psi_error_rh_smoothed y 4000 (140) (132/10^6) hyA
                  (by norm_num) (by norm_num) (by nlinarith only [hA]) (by norm_num) hRH'
                have hb := budget_case7 y hA
                have hdiv : y / 2400 ≤ y / (40*Real.log y) := by
                  apply div_le_div_of_nonneg_left hy0.le (by positivity)
                  linarith
                exact hs.trans (hb.trans hdiv)
              · have hcut6' : Real.exp (60) ≤ y := le_of_not_gt hcut6
                have hlogN : Real.log y ≤ 136 := by
                  have hh := Real.log_lt_log hy0 hY
                  exact (by simpa using hh : Real.log y < 136).le
                have hA : (100000000000000000000000000:ℝ) ≤ y := exp_lower_60.trans hcut6'
                have hs := psi_error_rh_smoothed y 10000 (1750) (67/10^6) hyA
                  (by norm_num) (by norm_num) (by nlinarith only [hA]) (by norm_num) hRH'
                have hb := budget_case8 y hA
                have hdiv : y / 5440 ≤ y / (40*Real.log y) := by
                  apply div_le_div_of_nonneg_left hy0.le (by positivity)
                  linarith
                exact hs.trans (hb.trans hdiv)
