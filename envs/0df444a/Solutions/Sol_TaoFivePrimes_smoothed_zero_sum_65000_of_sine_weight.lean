-- Prove2me | solution 1 for TaoFivePrimes.smoothed_zero_sum_65000_of_sine_weight
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:56:20.322195+00:00
-- url     : https://prove2.me/submissions/2ba2a26a-382d-44ae-9b8d-59c0c08946e8

/- Conditional zero-sum reduction. The weighted high-zero hypothesis is explicit. -/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_ImprovedRegion
import Theorems.Thm_TaoFivePrimes_low_zero_reciprocal_weight_65000
import Theorems.Thm_TaoFivePrimes_oscillatory_smoothed_zero_kernel_bound

set_option autoImplicit false
set_option maxHeartbeats 2000000
open DusartSmoothing Complex Set

private lemma low_zero_on_line (ρ : ℂ) (hρ : RvM.IsNontrivialZero ρ)
    (hγ : |ρ.im| ≤ 65000)
    (hRH : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      0 ≤ s.im → s.im ≤ 65000 → s.re = 1/2) :
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

theorem solution (a h z B : ℝ) (ha : 1 ≤ a) (hh : 0 < h) (hsmall : 2*h ≤ a)
    (haz : a+2*h ≤ z) (hB : 0 ≤ B)
    (hRH : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      0 ≤ s.im → s.im ≤ 65000 → s.re = 1/2)
    (hweight : ∀ Z : Finset ℂ, (∀ ρ ∈ Z, RvM.IsNontrivialZero ρ) →
      (∀ ρ ∈ Z, 65000 < |ρ.im|) →
      (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) *
        ((min (4*(Real.sin (ρ.im*(h/(a+h))/2))^2 + 8*(h/(a+h)) +
          3 * |ρ.im| * (h/(a+h))^2) 4) / |ρ.im|^3)) ≤ B) :
    (∑' ρ : NontrivialZetaZero,
      ‖(RvM.zeroMult ρ.val : ℂ) * smoothedZeroKernel a h ρ.val‖) ≤
      (301/10:ℝ)*Real.sqrt z + (z^(23/8:ℝ)/h^2)*B := by
  classical
  have hz : 0 < z := by linarith
  have hz1 : 1 ≤ z := by linarith
  have hterm_low (ρ : NontrivialZetaZero) (hγ : |ρ.val.im| ≤ 65000) :
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
  have hterm_high (ρ : NontrivialZetaZero) (hγ : 65000 < |ρ.val.im|) :
      ‖(RvM.zeroMult ρ.val : ℂ) * smoothedZeroKernel a h ρ.val‖ ≤
        (z^(23/8:ℝ)/h^2) * ((RvM.zeroMult ρ.val : ℝ) *
          ((min (4*(Real.sin (ρ.val.im*(h/(a+h))/2))^2 + 8*(h/(a+h)) +
            3 * |ρ.val.im| * (h/(a+h))^2) 4) / |ρ.val.im|^3)) := by
    have hρ := ρ.property
    have hβ : ρ.val.re ≤ (7/8:ℝ) := by
      by_contra! hβ
      exact ExplicitPNT.DusartTable1.Modules.ImprovedRegion.1 ρ.val hβ hρ.1
    have hi : 0 < |ρ.val.im| := by linarith
    let r : ℝ := h/(a+h)
    let F : ℝ := 4*(Real.sin (ρ.val.im*r/2))^2 + 8*r + 3 * |ρ.val.im| * r^2
    have hr : 0 ≤ r := by dsimp [r]; positivity
    have hF : 0 ≤ F := by dsimp [F]; positivity
    have hpow : (a+2*h)^(ρ.val.re+2) ≤ z^(23/8:ℝ) := by
      exact (Real.rpow_le_rpow (by linarith) haz (by linarith [hρ.2.1])).trans
        (Real.rpow_le_rpow_of_exponent_le hz1 (by linarith))
    have hk : ‖smoothedZeroKernel a h ρ.val‖ ≤
        (a+2*h)^(ρ.val.re+2)/(h^2*|ρ.val.im|^3)*F := by
      simpa [F,r] using TaoFivePrimes.oscillatory_smoothed_zero_kernel_bound a h ρ.val
        (by linarith) hh hsmall hρ.2.1.le hρ.2.2.le hi
    have hk' : ‖smoothedZeroKernel a h ρ.val‖ ≤
        (z^(23/8:ℝ)/h^2)*(F/|ρ.val.im|^3) := by
      calc
        _ ≤ (a+2*h)^(ρ.val.re+2)/(h^2*|ρ.val.im|^3)*F := hk
        _ ≤ z^(23/8:ℝ)/(h^2*|ρ.val.im|^3)*F := by gcongr
        _ = (z^(23/8:ℝ)/h^2)*(F/|ρ.val.im|^3) := by ring
    let M : ℝ := z^(7/8:ℝ)
    have hM : 0 ≤ M := Real.rpow_nonneg hz.le _
    have hp (y : ℝ) (hy : y ∈ Set.Icc a (a+2*h)) : ‖(y:ℂ)^ρ.val‖ ≤ M := by
      have hy0 : 0 < y := by linarith [hy.1]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hy0]
      exact (Real.rpow_le_rpow_of_exponent_le (ha.trans hy.1) hβ).trans
        (Real.rpow_le_rpow hy0.le (hy.2.trans haz) (by norm_num))
    have hbase := norm_smoothedZeroKernel_high a h M (by linarith) hh hM ρ.val hi hp
    have hpowM : M*z^2 = z^(23/8:ℝ) := by
      dsimp [M]
      rw [←Real.rpow_two, ←Real.rpow_add hz]
      norm_num
    have hkcrude : ‖smoothedZeroKernel a h ρ.val‖ ≤
        (z^(23/8:ℝ)/h^2)*(4/|ρ.val.im|^3) := by
      calc
        _ ≤ 4*M*(a+2*h)^2/(h^2*|ρ.val.im|^3) := hbase
        _ ≤ 4*M*z^2/(h^2*|ρ.val.im|^3) := by gcongr
        _ = (z^(23/8:ℝ)/h^2)*(4/|ρ.val.im|^3) := by rw [←hpowM]; ring
    have hkmin : ‖smoothedZeroKernel a h ρ.val‖ ≤
        (z^(23/8:ℝ)/h^2)*(min F 4/|ρ.val.im|^3) := by
      by_cases hF4 : F ≤ 4
      · rw [min_eq_left hF4]
        exact hk'
      · rw [min_eq_right (le_of_not_ge hF4)]
        exact hkcrude
    rw [norm_mul, Complex.norm_natCast]
    have hm := mul_le_mul_of_nonneg_left hkmin (Nat.cast_nonneg (RvM.zeroMult ρ.val))
    simpa only [F,r,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hm
  apply Real.tsum_le_of_sum_le (fun ρ => norm_nonneg _)
  intro S
  let L := S.filter (fun ρ : NontrivialZetaZero => |ρ.val.im| ≤ 65000)
  let U := S.filter (fun ρ : NontrivialZetaZero => ¬|ρ.val.im| ≤ 65000)
  let ZL : Finset ℂ := L.image (fun ρ => ρ.val)
  let ZU : Finset ℂ := U.image (fun ρ => ρ.val)
  have hZL : ∀ ρ ∈ ZL, RvM.IsNontrivialZero ρ := by
    intro ρ hρ
    obtain ⟨τ, _, rfl⟩ := Finset.mem_image.mp hρ
    exact τ.property
  have hγL : ∀ ρ ∈ ZL, |ρ.im| ≤ 65000 := by
    intro ρ hρ
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hρ
    exact (Finset.mem_filter.mp hτ).2
  have hZU : ∀ ρ ∈ ZU, RvM.IsNontrivialZero ρ := by
    intro ρ hρ
    obtain ⟨τ, _, rfl⟩ := Finset.mem_image.mp hρ
    exact τ.property
  have hγU : ∀ ρ ∈ ZU, 65000 < |ρ.im| := by
    intro ρ hρ
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hρ
    exact lt_of_not_ge (Finset.mem_filter.mp hτ).2
  have hL := TaoFivePrimes.low_zero_reciprocal_weight_65000 ZL hZL hγL
  dsimp [ZL] at hL
  rw [Finset.sum_image (fun a _ b _ he => Subtype.val_injective he)] at hL
  have hU := hweight ZU hZU hγU
  dsimp [ZU] at hU
  rw [Finset.sum_image (fun a _ b _ he => Subtype.val_injective he)] at hU
  have hsumL : (∑ ρ ∈ L, ‖(RvM.zeroMult ρ.val : ℂ) * smoothedZeroKernel a h ρ.val‖) ≤
      Real.sqrt z * (301/10:ℝ) := by
    calc
      _ ≤ ∑ ρ ∈ L, Real.sqrt z * ((RvM.zeroMult ρ.val : ℝ) * (1/|ρ.val.im|)) :=
        Finset.sum_le_sum (fun ρ hρ => hterm_low ρ (Finset.mem_filter.mp hρ).2)
      _ = Real.sqrt z * (∑ ρ ∈ L, (RvM.zeroMult ρ.val : ℝ) * (1/|ρ.val.im|)) := by rw [Finset.mul_sum]
      _ ≤ Real.sqrt z * (301/10:ℝ) := mul_le_mul_of_nonneg_left hL (Real.sqrt_nonneg z)
  have hsumU : (∑ ρ ∈ U, ‖(RvM.zeroMult ρ.val : ℂ) * smoothedZeroKernel a h ρ.val‖) ≤
      (z^(23/8:ℝ)/h^2)*B := by
    calc
      _ ≤ ∑ ρ ∈ U, (z^(23/8:ℝ)/h^2) * ((RvM.zeroMult ρ.val : ℝ) *
          ((min (4*(Real.sin (ρ.val.im*(h/(a+h))/2))^2 + 8*(h/(a+h)) +
            3 * |ρ.val.im| * (h/(a+h))^2) 4) / |ρ.val.im|^3)) :=
        Finset.sum_le_sum (fun ρ hρ => hterm_high ρ (lt_of_not_ge (Finset.mem_filter.mp hρ).2))
      _ = (z^(23/8:ℝ)/h^2) * (∑ ρ ∈ U, (RvM.zeroMult ρ.val : ℝ) *
          ((min (4*(Real.sin (ρ.val.im*(h/(a+h))/2))^2 + 8*(h/(a+h)) +
            3 * |ρ.val.im| * (h/(a+h))^2) 4) / |ρ.val.im|^3)) := by rw [Finset.mul_sum]
      _ ≤ (z^(23/8:ℝ)/h^2)*B := mul_le_mul_of_nonneg_left hU (by positivity)
  have hsplit := Finset.sum_filter_add_sum_filter_not S
    (fun ρ : NontrivialZetaZero => |ρ.val.im| ≤ 65000)
    (fun ρ => ‖(RvM.zeroMult ρ.val : ℂ) * smoothedZeroKernel a h ρ.val‖)
  change (∑ ρ ∈ L, _) + (∑ ρ ∈ U, _) = _ at hsplit
  linarith only [hsumL, hsumU, hsplit]
