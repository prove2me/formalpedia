-- Prove2me | solution 1 for TaoFivePrimes.zeta_zero_free_rectangle_100_101
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-14T03:39:04.386717+00:00
-- url     : https://prove2.me/submissions/3ba05cfc-851f-4898-bbd4-a5f36e34744c

/- First new slice of the existing height-100–1000 RH milestone.
The analytic foundations and proposed Mellin moments are retained from the
ACCEPTED height-14–100 pilot: original proof/certificate sometik179,
theta/Mellin foundations Gabewhigham. New local coefficients are computed
exactly at height 100.5 and will be checked by ordinary Lean proofs. -/
import Theorems.Thm_TaoFivePrimes_rh14to100_moments_enclosed
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option linter.ambiguousOpen false
namespace RH101Proof
open _root_.CertifiedZetaQuadrature
section Height100Module0

open Finset
namespace CertifiedPackedConvolution

end CertifiedPackedConvolution

end Height100Module0

section Height100Module1

set_option autoImplicit false
open Finset
open scoped BigOperators

namespace CertifiedMomentConvolution

end CertifiedMomentConvolution

end Height100Module1

section Height100Module2

open Complex MeasureTheory Finset Metric Set

namespace CertifiedTaylorQuadrature

noncomputable def coefficient (f : ℂ → ℂ) (c : ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n f c / (n.factorial:ℂ)

lemma coefficient_bound (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c : ℂ)
    (R M : ℝ) (hR : 0< R) (hb : ∀ z ∈ sphere c R, ‖f z‖≤ M) (n : ℕ) :
    ‖coefficient f c n‖ ≤  M/R^n := by
  have hd := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR
    hf.diffContOnCl hb
  rw [coefficient, norm_div, Complex.norm_natCast]
  have hn : (0:ℝ)< n.factorial := by positivity
  apply (div_le_iff₀ hn).mpr
  calc
    ‖iteratedDeriv n f c‖ ≤  n.factorial*M/R^n := hd
    _ = M/R^n*n.factorial := by ring

end CertifiedTaylorQuadrature

end Height100Module2

section Height100Module3

set_option autoImplicit false
open Complex Finset
open scoped BigOperators

namespace CertifiedMomentConvolution
open CertifiedTaylorQuadrature

end CertifiedMomentConvolution

end Height100Module3

section Height100Module4

open Complex Finset
namespace CertifiedExponentialJets
open CertifiedTaylorQuadrature CertifiedMomentConvolution

end CertifiedExponentialJets

end Height100Module4

section Height100Module5

open Complex Finset
namespace CertifiedIntegerExponentialJets
open CertifiedMomentConvolution CertifiedExponentialJets

end CertifiedIntegerExponentialJets

end Height100Module5

section Height100Module6

set_option autoImplicit false
open Finset
open scoped BigOperators
namespace CertifiedSignedODEConvolution
open CertifiedIntegerExponentialJets

end CertifiedSignedODEConvolution

end Height100Module6

section Height100Module7

set_option autoImplicit false
namespace CertifiedListODEVectors
open CertifiedSignedODEConvolution
open Finset
open scoped BigOperators

end CertifiedListODEVectors

end Height100Module7

section Height100Module8

set_option autoImplicit false
open Finset
namespace CertifiedPackedHorner
open CertifiedPackedConvolution

end CertifiedPackedHorner

namespace CertifiedPackedHorner

end CertifiedPackedHorner

end Height100Module8

section Height100Module9

open Complex MeasureTheory Set HurwitzZeta Real
open scoped Real

namespace ZetaSix

/-- The Jacobi-theta functional-equation pair underlying Mathlib's completed zeta function. -/
noncomputable def P : WeakFEPair ℂ := hurwitzEvenFEPair 0

lemma evenKernel_zero_eq_F_int {t : ℝ} (ht : 0 < t) :
    evenKernel 0 t = HurwitzKernelBounds.F_int 0 0 t := by
  have h := (hasSum_int_evenKernel 0 ht).tsum_eq
  have h2 : HurwitzKernelBounds.F_int 0 ((0 : ℝ) : UnitAddCircle) t
      = ∑' n : ℤ, HurwitzKernelBounds.f_int 0 0 t n := by
    simp only [HurwitzKernelBounds.F_int, Function.Periodic.lift_coe]
  simp only [QuotientAddGroup.mk_zero] at h2 h
  rw [h2, ← h]
  simp [HurwitzKernelBounds.f_int]

/-- Explicit bound for the theta kernel: `|θ t - 1| ≤  2 e ^ (-π t) / (1 - e ^ (-π t))`. -/
lemma abs_evenKernel_zero_sub_one_le {t : ℝ} (ht : 0 < t) :
    |evenKernel 0 t - 1| ≤  2 * rexp (-π * t) / (1 - rexp (-π * t)) := by
  have h1 := HurwitzKernelBounds.F_nat_zero_zero_sub_le ht
  have h2 := HurwitzKernelBounds.F_nat_zero_le (a := 1) zero_le_one ht
  have h3 : HurwitzKernelBounds.F_int 0 ((0 : ℝ) : UnitAddCircle) t
      = HurwitzKernelBounds.F_nat 0 0 t + HurwitzKernelBounds.F_nat 0 (1 - 0) t :=
    HurwitzKernelBounds.F_int_eq_of_mem_Icc 0 (by simp) ht
  simp only [QuotientAddGroup.mk_zero, sub_zero] at h3
  simp only [Real.norm_eq_abs, one_pow, mul_one] at h1 h2
  rw [evenKernel_zero_eq_F_int ht, h3,
    show HurwitzKernelBounds.F_nat 0 0 t + HurwitzKernelBounds.F_nat 0 1 t - 1
      = (HurwitzKernelBounds.F_nat 0 0 t - 1) + HurwitzKernelBounds.F_nat 0 1 t from by ring]
  calc |_| ≤  |HurwitzKernelBounds.F_nat 0 0 t - 1| + |HurwitzKernelBounds.F_nat 0 1 t| :=
        abs_add_le _ _
    _ ≤  rexp (-π * t) / (1 - rexp (-π * t)) + rexp (-π * t) / (1 - rexp (-π * t)) :=
        add_le_add h1 h2
    _ = 2 * rexp (-π * t) / (1 - rexp (-π * t)) := by ring
/-- The theta functional equation in the form we need. -/
lemma evenKernel_eq_of_pos {t : ℝ} (h0 : 0 < t) :
    evenKernel 0 t = t ^ (-(1 : ℝ) / 2) * evenKernel 0 (1 / t) := by
  have h := evenKernel_functional_equation 0 t
  rw [← evenKernel_eq_cosKernel_of_zero] at h
  rw [h]
  congr 1
  rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_mul h0.le]
  norm_num

lemma f_modif_of_one_lt {t : ℝ} (ht : 1 < t) :
    P.f_modif t = ((evenKernel 0 t : ℝ) : ℂ) - 1 := by
  simp [P, WeakFEPair.f_modif, hurwitzEvenFEPair, ht, not_lt.2 ht.le, Set.indicator_of_notMem]

lemma f_modif_of_lt_one {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    P.f_modif t = ((evenKernel 0 t : ℝ) : ℂ) - ((t ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) := by
  simp [P, WeakFEPair.f_modif, hurwitzEvenFEPair, h0, h1, not_lt.2 h1.le]
  norm_num

lemma f_modif_one : P.f_modif 1 = 0 := by
  simp [P, WeakFEPair.f_modif]

lemma exp_pi_ge_23 : (23 : ℝ) ≤  rexp π := by
  have h1 : (0.7853 : ℝ) < π / 4 := by nlinarith [Real.pi_gt_d4]
  have hp : (0 : ℝ) < π / 4 := by positivity
  have h2 : (2.19 : ℝ) ≤  rexp (π / 4) := by
    have h := Real.sum_le_exp_of_nonneg (x := π / 4) hp.le 6
    simp [Finset.sum_range_succ, Nat.factorial] at h
    nlinarith [h1, pow_pos hp 2, pow_pos hp 3, pow_pos hp 4, pow_pos hp 5]
  have h3 : (rexp (π / 4)) ^ 4 = rexp π := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h4 : (2.19 : ℝ) ^ 4 ≤  (rexp (π / 4)) ^ 4 := by gcongr
  rw [← h3]; nlinarith [h4]

lemma exp_neg_pi_le_23 : rexp (-π) ≤  1 / 23 := by
  have h := exp_pi_ge_23
  have hprod : rexp (-π) * rexp π = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (-π), Real.exp_pos π]

lemma abs_evenKernel_sub_one_le_of_one_le {t : ℝ} (ht : 1 ≤  t) :
    |evenKernel 0 t - 1| ≤  21 / 10 * rexp (-π * t) := by
  have hexp : rexp (-π * t) ≤  rexp (-π) := by
    apply Real.exp_le_exp.2
    nlinarith [Real.pi_pos]
  have h23 : rexp (-π * t) ≤  1 / 23 := le_trans hexp exp_neg_pi_le_23
  have hpos : 0 < rexp (-π * t) := Real.exp_pos _
  have hd : (0 : ℝ) < 1 - rexp (-π * t) := by linarith
  refine (abs_evenKernel_zero_sub_one_le (by linarith)).trans ?_
  rw [div_le_iff₀ hd]
  nlinarith

lemma norm_f_modif_le_of_one_lt {t : ℝ} (ht : 1 < t) :
    ‖P.f_modif t‖ ≤  21 / 10 * rexp (-π * t) := by
  rw [f_modif_of_one_lt ht,
    show ((evenKernel 0 t : ℝ) : ℂ) - 1 = ((evenKernel 0 t - 1 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs]
  exact abs_evenKernel_sub_one_le_of_one_le ht.le

lemma norm_f_modif_le_of_lt_one {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    ‖P.f_modif t‖ ≤  21 / 10 * t ^ (-(1 : ℝ) / 2) * rexp (-π / t) := by
  have ht1 : (1 : ℝ) ≤  1 / t := by rw [le_div_iff₀ h0]; linarith
  have hrpow : (0 : ℝ) < t ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos h0 _
  rw [f_modif_of_lt_one h0 h1,
    show ((evenKernel 0 t : ℝ) : ℂ) - ((t ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)
      = ((evenKernel 0 t - t ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, evenKernel_eq_of_pos h0,
    show t ^ (-(1 : ℝ) / 2) * evenKernel 0 (1 / t) - t ^ (-(1 : ℝ) / 2)
      = t ^ (-(1 : ℝ) / 2) * (evenKernel 0 (1 / t) - 1) from by ring,
    abs_mul, abs_of_pos hrpow, mul_comm (21 / 10 : ℝ), mul_assoc]
  have h := abs_evenKernel_sub_one_le_of_one_le ht1
  rw [show -π * (1 / t) = -π / t by ring] at h
  exact mul_le_mul_of_nonneg_left h hrpow.le

/-- `∫_0^∞ x^k e^{-π x} dx = k! / π^{k+1}`. -/
lemma integral_pow_mul_exp (k : ℕ) :
    (∫ x in Ioi (0 : ℝ), x ^ k * rexp (-π * x)) = (Nat.factorial k) / π ^ (k + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ) + 1) (r := π) (by positivity)
    Real.pi_pos
  have hc : (∫ x in Ioi (0 : ℝ), x ^ ((k : ℝ) + 1 - 1) * rexp (-(π * x)))
      = ∫ x in Ioi (0 : ℝ), x ^ k * rexp (-π * x) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := hx
    rw [show ((k : ℝ) + 1 - 1) = (k : ℝ) by ring, Real.rpow_natCast]
    ring_nf
  rw [hc, Real.Gamma_nat_eq_factorial k,
    show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast] at h
  rw [h, div_pow, one_pow]
  field_simp

lemma integrableOn_pow_mul_exp (k : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ k * rexp (-π * x)) (Ioi 0) := by
  have hg : IntegrableOn (fun y : ℝ => rexp (-y) * y ^ ((k : ℝ) + 1 - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent (by positivity)
  have hs := (integrableOn_Ioi_comp_mul_left_iff
    (fun y : ℝ => rexp (-y) * y ^ ((k : ℝ) + 1 - 1)) 0 Real.pi_pos).mpr (by simpa using hg)
  have hc : IntegrableOn
      (fun x : ℝ => (π ^ k)⁻¹ * (rexp (-(π * x)) * (π * x) ^ ((k : ℝ) + 1 - 1))) (Ioi 0) :=
    hs.const_mul _
  refine hc.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx0 : (0 : ℝ) < x := hx
  dsimp only
  rw [show ((k : ℝ) + 1 - 1) = (k : ℝ) by ring, Real.mul_rpow Real.pi_pos.le hx0.le,
    Real.rpow_natCast, Real.rpow_natCast]
  have hne : (π : ℝ) ^ k ≠ 0 := by positivity
  field_simp

end ZetaSix

end Height100Module9

section Height100Module10

open Real MeasureTheory Set HurwitzZeta HurwitzKernelBounds

namespace TaoZetaBounds

end TaoZetaBounds

end Height100Module10

section Height100Module11

open Real MeasureTheory Set Filter
open scoped Topology

namespace TaoZetaBounds

end TaoZetaBounds

end Height100Module11

section Height100Module12

open Real MeasureTheory Set Filter Finset HurwitzZeta HurwitzKernelBounds

namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature
open TaoZetaBounds

end CertifiedZetaQuadrature

end Height100Module12

section Height100Module13

open Complex Finset Metric

namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module13

section Height100Module14

open Real MeasureTheory Set Filter HurwitzZeta
namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module14

section Height100Module15

open Complex MeasureTheory Metric Set Finset
namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module15

section Height100Module16

open Real MeasureTheory Set Filter Finset
namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module16

section Height100Module17

open Complex MeasureTheory Set HurwitzZeta Real
open scoped Real
set_option autoImplicit false
set_option exponentiation.threshold 1024
set_option maxRecDepth 10000

namespace TaoZetaWide256
open ZetaSix

noncomputable def maj (t : ℝ) : ℝ :=
  if t ≤  1 then 21 / 10 * (t ^ (-130 : ℝ) * rexp (-π / t))
  else 21 / 10 * (t ^ (128 : ℝ) * rexp (-π * t))

lemma integrableOn_outer :
    IntegrableOn (fun t : ℝ => t ^ (128 : ℝ) * rexp (-π * t)) (Ioi 1) := by
  simpa only [Real.rpow_ofNat] using
    (ZetaSix.integrableOn_pow_mul_exp 128).mono_set (Ioi_subset_Ioi zero_le_one)

lemma outer_le :
    (∫ t in Ioi (1 : ℝ), t ^ (128 : ℝ) * rexp (-π * t)) ≤  ((10^155) : ℝ) / (21 / 10) := by
  have h := MeasureTheory.setIntegral_mono_set
    (ZetaSix.integrableOn_pow_mul_exp 128)
    (Filter.Eventually.of_forall (fun x : ℝ => by positivity :
      ∀ x : ℝ, 0 ≤  x ^ 128 * rexp (-π * x)))
    (Filter.Eventually.of_forall (Ioi_subset_Ioi (show (0 : ℝ) ≤  1 by norm_num)))
  simp only [Real.rpow_ofNat] at *
  rw [ZetaSix.integral_pow_mul_exp] at h
  have hp : (3 : ℝ) ^ 129 ≤  π ^ 129 := pow_le_pow_left₀ (by norm_num) Real.pi_gt_three.le 129
  have hpi : (0 : ℝ) < π ^ 129 := by positivity
  have hb : (Nat.factorial 128 : ℝ) / π ^ 129 ≤  (10^155) / (21 / 10) := by
    rw [div_le_iff₀ hpi]
    norm_num [Nat.factorial] at *
    nlinarith
  exact h.trans hb

/-- The kernel of the substituted integral: `u^{-1/2} e^{-π u}` cut off below `1`. -/
private noncomputable def gInd : ℝ → ℝ :=
  Set.indicator (Ioi 1) fun u => u ^ (128 : ℝ) * rexp (-π * u)

private lemma gInd_integrableOn : IntegrableOn gInd (Ioi (0 : ℝ)) := by
  rw [gInd]
  exact (integrableOn_outer.integrable_indicator measurableSet_Ioi).integrableOn

private lemma integral_gInd : (∫ y in Ioi (0 : ℝ), gInd y)
    = ∫ u in Ioi (1 : ℝ), u ^ (128 : ℝ) * rexp (-π * u) := by
  rw [gInd, MeasureTheory.integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, Set.Ioi_inter_Ioi]
  norm_num

private lemma cov_ptwise (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
    (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • gInd (x ^ (-1 : ℝ))
      = (Ioo (0 : ℝ) 1).indicator (fun x => x ^ (-130 : ℝ) * rexp (-π / x)) x := by
  have hx0 : 0 < x := hx
  have hinv : x ^ (-1 : ℝ) = x⁻¹ := by rw [Real.rpow_neg_one]
  rcases lt_or_ge x 1 with h | h
  · have h1 : (1 : ℝ) < x⁻¹ := by rw [lt_inv_comm₀ (by norm_num) hx0]; simpa using h
    rw [Set.indicator_of_mem (show x ∈ Ioo (0 : ℝ) 1 from ⟨hx0, h⟩), gInd, hinv,
      Set.indicator_of_mem (mem_Ioi.mpr h1)]
    have hd : -π * x⁻¹ = -π / x := by field_simp
    have hpow : (x⁻¹) ^ (128 : ℝ) = x ^ (-128 : ℝ) := by
      rw [← Real.rpow_neg_one x, ← Real.rpow_mul hx0.le]
      norm_num
    rw [hd, hpow, smul_eq_mul]
    have hxx : x ^ ((-1 : ℝ) - 1) * x ^ (-128 : ℝ) = x ^ (-130 : ℝ) := by
      rw [← Real.rpow_add hx0]
      norm_num
    rw [show |(-1 : ℝ)| = 1 by norm_num, one_mul, ← mul_assoc, hxx]
  · have h1 : x⁻¹ ≤  1 := by rw [inv_le_one_iff₀]; right; exact h
    rw [Set.indicator_of_notMem (by simp; intro _; exact h), gInd, hinv,
      Set.indicator_of_notMem (by simp [not_lt.2 h1])]
    simp

lemma integrableOn_inner :
    IntegrableOn (fun x : ℝ => x ^ (-130 : ℝ) * rexp (-π / x)) (Ioc (0 : ℝ) 1) := by
  have h1 : IntegrableOn
      (fun x : ℝ => (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • gInd (x ^ (-1 : ℝ))) (Ioi 0) :=
    (MeasureTheory.integrableOn_Ioi_comp_rpow_iff gInd (by norm_num : (-1 : ℝ) ≠ 0)).mpr
      gInd_integrableOn
  have h2 : IntegrableOn
      ((Ioo (0 : ℝ) 1).indicator fun x => x ^ (-130 : ℝ) * rexp (-π / x)) (Ioi 0) :=
    h1.congr_fun cov_ptwise measurableSet_Ioi
  have h3 := (MeasureTheory.integrable_indicator_iff measurableSet_Ioo).mp h2
  rw [IntegrableOn, Measure.restrict_restrict measurableSet_Ioo,
    show Ioo (0 : ℝ) 1 ∩ Ioi 0 = Ioo (0 : ℝ) 1 by
      ext x; simp only [mem_inter_iff, mem_Ioo, mem_Ioi]; tauto] at h3
  rw [IntegrableOn, ← MeasureTheory.Measure.restrict_congr_set
    (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := 1))]
  exact h3

lemma integral_inner : (∫ x in Ioc (0 : ℝ) 1, x ^ (-130 : ℝ) * rexp (-π / x))
    = ∫ u in Ioi (1 : ℝ), u ^ (128 : ℝ) * rexp (-π * u) := by
  have hcov := MeasureTheory.integral_comp_rpow_Ioi gInd (by norm_num : (-1 : ℝ) ≠ 0)
  rw [integral_gInd] at hcov
  rw [setIntegral_congr_fun measurableSet_Ioi cov_ptwise] at hcov
  rw [MeasureTheory.integral_indicator measurableSet_Ioo, Measure.restrict_restrict
    measurableSet_Ioo, show Ioo (0 : ℝ) 1 ∩ Ioi 0 = Ioo (0 : ℝ) 1 by
      ext x; simp only [mem_inter_iff, mem_Ioo, mem_Ioi]; tauto] at hcov
  rw [← MeasureTheory.Measure.restrict_congr_set (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := 1))]
  exact hcov

lemma integrableOn_maj_Ioc : IntegrableOn maj (Ioc (0 : ℝ) 1) := by
  have h : IntegrableOn (fun x : ℝ => 21 / 10 * (x ^ (-130 : ℝ) * rexp (-π / x)))
      (Ioc (0 : ℝ) 1) := integrableOn_inner.const_mul (21 / 10)
  refine h.congr_fun ?_ measurableSet_Ioc
  intro t ht
  simp [maj, ht.2]

lemma integrableOn_maj_Ioi : IntegrableOn maj (Ioi (1 : ℝ)) := by
  have h : IntegrableOn (fun t : ℝ => 21 / 10 * (t ^ (128 : ℝ) * rexp (-π * t)))
      (Ioi (1 : ℝ)) := integrableOn_outer.const_mul (21 / 10)
  refine h.congr_fun ?_ measurableSet_Ioi
  intro t ht
  simp [maj, not_le.2 (mem_Ioi.mp ht)]

lemma integrableOn_maj : IntegrableOn maj (Ioi 0) := by
  rw [show Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 from (Ioc_union_Ioi_eq_Ioi zero_le_one).symm]
  exact integrableOn_maj_Ioc.union integrableOn_maj_Ioi

lemma integral_maj_le : ∫ t in Ioi (0 : ℝ), maj t ≤  (2*10^155) := by
  have hsplit : ∫ t in Ioi (0 : ℝ), maj t
      = (∫ t in Ioc (0 : ℝ) 1, maj t) + ∫ t in Ioi (1 : ℝ), maj t := by
    rw [show Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 from (Ioc_union_Ioi_eq_Ioi zero_le_one).symm]
    exact setIntegral_union (by simp [Set.disjoint_left]) measurableSet_Ioi
      integrableOn_maj_Ioc integrableOn_maj_Ioi
  have h1 : ∫ t in Ioc (0 : ℝ) 1, maj t
      = 21 / 10 * ∫ u in Ioi (1 : ℝ), u ^ (128 : ℝ) * rexp (-π * u) := by
    rw [setIntegral_congr_fun measurableSet_Ioc
      (g := fun t : ℝ => 21 / 10 * (t ^ (-130 : ℝ) * rexp (-π / t)))
      (fun t ht => by simp [maj, ht.2]), integral_const_mul, integral_inner]
  have h2 : ∫ t in Ioi (1 : ℝ), maj t
      = 21 / 10 * ∫ u in Ioi (1 : ℝ), u ^ (128 : ℝ) * rexp (-π * u) := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (g := fun t : ℝ => 21 / 10 * (t ^ (128 : ℝ) * rexp (-π * t)))
      (fun t ht => by simp [maj, not_le.2 (mem_Ioi.mp ht)]), integral_const_mul]
  rw [hsplit, h1, h2]
  have hJ := outer_le
  linarith

lemma norm_integrand_le {s : ℂ} (h0 : -256 ≤  s.re) (h1 : s.re ≤  257) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (s / 2 - 1) • P.f_modif t‖ ≤  maj t := by
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
    show (s / 2 - 1).re = s.re / 2 - 1 by simp]
  rcases lt_trichotomy t 1 with hlt | rfl | hgt
  · have hmaj : maj t = 21 / 10 * (t ^ (-130 : ℝ) * rexp (-π / t)) := by simp [maj, hlt.le]
    rw [hmaj]
    have hstep : t ^ (s.re / 2 - 1) * ‖P.f_modif t‖
        ≤  t ^ (s.re / 2 - 1) * (21 / 10 * t ^ (-(1 : ℝ) / 2) * rexp (-π / t)) :=
      mul_le_mul_of_nonneg_left (norm_f_modif_le_of_lt_one ht hlt) (Real.rpow_nonneg ht.le _)
    refine hstep.trans ?_
    have hcomb : t ^ (s.re / 2 - 1) * (21 / 10 * t ^ (-(1 : ℝ) / 2) * rexp (-π / t))
        = 21 / 10 * (t ^ (s.re / 2 - 3 / 2) * rexp (-π / t)) := by
      rw [show s.re / 2 - 3 / 2 = (s.re / 2 - 1) + (-(1 : ℝ) / 2) by ring, Real.rpow_add ht]
      ring
    rw [hcomb]
    have hexp : t ^ (s.re / 2 - 3 / 2) ≤  t ^ (-130 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge ht hlt.le (by linarith)
    have hnn : (0 : ℝ) ≤  rexp (-π / t) := (Real.exp_pos _).le
    nlinarith [Real.rpow_pos_of_pos ht (-130 : ℝ), Real.rpow_pos_of_pos ht (s.re / 2 - 3 / 2)]
  · have hm : maj (1 : ℝ) = 21 / 10 * ((1 : ℝ) ^ (-130 : ℝ) * rexp (-π / 1)) := if_pos le_rfl
    rw [hm, f_modif_one]
    simp only [norm_zero, mul_zero]
    positivity
  · have hmaj : maj t = 21 / 10 * (t ^ (128 : ℝ) * rexp (-π * t)) := by
      simp [maj, not_le.2 hgt]
    rw [hmaj]
    have hstep : t ^ (s.re / 2 - 1) * ‖P.f_modif t‖
        ≤  t ^ (s.re / 2 - 1) * (21 / 10 * rexp (-π * t)) :=
      mul_le_mul_of_nonneg_left (norm_f_modif_le_of_one_lt hgt) (Real.rpow_nonneg ht.le _)
    refine hstep.trans ?_
    have hexp : t ^ (s.re / 2 - 1) ≤  t ^ (128 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hgt.le (by linarith)
    have hnn : (0 : ℝ) ≤  rexp (-π * t) := (Real.exp_pos _).le
    nlinarith [Real.rpow_pos_of_pos ht (128 : ℝ), Real.rpow_pos_of_pos ht (s.re / 2 - 1)]

/-- **Sharpened bound on the entire part of the completed zeta function.**
In the critical strip, `‖Λ₀ s‖ ≤  (10^155)`. -/
theorem norm_completedRiemannZeta₀_le {s : ℂ} (h0 : -256 ≤  s.re) (h1 : s.re ≤  257) :
    ‖completedRiemannZeta₀ s‖ ≤  (10^155) := by
  have hdef : completedRiemannZeta₀ s = mellin P.f_modif (s / 2) / 2 := rfl
  rw [hdef, norm_div, Complex.norm_ofNat]
  have hb : ‖mellin P.f_modif (s / 2)‖ ≤  ∫ t in Ioi (0 : ℝ), maj t := by
    rw [mellin]
    refine norm_integral_le_of_norm_le integrableOn_maj ?_
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0 : ℝ)))] with t ht
    exact norm_integrand_le h0 h1 ht
  have := hb.trans integral_maj_le
  linarith

end TaoZetaWide256

end Height100Module17

section Height100Module18

open Complex Finset Metric
open scoped BigOperators
set_option autoImplicit false
set_option exponentiation.threshold 1024

namespace TaoZetaGlobal

lemma norm_iteratedDeriv_completedZeta (n : ℕ) :
    ‖iteratedDeriv n completedRiemannZeta₀ (1 / 2)‖ ≤ 
      n.factorial * (10^155) / (256 : ℝ) ^ n := by
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (by norm_num)
    differentiable_completedZeta₀.diffContOnCl
  intro z hz
  have habs : |z.re - 1 / 2| ≤  (256 : ℝ) := by
    have h := Complex.abs_re_le_norm (z - (1 / 2 : ℂ))
    rw [mem_sphere_iff_norm.mp hz] at h
    simpa using h
  apply TaoZetaWide256.norm_completedRiemannZeta₀_le <;> linarith [(abs_le.mp habs).1, (abs_le.mp habs).2]

noncomputable def taylorTerm (z : ℂ) (n : ℕ) : ℂ :=
  (n.factorial : ℂ)⁻¹ • (z - 1 / 2) ^ n •
    iteratedDeriv n completedRiemannZeta₀ (1 / 2)

lemma norm_taylorTerm_le (z : ℂ) (n : ℕ) :
    ‖taylorTerm z n‖ ≤  (10^155) * (‖z - 1 / 2‖ / 256) ^ n := by
  have h := norm_iteratedDeriv_completedZeta n
  have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
  unfold taylorTerm
  simp only [norm_smul, norm_inv, Complex.norm_natCast, norm_pow]
  calc
    (n.factorial : ℝ)⁻¹ * (‖z - 1 / 2‖ ^ n *
        ‖iteratedDeriv n completedRiemannZeta₀ (1 / 2)‖) ≤ 
      (n.factorial : ℝ)⁻¹ * (‖z - 1 / 2‖ ^ n *
        (n.factorial * (10^155) / (256 : ℝ) ^ n)) := by gcongr
    _ = (10^155) * (‖z - 1 / 2‖ / 256) ^ n := by
      rw [div_pow]
      field_simp

/-- A uniform certified truncation bound, with no assumptions about computed coefficients. -/
lemma norm_taylor_remainder_le (z : ℂ) (hz : ‖z - 1 / 2‖ < 256) (N : ℕ) :
    ‖completedRiemannZeta₀ z - ∑ n ∈ range N, taylorTerm z n‖ ≤ 
      (10^155) * (‖z - 1 / 2‖ / 256) ^ N / (1 - ‖z - 1 / 2‖ / 256) := by
  let q : ℝ := ‖z - 1 / 2‖ / 256
  have hq0 : 0 ≤  q := by positivity
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hs : HasSum (taylorTerm z) (completedRiemannZeta₀ z) :=
    Complex.hasSum_taylorSeries_of_entire differentiable_completedZeta₀ (1 / 2) z
  have htail : completedRiemannZeta₀ z - ∑ n ∈ range N, taylorTerm z n =
      ∑' n : ℕ, taylorTerm z (n + N) := by
    have h := hs.summable.sum_add_tsum_nat_add N
    rw [hs.tsum_eq] at h
    apply sub_eq_iff_eq_add.mpr
    simpa [add_comm] using h.symm
  rw [htail]
  have hgeo : HasSum (fun n : ℕ => ((10^155) * q ^ N) * q ^ n)
      (((10^155) * q ^ N) * (1 - q)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0 hq1).mul_left ((10^155) * q ^ N)
  have hbound := tsum_of_norm_bounded hgeo (fun n : ℕ => by
    calc ‖taylorTerm z (n + N)‖ ≤  (10^155) * q ^ (n + N) := norm_taylorTerm_le z (n + N)
      _ = ((10^155) * q ^ N) * q ^ n := by rw [pow_add]; ring)
  simpa only [q, div_eq_mul_inv] using hbound

lemma norm_taylor_remainder_512 (z : ℂ) (hz : ‖z - 1 / 2‖ ≤  104) :
    ‖completedRiemannZeta₀ z - ∑ n ∈ range 512, taylorTerm z n‖ ≤  1 / 10 ^ 45 := by
  have hr := norm_taylor_remainder_le z (by linarith) 512
  have hq : ‖z - 1 / 2‖ / 256 ≤  (13 / 32 : ℝ) := by linarith
  have hq0 : 0 ≤  ‖z - 1 / 2‖ / 256 := by positivity
  apply hr.trans
  calc
    (10^155) * (‖z - 1 / 2‖ / 256) ^ 512 / (1 - ‖z - 1 / 2‖ / 256) ≤ 
        (10^155) * (13 / 32 : ℝ) ^ 512 / (1 - 13 / 32) := by
      gcongr
    _ ≤  1 / 10 ^ 45 := by norm_num

end TaoZetaGlobal

end Height100Module18

section Height100Module19

open Complex MeasureTheory Set Filter Asymptotics
open scoped Topology
set_option autoImplicit false

namespace TaoZetaCertificate

noncomputable def logKernel : ℕ → ℝ → ℂ
  | 0 => ZetaSix.P.f_modif
  | n + 1 => fun t => Real.log t • logKernel n t

lemma logKernel_eq (n : ℕ) (t : ℝ) :
    logKernel n t = (Real.log t) ^ n • ZetaSix.P.f_modif t := by
  induction n with
  | zero => simp [logKernel]
  | succ n ih => simp only [logKernel, ih, pow_succ]; rw [smul_smul]; congr 1; ring

lemma logKernel_locallyIntegrable (n : ℕ) :
    LocallyIntegrableOn (logKernel n) (Ioi 0) := by
  induction n with
  | zero => exact ZetaSix.P.hf_modif_int
  | succ n ih =>
    exact MeasureTheory.LocallyIntegrableOn.continuousOn_smul isOpen_Ioi.isLocallyClosed ih
      (fun t ht => (Real.continuousAt_log (ne_of_gt ht)).continuousWithinAt)

lemma logKernel_top (n : ℕ) (r : ℝ) :
    logKernel n =O[atTop] (fun t : ℝ => t ^ r) := by
  induction n generalizing r with
  | zero =>
    exact ZetaSix.P.isStrongFEPair_toStrongFEPair.hf_top r
  | succ n ih =>
    have h := isBigO_rpow_top_log_smul (a := -(r - 1)) (b := -r) (by linarith)
      (by simpa only [neg_neg] using ih (r - 1))
    simpa only [neg_neg, logKernel] using h

lemma logKernel_zero (n : ℕ) (r : ℝ) :
    logKernel n =O[𝓝[>] 0] (fun t : ℝ => t ^ r) := by
  induction n generalizing r with
  | zero =>
    exact ZetaSix.P.isStrongFEPair_toStrongFEPair.hf_zero r
  | succ n ih =>
    have h := isBigO_rpow_zero_log_smul (a := -(r + 1)) (b := -r) (by linarith)
      (by simpa only [neg_neg] using ih (r + 1))
    simpa only [neg_neg, logKernel] using h

lemma logKernel_mellin_hasDerivAt (n : ℕ) (s : ℂ) :
    HasDerivAt (mellin (logKernel n)) (mellin (logKernel (n + 1)) s) s := by
  exact (mellin_hasDerivAt_of_isBigO_rpow (logKernel_locallyIntegrable n)
    (logKernel_top n (-(s.re + 1))) (by linarith)
    (logKernel_zero n (-(s.re - 1))) (by linarith)).2

lemma logKernel_mellin_convergent (n : ℕ) (s : ℂ) :
    MellinConvergent (logKernel n) s := by
  exact mellinConvergent_of_isBigO_rpow (logKernel_locallyIntegrable n)
    (logKernel_top n (-(s.re + 1))) (by linarith)
    (logKernel_zero n (-(s.re - 1))) (by linarith)

lemma iteratedDeriv_mellin_kernel (n : ℕ) :
    iteratedDeriv n (mellin ZetaSix.P.f_modif) = mellin (logKernel n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    exact funext fun s => (logKernel_mellin_hasDerivAt n s).deriv

lemma completedZeta_derivative_moment (n : ℕ) (s : ℂ) :
    iteratedDeriv n completedRiemannZeta₀ s =
      mellin (logKernel n) (s / 2) / (2 : ℂ) ^ (n + 1) := by
  have hf : Differentiable ℂ (mellin ZetaSix.P.f_modif) :=
    fun s => (logKernel_mellin_hasDerivAt 0 s).differentiableAt
  have he : completedRiemannZeta₀ =
      (fun s : ℂ => mellin ZetaSix.P.f_modif ((1 / 2 : ℂ) * s) / 2) := by
    ext z
    change mellin ZetaSix.P.f_modif (z / 2) / 2 = _
    congr 2
    ring
  rw [he, iteratedDeriv_div_const]
  rw [iteratedDeriv_comp_const_mul hf.contDiff, iteratedDeriv_mellin_kernel]
  have hs : (1 / 2 : ℂ) * s = s / 2 := by ring
  dsimp only
  rw [hs]
  rw [pow_succ, div_pow, one_pow]
  field_simp

end TaoZetaCertificate

end Height100Module19

section Height100Module20

open Complex MeasureTheory Set HurwitzZeta
set_option autoImplicit false

namespace TaoZetaCertificate

noncomputable def momentIntegrand (n : ℕ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ ((1 / 4 : ℂ) - 1) • logKernel (2 * n) t

noncomputable def outerIntegrand (n : ℕ) (t : ℝ) : ℂ :=
  ((t ^ (-3 / 4 : ℝ) * Real.log t ^ (2 * n) * (evenKernel 0 t - 1) : ℝ) : ℂ)

lemma momentIntegrand_outer (n : ℕ) {t : ℝ} (ht : 1 < t) :
    momentIntegrand n t = outerIntegrand n t := by
  have ht0 : 0 ≤  t := by linarith
  unfold momentIntegrand outerIntegrand
  rw [logKernel_eq, ZetaSix.f_modif_of_one_lt ht]
  have he : (1 / 4 : ℂ) - 1 = ((-3 / 4 : ℝ) : ℂ) := by norm_num
  rw [he, ← Complex.ofReal_cpow ht0]
  simp only [Complex.real_smul, smul_eq_mul]
  push_cast
  ring

lemma momentIntegrand_inner (n : ℕ) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    momentIntegrand n t =
      ((t ^ (-5 / 4 : ℝ) * Real.log t ^ (2 * n) *
        (evenKernel 0 (1 / t) - 1) : ℝ) : ℂ) := by
  unfold momentIntegrand
  rw [logKernel_eq, ZetaSix.f_modif_of_lt_one ht ht1, ZetaSix.evenKernel_eq_of_pos ht]
  have he : (1 / 4 : ℂ) - 1 = ((-3 / 4 : ℝ) : ℂ) := by norm_num
  rw [he, ← Complex.ofReal_cpow ht.le]
  have hpow : t ^ (-5 / 4 : ℝ) = t ^ (-3 / 4 : ℝ) * t ^ (-(1 : ℝ) / 2) := by
    rw [← Real.rpow_add ht]
    norm_num
  rw [hpow]
  simp only [Complex.real_smul, smul_eq_mul]
  push_cast
  ring

private noncomputable def outerIndicator (n : ℕ) : ℝ → ℂ :=
  (Ioi 1).indicator (outerIntegrand n)

private lemma integral_outerIndicator (n : ℕ) :
    (∫ t in Ioi (0 : ℝ), outerIndicator n t) = ∫ t in Ioi 1, outerIntegrand n t := by
  rw [outerIndicator, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, Ioi_inter_Ioi]
  norm_num

private lemma reciprocal_integrand (n : ℕ) (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
    (|(-1 : ℝ)| * t ^ ((-1 : ℝ) - 1)) • outerIndicator n (t ^ (-1 : ℝ)) =
      (Ioo (0 : ℝ) 1).indicator (momentIntegrand n) t := by
  have ht0 : 0 < t := ht
  rw [Real.rpow_neg_one]
  rcases lt_or_ge t 1 with h | h
  · have hinv : 1 < t⁻¹ := by rw [lt_inv_comm₀ (by norm_num) ht0]; simpa using h
    rw [indicator_of_mem (show t ∈ Ioo (0 : ℝ) 1 from ⟨ht0, h⟩),
      outerIndicator, indicator_of_mem (show t⁻¹ ∈ Ioi (1 : ℝ) from hinv), momentIntegrand_inner n ht0 h]
    unfold outerIntegrand
    have hpow : (t⁻¹) ^ (-3 / 4 : ℝ) = t ^ (3 / 4 : ℝ) := by
      rw [← Real.rpow_neg_one t, ← Real.rpow_mul ht0.le]
      norm_num
    have hlog : Real.log (t⁻¹) ^ (2 * n) = Real.log t ^ (2 * n) := by
      rw [Real.log_inv, Even.neg_pow (even_two_mul n)]
    rw [hpow, hlog]
    have he : t ^ (-2 : ℝ) * t ^ (3 / 4 : ℝ) = t ^ (-(5 / 4) : ℝ) := by
      rw [← Real.rpow_add ht0]
      norm_num
    norm_num only [abs_neg, abs_one, one_mul]
    rw [Complex.real_smul]
    push_cast
    rw [← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul, he]
    simp only [one_div]
  · have hinv : t⁻¹ ≤  1 := by rw [inv_le_one_iff₀]; right; exact h
    rw [indicator_of_notMem (by simp; intro _; exact h), outerIndicator,
      indicator_of_notMem (by simpa using not_lt.mpr hinv)]
    simp

lemma integral_moment_inner (n : ℕ) :
    (∫ t in Ioc (0 : ℝ) 1, momentIntegrand n t) = ∫ t in Ioi 1, outerIntegrand n t := by
  have h := integral_comp_rpow_Ioi (outerIndicator n) (by norm_num : (-1 : ℝ) ≠ 0)
  rw [integral_outerIndicator, setIntegral_congr_fun measurableSet_Ioi (reciprocal_integrand n)] at h
  rw [integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
    show Ioo (0 : ℝ) 1 ∩ Ioi 0 = Ioo (0 : ℝ) 1 by ext t; simp; tauto] at h
  rw [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := 1))]
  exact h

lemma mellin_even_moment_folded (n : ℕ) :
    mellin (logKernel (2 * n)) (1 / 4) = 2 * ∫ t in Ioi 1, outerIntegrand n t := by
  have hi : IntegrableOn (momentIntegrand n) (Ioi (0 : ℝ)) :=
    logKernel_mellin_convergent (2 * n) (1 / 4)
  have hi0 := hi.mono_set (Ioc_subset_Ioi_self : Ioc (0 : ℝ) 1 ⊆ Ioi 0)
  have hi1 := hi.mono_set (Ioi_subset_Ioi (show (0 : ℝ) ≤  1 by norm_num))
  change (∫ t in Ioi (0 : ℝ), momentIntegrand n t) = _
  rw [show Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 from (Ioc_union_Ioi_eq_Ioi zero_le_one).symm]
  rw [setIntegral_union (by simp [Set.disjoint_left]) measurableSet_Ioi hi0 hi1,
    integral_moment_inner n,
    setIntegral_congr_fun measurableSet_Ioi (fun t ht => momentIntegrand_outer n ht)]
  ring

lemma even_derivative_moment_folded (n : ℕ) :
    iteratedDeriv (2 * n) completedRiemannZeta₀ (1 / 2) =
      (∫ t in Ioi 1, outerIntegrand n t) / (2 : ℂ) ^ (2 * n) := by
  rw [completedZeta_derivative_moment]
  have hc : (1 / 2 : ℂ) / 2 = 1 / 4 := by norm_num
  rw [hc, mellin_even_moment_folded, pow_succ]
  field_simp

end TaoZetaCertificate

end Height100Module20

section Height100Module21

open Complex MeasureTheory Set
open scoped ComplexConjugate
set_option autoImplicit false

namespace TaoZetaCertificate

lemma odd_taylor_derivative_zero (n : ℕ) :
    iteratedDeriv (2 * n + 1) completedRiemannZeta₀ (1 / 2) = 0 := by
  have hf : (fun z => completedRiemannZeta₀ (1 - z)) = completedRiemannZeta₀ :=
    funext completedRiemannZeta₀_one_sub
  have h := congrFun (congrArg (iteratedDeriv (2 * n + 1)) hf) (1 / 2)
  rw [iteratedDeriv_comp_const_sub] at h
  norm_num [pow_add, pow_mul] at h
  linear_combination -h / 2

end TaoZetaCertificate

end Height100Module21

section Height100Module22

open Complex Finset Metric Filter
namespace CertifiedComplexTaylor
open CertifiedTaylorQuadrature

noncomputable def polynomial (f : ℂ → ℂ) (c : ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ range N, coefficient f c n*(z-c)^n
noncomputable def remainder (f : ℂ → ℂ) (c : ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  f z-polynomial f c N z

lemma series_sum (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c z : ℂ) :
    HasSum (fun n : ℕ => coefficient f c n*(z-c)^n) (f z) := by
  have h := Complex.hasSum_taylorSeries_of_entire hf c z
  convert! h using 1
  ext n
  simp only [coefficient,smul_eq_mul]
  ring

lemma remainder_eq_tsum (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c z : ℂ) (N : ℕ) :
    remainder f c N z = ∑' n : ℕ, coefficient f c (n+N)*(z-c)^(n+N) := by
  have hs := series_sum f hf c z
  have h := hs.summable.sum_add_tsum_nat_add N
  rw [hs.tsum_eq] at h
  unfold remainder polynomial
  apply sub_eq_iff_eq_add.mpr
  simpa [add_comm] using h.symm

lemma remainder_bound (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c : ℂ)
    (R M r : ℝ) (hR : 0< R) (hM : 0≤ M) (hr : 0≤ r) (hrR : r< R)
    (hb : ∀ z ∈ sphere c R, ‖f z‖≤ M) (N : ℕ) (z : ℂ) (hz : ‖z-c‖≤ r) :
    ‖remainder f c N z‖≤ M*(r/R)^N/(1-r/R) := by
  have hq0 : 0≤ r/R := div_nonneg hr hR.le
  have hq1 : r/R<1 := (div_lt_one hR).mpr hrR
  rw [remainder_eq_tsum f hf c z N]
  have hgeo := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (M*(r/R)^N)
  have hterms : ∀ n : ℕ, ‖coefficient f c (n+N)*(z-c)^(n+N)‖ ≤  (M*(r/R)^N)*(r/R)^n := by
    intro n
    rw [norm_mul,norm_pow]
    calc
      _ ≤  (M/R^(n+N))*r^(n+N) := by
        gcongr
        exact coefficient_bound f hf c R M hR hb (n+N)
      _ = _ := by rw [div_pow,div_pow,pow_add,pow_add]; ring
  simpa only [div_eq_mul_inv] using tsum_of_norm_bounded hgeo hterms

lemma coefficient_sub (f g : ℂ → ℂ) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (c : ℂ) (n : ℕ) :
    coefficient (fun z => f z-g z) c n = coefficient f c n-coefficient g c n := by
  unfold coefficient
  change iteratedDeriv n (f-g) c/(n.factorial:ℂ)=_
  rw [iteratedDeriv_sub hf.contDiff.contDiffAt hg.contDiff.contDiffAt,sub_div]

/-- Uniform global approximation on one circle transfers to every local Taylor coefficient. -/
lemma coefficient_error (f g : ℂ → ℂ) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (c : ℂ) (R δ : ℝ) (hR : 0< R) (hb : ∀ z ∈ sphere c R, ‖f z-g z‖≤ δ) (n : ℕ) :
    ‖coefficient f c n-coefficient g c n‖≤ δ/R^n := by
  rw [← coefficient_sub f g hf hg]
  exact coefficient_bound _ (hf.sub hg) c R δ hR hb n

end CertifiedComplexTaylor

end Height100Module22

section Height100Module23

open Complex MeasureTheory Set HurwitzZeta Real
open scoped Real
set_option autoImplicit false

namespace TaoZetaWide
open ZetaSix

noncomputable def maj (t : ℝ) : ℝ :=
  if t ≤  1 then 21 / 10 * (t ^ (-14 : ℝ) * rexp (-π / t))
  else 21 / 10 * (t ^ (12 : ℝ) * rexp (-π * t))

lemma integrableOn_outer :
    IntegrableOn (fun t : ℝ => t ^ (12 : ℝ) * rexp (-π * t)) (Ioi 1) := by
  simpa only [Real.rpow_ofNat] using
    (ZetaSix.integrableOn_pow_mul_exp 12).mono_set (Ioi_subset_Ioi zero_le_one)

lemma outer_le :
    (∫ t in Ioi (1 : ℝ), t ^ (12 : ℝ) * rexp (-π * t)) ≤  (640 : ℝ) / (21 / 10) := by
  have h := MeasureTheory.setIntegral_mono_set
    (ZetaSix.integrableOn_pow_mul_exp 12)
    (Filter.Eventually.of_forall (fun x : ℝ => by positivity :
      ∀ x : ℝ, 0 ≤  x ^ 12 * rexp (-π * x)))
    (Filter.Eventually.of_forall (Ioi_subset_Ioi (show (0 : ℝ) ≤  1 by norm_num)))
  simp only [Real.rpow_ofNat] at *
  rw [ZetaSix.integral_pow_mul_exp] at h
  have hp : (3 : ℝ) ^ 13 ≤  π ^ 13 := pow_le_pow_left₀ (by norm_num) Real.pi_gt_three.le 13
  have hpi : (0 : ℝ) < π ^ 13 := by positivity
  have hb : (Nat.factorial 12 : ℝ) / π ^ 13 ≤  640 / (21 / 10) := by
    rw [div_le_iff₀ hpi]
    norm_num [Nat.factorial] at *
    nlinarith
  exact h.trans hb

/-- The kernel of the substituted integral: `u^{-1/2} e^{-π u}` cut off below `1`. -/
private noncomputable def gInd : ℝ → ℝ :=
  Set.indicator (Ioi 1) fun u => u ^ (12 : ℝ) * rexp (-π * u)

private lemma gInd_integrableOn : IntegrableOn gInd (Ioi (0 : ℝ)) := by
  rw [gInd]
  exact (integrableOn_outer.integrable_indicator measurableSet_Ioi).integrableOn

private lemma integral_gInd : (∫ y in Ioi (0 : ℝ), gInd y)
    = ∫ u in Ioi (1 : ℝ), u ^ (12 : ℝ) * rexp (-π * u) := by
  rw [gInd, MeasureTheory.integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, Set.Ioi_inter_Ioi]
  norm_num

private lemma cov_ptwise (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
    (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • gInd (x ^ (-1 : ℝ))
      = (Ioo (0 : ℝ) 1).indicator (fun x => x ^ (-14 : ℝ) * rexp (-π / x)) x := by
  have hx0 : 0 < x := hx
  have hinv : x ^ (-1 : ℝ) = x⁻¹ := by rw [Real.rpow_neg_one]
  rcases lt_or_ge x 1 with h | h
  · have h1 : (1 : ℝ) < x⁻¹ := by rw [lt_inv_comm₀ (by norm_num) hx0]; simpa using h
    rw [Set.indicator_of_mem (show x ∈ Ioo (0 : ℝ) 1 from ⟨hx0, h⟩), gInd, hinv,
      Set.indicator_of_mem (mem_Ioi.mpr h1)]
    have hd : -π * x⁻¹ = -π / x := by field_simp
    have hpow : (x⁻¹) ^ (12 : ℝ) = x ^ (-12 : ℝ) := by
      rw [← Real.rpow_neg_one x, ← Real.rpow_mul hx0.le]
      norm_num
    rw [hd, hpow, smul_eq_mul]
    have hxx : x ^ ((-1 : ℝ) - 1) * x ^ (-12 : ℝ) = x ^ (-14 : ℝ) := by
      rw [← Real.rpow_add hx0]
      norm_num
    rw [show |(-1 : ℝ)| = 1 by norm_num, one_mul, ← mul_assoc, hxx]
  · have h1 : x⁻¹ ≤  1 := by rw [inv_le_one_iff₀]; right; exact h
    rw [Set.indicator_of_notMem (by simp; intro _; exact h), gInd, hinv,
      Set.indicator_of_notMem (by simp [not_lt.2 h1])]
    simp

lemma integrableOn_inner :
    IntegrableOn (fun x : ℝ => x ^ (-14 : ℝ) * rexp (-π / x)) (Ioc (0 : ℝ) 1) := by
  have h1 : IntegrableOn
      (fun x : ℝ => (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • gInd (x ^ (-1 : ℝ))) (Ioi 0) :=
    (MeasureTheory.integrableOn_Ioi_comp_rpow_iff gInd (by norm_num : (-1 : ℝ) ≠ 0)).mpr
      gInd_integrableOn
  have h2 : IntegrableOn
      ((Ioo (0 : ℝ) 1).indicator fun x => x ^ (-14 : ℝ) * rexp (-π / x)) (Ioi 0) :=
    h1.congr_fun cov_ptwise measurableSet_Ioi
  have h3 := (MeasureTheory.integrable_indicator_iff measurableSet_Ioo).mp h2
  rw [IntegrableOn, Measure.restrict_restrict measurableSet_Ioo,
    show Ioo (0 : ℝ) 1 ∩ Ioi 0 = Ioo (0 : ℝ) 1 by
      ext x; simp only [mem_inter_iff, mem_Ioo, mem_Ioi]; tauto] at h3
  rw [IntegrableOn, ← MeasureTheory.Measure.restrict_congr_set
    (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := 1))]
  exact h3

lemma integral_inner : (∫ x in Ioc (0 : ℝ) 1, x ^ (-14 : ℝ) * rexp (-π / x))
    = ∫ u in Ioi (1 : ℝ), u ^ (12 : ℝ) * rexp (-π * u) := by
  have hcov := MeasureTheory.integral_comp_rpow_Ioi gInd (by norm_num : (-1 : ℝ) ≠ 0)
  rw [integral_gInd] at hcov
  rw [setIntegral_congr_fun measurableSet_Ioi cov_ptwise] at hcov
  rw [MeasureTheory.integral_indicator measurableSet_Ioo, Measure.restrict_restrict
    measurableSet_Ioo, show Ioo (0 : ℝ) 1 ∩ Ioi 0 = Ioo (0 : ℝ) 1 by
      ext x; simp only [mem_inter_iff, mem_Ioo, mem_Ioi]; tauto] at hcov
  rw [← MeasureTheory.Measure.restrict_congr_set (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := 1))]
  exact hcov

lemma integrableOn_maj_Ioc : IntegrableOn maj (Ioc (0 : ℝ) 1) := by
  have h : IntegrableOn (fun x : ℝ => 21 / 10 * (x ^ (-14 : ℝ) * rexp (-π / x)))
      (Ioc (0 : ℝ) 1) := integrableOn_inner.const_mul (21 / 10)
  refine h.congr_fun ?_ measurableSet_Ioc
  intro t ht
  simp [maj, ht.2]

lemma integrableOn_maj_Ioi : IntegrableOn maj (Ioi (1 : ℝ)) := by
  have h : IntegrableOn (fun t : ℝ => 21 / 10 * (t ^ (12 : ℝ) * rexp (-π * t)))
      (Ioi (1 : ℝ)) := integrableOn_outer.const_mul (21 / 10)
  refine h.congr_fun ?_ measurableSet_Ioi
  intro t ht
  simp [maj, not_le.2 (mem_Ioi.mp ht)]

lemma integrableOn_maj : IntegrableOn maj (Ioi 0) := by
  rw [show Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 from (Ioc_union_Ioi_eq_Ioi zero_le_one).symm]
  exact integrableOn_maj_Ioc.union integrableOn_maj_Ioi

lemma integral_maj_le : ∫ t in Ioi (0 : ℝ), maj t ≤  1280 := by
  have hsplit : ∫ t in Ioi (0 : ℝ), maj t
      = (∫ t in Ioc (0 : ℝ) 1, maj t) + ∫ t in Ioi (1 : ℝ), maj t := by
    rw [show Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 from (Ioc_union_Ioi_eq_Ioi zero_le_one).symm]
    exact setIntegral_union (by simp [Set.disjoint_left]) measurableSet_Ioi
      integrableOn_maj_Ioc integrableOn_maj_Ioi
  have h1 : ∫ t in Ioc (0 : ℝ) 1, maj t
      = 21 / 10 * ∫ u in Ioi (1 : ℝ), u ^ (12 : ℝ) * rexp (-π * u) := by
    rw [setIntegral_congr_fun measurableSet_Ioc
      (g := fun t : ℝ => 21 / 10 * (t ^ (-14 : ℝ) * rexp (-π / t)))
      (fun t ht => by simp [maj, ht.2]), integral_const_mul, integral_inner]
  have h2 : ∫ t in Ioi (1 : ℝ), maj t
      = 21 / 10 * ∫ u in Ioi (1 : ℝ), u ^ (12 : ℝ) * rexp (-π * u) := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (g := fun t : ℝ => 21 / 10 * (t ^ (12 : ℝ) * rexp (-π * t)))
      (fun t ht => by simp [maj, not_le.2 (mem_Ioi.mp ht)]), integral_const_mul]
  rw [hsplit, h1, h2]
  have hJ := outer_le
  linarith

lemma norm_integrand_le {s : ℂ} (h0 : -24 ≤  s.re) (h1 : s.re ≤  25) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (s / 2 - 1) • P.f_modif t‖ ≤  maj t := by
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
    show (s / 2 - 1).re = s.re / 2 - 1 by simp]
  rcases lt_trichotomy t 1 with hlt | rfl | hgt
  · have hmaj : maj t = 21 / 10 * (t ^ (-14 : ℝ) * rexp (-π / t)) := by simp [maj, hlt.le]
    rw [hmaj]
    have hstep : t ^ (s.re / 2 - 1) * ‖P.f_modif t‖
        ≤  t ^ (s.re / 2 - 1) * (21 / 10 * t ^ (-(1 : ℝ) / 2) * rexp (-π / t)) :=
      mul_le_mul_of_nonneg_left (norm_f_modif_le_of_lt_one ht hlt) (Real.rpow_nonneg ht.le _)
    refine hstep.trans ?_
    have hcomb : t ^ (s.re / 2 - 1) * (21 / 10 * t ^ (-(1 : ℝ) / 2) * rexp (-π / t))
        = 21 / 10 * (t ^ (s.re / 2 - 3 / 2) * rexp (-π / t)) := by
      rw [show s.re / 2 - 3 / 2 = (s.re / 2 - 1) + (-(1 : ℝ) / 2) by ring, Real.rpow_add ht]
      ring
    rw [hcomb]
    have hexp : t ^ (s.re / 2 - 3 / 2) ≤  t ^ (-14 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge ht hlt.le (by linarith)
    have hnn : (0 : ℝ) ≤  rexp (-π / t) := (Real.exp_pos _).le
    nlinarith [Real.rpow_pos_of_pos ht (-14 : ℝ), Real.rpow_pos_of_pos ht (s.re / 2 - 3 / 2)]
  · have hm : maj (1 : ℝ) = 21 / 10 * ((1 : ℝ) ^ (-14 : ℝ) * rexp (-π / 1)) := if_pos le_rfl
    rw [hm, f_modif_one]
    simp only [norm_zero, mul_zero]
    positivity
  · have hmaj : maj t = 21 / 10 * (t ^ (12 : ℝ) * rexp (-π * t)) := by
      simp [maj, not_le.2 hgt]
    rw [hmaj]
    have hstep : t ^ (s.re / 2 - 1) * ‖P.f_modif t‖
        ≤  t ^ (s.re / 2 - 1) * (21 / 10 * rexp (-π * t)) :=
      mul_le_mul_of_nonneg_left (norm_f_modif_le_of_one_lt hgt) (Real.rpow_nonneg ht.le _)
    refine hstep.trans ?_
    have hexp : t ^ (s.re / 2 - 1) ≤  t ^ (12 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hgt.le (by linarith)
    have hnn : (0 : ℝ) ≤  rexp (-π * t) := (Real.exp_pos _).le
    nlinarith [Real.rpow_pos_of_pos ht (12 : ℝ), Real.rpow_pos_of_pos ht (s.re / 2 - 1)]

/-- **Sharpened bound on the entire part of the completed zeta function.**
In the critical strip, `‖Λ₀ s‖ ≤  640`. -/
theorem norm_completedRiemannZeta₀_le {s : ℂ} (h0 : -24 ≤  s.re) (h1 : s.re ≤  25) :
    ‖completedRiemannZeta₀ s‖ ≤  640 := by
  have hdef : completedRiemannZeta₀ s = mellin P.f_modif (s / 2) / 2 := rfl
  rw [hdef, norm_div, Complex.norm_ofNat]
  have hb : ‖mellin P.f_modif (s / 2)‖ ≤  ∫ t in Ioi (0 : ℝ), maj t := by
    rw [mellin]
    refine norm_integral_le_of_norm_le integrableOn_maj ?_
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0 : ℝ)))] with t ht
    exact norm_integrand_le h0 h1 ht
  have := hb.trans integral_maj_le
  linarith

end TaoZetaWide

end Height100Module23

section Height100Module24

open Complex Metric TaoZetaCertificate
namespace CertifiedLocalXi

noncomputable def xi (s : ℂ) : ℂ :=
  1/2+s*(s-1)/2*completedRiemannZeta₀ s
noncomputable def center (T : ℝ) : ℂ := 1/2+(T:ℂ)*I

lemma xi_entire : Differentiable ℂ xi := by
  unfold xi
  have hΛ := differentiable_completedZeta₀
  fun_prop

end CertifiedLocalXi

end Height100Module24

section Height100Module25

open Complex MeasureTheory Set Finset
namespace CertifiedGlobalMoments
open _root_.CertifiedGlobalMoments
open CertifiedZetaQuadrature TaoZetaCertificate

noncomputable def scaledVariable (z : ℂ) : ℂ := (z-1/2)/128
noncomputable def polynomial (b : ℕ → ℝ) (z : ℂ) : ℂ :=
  ∑ j ∈ range 256, (b j:ℂ)*(scaledVariable z)^(2*j)
noncomputable def xiPolynomial (b : ℕ → ℝ) (z : ℂ) : ℂ :=
  1/2+z*(z-1)/2*polynomial b z

lemma moment_scaled_integral (j : ℕ) :
    (moment j:ℂ)=(64:ℂ)^(2*j)/((2*j).factorial:ℂ)*∫ t in Ioi (1:ℝ), outerIntegrand j t := by
  unfold moment outerIntegrand
  rw [← integral_complex_ofReal,← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  unfold momentWeight
  push_cast
  rw [mul_pow]
  ring

lemma even_term (z : ℂ) (j : ℕ) :
    TaoZetaGlobal.taylorTerm z (2*j)=(moment j:ℂ)*(scaledVariable z)^(2*j) := by
  rw [TaoZetaGlobal.taylorTerm,even_derivative_moment_folded,moment_scaled_integral]
  simp only [smul_eq_mul,scaledVariable,div_pow]
  rw [show (128:ℂ)=64*2 by norm_num,mul_pow]
  have hf : ((2*j).factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero (2*j)
  field_simp

lemma odd_term (z : ℂ) (j : ℕ) : TaoZetaGlobal.taylorTerm z (2*j+1)=0 := by
  unfold TaoZetaGlobal.taylorTerm
  rw [odd_taylor_derivative_zero]
  simp

lemma sum_even_odd (f : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ range (2*N), f n)=∑ j ∈ range N, (f (2*j)+f (2*j+1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2*(N+1)=2*N+1+1 by omega]
    simp only [sum_range_succ,ih]
    ring

lemma taylor_sum_eq (z : ℂ) :
    (∑ n ∈ range 512, TaoZetaGlobal.taylorTerm z n)=polynomial moment z := by
  rw [show 512=2*256 by norm_num,sum_even_odd]
  simp_rw [even_term,odd_term,add_zero]
  rfl

lemma polynomial_entire (b : ℕ → ℝ) : Differentiable ℂ (polynomial b) := by
  unfold polynomial scaledVariable
  fun_prop

lemma xiPolynomial_entire (b : ℕ → ℝ) : Differentiable ℂ (xiPolynomial b) := by
  have h := polynomial_entire b
  unfold xiPolynomial
  fun_prop

lemma scaledVariable_norm (z : ℂ) (hz : ‖z-1/2‖≤ 104) : ‖scaledVariable z‖≤ 13/16 := by
  rw [scaledVariable,norm_div]
  norm_num
  linarith

lemma polynomial_error (b : ℕ → ℝ) (ε : ℝ) (hε : 0≤ ε)
    (hb : ∀ j<256, |moment j-b j|≤ ε) (z : ℂ) (hz : ‖z-1/2‖≤ 104) :
    ‖polynomial moment z-polynomial b z‖≤ 3*ε := by
  have hv := scaledVariable_norm z hz
  have hgeo := hasSum_geometric_of_lt_one (by norm_num : (0:ℝ)≤ 169/256) (by norm_num : (169/256:ℝ)<1)
  have hs := sum_le_hasSum (range 256) (fun n _ => pow_nonneg (by norm_num : (0:ℝ)≤ 169/256) n) hgeo
  have he : polynomial moment z-polynomial b z =
      ∑ j ∈ range 256, ((moment j-b j:ℝ):ℂ)*(scaledVariable z)^(2*j) := by
    unfold polynomial
    simp_rw [ofReal_sub,sub_mul,sum_sub_distrib]
  rw [he]
  calc
    _ ≤  ∑ j ∈ range 256, ‖((moment j-b j:ℝ):ℂ)*(scaledVariable z)^(2*j)‖ := norm_sum_le _ _
    _ ≤  ε*∑ j ∈ range 256, (169/256:ℝ)^j := by
      rw [mul_sum]
      apply sum_le_sum
      intro j hj
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,norm_pow]
      have hp : ‖scaledVariable z‖^(2*j)≤ (169/256:ℝ)^j := by
        calc
          _ ≤  (13/16:ℝ)^(2*j) := pow_le_pow_left₀ (norm_nonneg _) hv _
          _ = _ := by rw [pow_mul]; norm_num
      exact mul_le_mul (hb j (mem_range.mp hj)) hp (by positivity) hε
    _ ≤  ε*(1-(169/256:ℝ))⁻¹ := mul_le_mul_of_nonneg_left hs hε
    _ ≤  3*ε := by norm_num; linarith

lemma completedZeta_error (b : ℕ → ℝ) (ε : ℝ) (hε : 0≤ ε)
    (hb : ∀ j<256, |moment j-b j|≤ ε) (z : ℂ) (hz : ‖z-1/2‖≤ 104) :
    ‖completedRiemannZeta₀ z-polynomial b z‖≤ 1/10^45+3*ε := by
  have ht := TaoZetaGlobal.norm_taylor_remainder_512 z hz
  rw [taylor_sum_eq] at ht
  have hp := polynomial_error b ε hε hb z hz
  have he : completedRiemannZeta₀ z-polynomial b z =
      (completedRiemannZeta₀ z-polynomial moment z)+(polynomial moment z-polynomial b z) := by ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add ht hp)

lemma xi_error (b : ℕ → ℝ)
    (hb : ∀ j<256, |moment j-b j|≤ 1/10^46) (z : ℂ) (hz : ‖z-1/2‖≤ 104) :
    ‖CertifiedLocalXi.xi z-xiPolynomial b z‖≤ 1/10^41 := by
  have h0 : ‖z‖≤ 105 := by
    have h := norm_add_le (z-(1/2:ℂ)) (1/2:ℂ)
    rw [sub_add_cancel] at h
    norm_num at h
    linarith
  have h1 : ‖z-1‖≤ 105 := by
    have h := norm_sub_le (z-(1/2:ℂ)) (1/2:ℂ)
    rw [show z-(1/2:ℂ)-1/2=z-1 by ring] at h
    norm_num at h
    linarith
  have hp : ‖z*(z-1)/2‖≤ 6000 := by
    rw [norm_div,norm_mul]
    norm_num
    nlinarith [norm_nonneg z,norm_nonneg (z-1),mul_nonneg (sub_nonneg.mpr h0) (sub_nonneg.mpr h1)]
  have he : CertifiedLocalXi.xi z-xiPolynomial b z=
      (z*(z-1)/2)*(completedRiemannZeta₀ z-polynomial b z) := by
    unfold CertifiedLocalXi.xi xiPolynomial
    ring
  rw [he,norm_mul]
  have hc := completedZeta_error b (1/10^46) (by positivity) hb z hz
  calc
    _ ≤  6000*((1/10^45)+3*(1/10^46:ℝ)) := mul_le_mul hp hc (norm_nonneg _) (by norm_num)
    _ ≤  _ := by norm_num

lemma local_coefficient_error (b : ℕ → ℝ)
    (hb : ∀ j<256, |moment j-b j|≤ 1/10^46) (T : ℝ) (hT : |T|≤ 103) (n : ℕ) :
    ‖CertifiedTaylorQuadrature.coefficient CertifiedLocalXi.xi (CertifiedLocalXi.center T) n-
      CertifiedTaylorQuadrature.coefficient (xiPolynomial b) (CertifiedLocalXi.center T) n‖≤ 1/10^41 := by
  have hs : ∀ z ∈ Metric.sphere (CertifiedLocalXi.center T) (1:ℝ),
      ‖CertifiedLocalXi.xi z-xiPolynomial b z‖≤ 1/10^41 := by
    intro z hz
    apply xi_error b hb
    have h := norm_add_le (z-CertifiedLocalXi.center T) (CertifiedLocalXi.center T-(1/2:ℂ))
    rw [sub_add_sub_cancel,mem_sphere_iff_norm.mp hz] at h
    have hc : ‖CertifiedLocalXi.center T-(1/2:ℂ)‖=|T| := by
      simp [CertifiedLocalXi.center,Real.norm_eq_abs]
    rw [hc] at h
    linarith
  have h := CertifiedComplexTaylor.coefficient_error CertifiedLocalXi.xi (xiPolynomial b)
    CertifiedLocalXi.xi_entire (xiPolynomial_entire b) (CertifiedLocalXi.center T) 1 (1/10^41)
    (by norm_num) hs n
  simpa using h

end CertifiedGlobalMoments

end Height100Module25

section Height100Module26

open Complex Finset
namespace CertifiedEvenPolynomial

end CertifiedEvenPolynomial

end Height100Module26

section Height100Module27

open Complex Metric Set
namespace CertifiedLocalXi

end CertifiedLocalXi

end Height100Module27

section Height100Module28

open Complex Metric
open scoped ComplexConjugate
namespace CertifiedLocalXi

end CertifiedLocalXi

end Height100Module28

section Height100Module29

open Complex Finset
namespace CertifiedLocalXi

noncomputable def rotatedVariable (T : ℝ) (z : ℂ) : ℂ := -I*(z-center T)
noncomputable def rotatedPolynomial (b : ℕ → ℝ) (T : ℝ) (z : ℂ) : ℂ :=
  ∑ n ∈ range 32, (b n : ℂ)*rotatedVariable T z^n

lemma rotatedVariable_norm (T : ℝ) (z : ℂ) :
    ‖rotatedVariable T z‖=‖z-center T‖ := by
  simp [rotatedVariable]

lemma scaled_taylor_rotated (S T : ℝ) (z : ℂ) :
    (S:ℂ)*CertifiedComplexTaylor.polynomial xi (center T) 32 z=
      ∑ n ∈ range 32,
        ((S:ℂ)*CertifiedTaylorQuadrature.coefficient xi (center T) n*I^n)*
          rotatedVariable T z^n := by
  unfold CertifiedComplexTaylor.polynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have he : I*rotatedVariable T z=z-center T := by
    simp [rotatedVariable,← mul_assoc]
  rw [mul_assoc,← mul_pow,he]
  ring

lemma rounded_polynomial_error (S T : ℝ) (b : ℕ → ℝ)
    (hb : ∀ n<32,
      ‖(S:ℂ)*CertifiedTaylorQuadrature.coefficient xi (center T) n*I^n-(b n:ℂ)‖
        ≤ 1/10^6)
    (z : ℂ) (hz : ‖z-center T‖≤ 1) :
    ‖(S:ℂ)*CertifiedComplexTaylor.polynomial xi (center T) 32 z-
      rotatedPolynomial b T z‖≤ 32/10^6 := by
  rw [scaled_taylor_rotated]
  unfold rotatedPolynomial
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤  ∑ n ∈ range 32,
      ‖((S:ℂ)*CertifiedTaylorQuadrature.coefficient xi (center T) n*I^n-(b n:ℂ))*
        rotatedVariable T z^n‖ := by
      simpa only [sub_mul] using
        (norm_sum_le (s:=range 32) (f:=fun n =>
          ((S:ℂ)*CertifiedTaylorQuadrature.coefficient xi (center T) n*I^n)*
            rotatedVariable T z^n-(b n:ℂ)*rotatedVariable T z^n))
    _ ≤  ∑ _n ∈ range 32, (1/10^6:ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul,norm_pow]
      have hp : ‖rotatedVariable T z‖^n≤ 1 := by
        apply pow_le_one₀ (norm_nonneg _)
        simpa only [rotatedVariable_norm] using hz
      calc
        _ ≤  (1/10^6:ℝ)*1 := mul_le_mul (hb n (mem_range.mp hn)) hp
          (by positivity) (by positivity)
        _ = _ := by ring
    _ = _ := by norm_num

end CertifiedLocalXi

end Height100Module29

section Height100Module30

open Complex Finset
namespace CertifiedLocalXi

lemma xi_nonzero_implies_zeta {s : ℂ} (h0 : 0< s.re) (h1 : s.re<1)
    (hXi : xi s≠0) : riemannZeta s≠0 := by
  have hs0 : s≠0 := fun h => by simp [h] at h0
  have hs1 : s≠1 := fun h => by simp [h] at h1
  have h1s : (1:ℂ)-s≠0 := sub_ne_zero.mpr hs1.symm
  rw [riemannZeta_def_of_ne_zero hs0]
  intro hz
  rcases div_eq_zero_iff.mp hz with hz | hz
  · apply hXi
    have hh := completedRiemannZeta_eq s
    rw [hz] at hh
    have hsum : completedRiemannZeta₀ s=1/s+1/(1-s) := by linear_combination -hh
    unfold xi
    rw [hsum]
    field_simp
    ring
  · exact Complex.Gammaℝ_ne_zero_of_re_pos h0 hz

end CertifiedLocalXi

end Height100Module30

section Height100Module31

open Complex Finset
namespace CertifiedPolynomialTranslation
open CertifiedTaylorQuadrature

lemma coefficient_affine (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c a : ℂ) (n : ℕ) :
    coefficient (fun z => f (c+a*z)) 0 n=a^n*coefficient f c n := by
  have hg : Differentiable ℂ (fun z => f (c+z)) := by fun_prop
  unfold coefficient
  rw [iteratedDeriv_comp_const_mul hg.contDiff,iteratedDeriv_comp_const_add]
  simp only [mul_zero,add_zero]
  ring

lemma coefficient_power (m n : ℕ) (c : ℂ) :
    coefficient (fun z : ℂ => z^m) c n=(m.choose n:ℂ)*c^(m-n) := by
  unfold coefficient
  rw [iteratedDeriv_pow,Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul]
  have hn : (n.factorial:ℂ)≠0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

end CertifiedPolynomialTranslation

end Height100Module31

section Height100Module32

open Complex Finset
namespace CertifiedPolynomialTranslation
open CertifiedTaylorQuadrature CertifiedGlobalMoments

noncomputable def criticalMomentCoefficient (b : ℕ → ℝ) (j : ℕ) : ℝ :=
  b j*(-1)^j/(128:ℝ)^(2*j)

noncomputable def criticalXiPolynomial (b : ℕ → ℝ) (z : ℂ) : ℂ :=
  1/2-∑ j ∈ range 256, (criticalMomentCoefficient b j:ℂ)*(z^(2*j+2)/2+z^(2*j)/8)

lemma scaledVariable_critical (z : ℂ) : scaledVariable (1/2+I*z)=I*(z/128) := by
  unfold scaledVariable
  ring

lemma even_I_power (j : ℕ) : I^(2*j)=(-1:ℂ)^j := by rw [pow_mul,I_sq]

lemma global_critical_identity (b : ℕ → ℝ) (z : ℂ) :
    xiPolynomial b (1/2+I*z)=criticalXiPolynomial b z := by
  have hf : (1/2+I*z)*(1/2+I*z-1)/2=-(z^2/2+1/8) := by
    ring_nf
    rw [I_sq]
    ring
  unfold xiPolynomial criticalXiPolynomial CertifiedGlobalMoments.polynomial
  rw [hf,mul_sum,sub_eq_add_neg,←sum_neg_distrib]
  congr 1
  apply sum_congr rfl
  intro j hj
  rw [scaledVariable_critical,mul_pow,even_I_power,div_pow]
  unfold criticalMomentCoefficient
  push_cast
  rw [pow_add]
  ring

lemma coefficient_const (a c : ℂ) (n : ℕ) :
    coefficient (fun _ : ℂ => a) c n=if n=0 then a else 0 := by
  unfold coefficient
  rw [iteratedDeriv_const]
  by_cases hn : n=0 <;> simp [hn]

noncomputable def localGlobalCoefficient (b : ℕ → ℝ) (T : ℝ) (n : ℕ) : ℝ :=
  (if n=0 then 1/2 else 0)-∑ j ∈ range 256, criticalMomentCoefficient b j*
    ((Nat.choose (2*j+2) n:ℝ)*T^(2*j+2-n)/2+(Nat.choose (2*j) n:ℝ)*T^(2*j-n)/8)

lemma coefficient_criticalXi (b : ℕ → ℝ) (T : ℝ) (n : ℕ) :
    coefficient (criticalXiPolynomial b) T n=(localGlobalCoefficient b T n:ℂ) := by
  have hf : ∀ j : ℕ, Differentiable ℂ (fun z : ℂ =>
      (criticalMomentCoefficient b j:ℂ)*(z^(2*j+2)/2+z^(2*j)/8)) := by intro j; fun_prop
  unfold criticalXiPolynomial coefficient
  rw [iteratedDeriv_fun_sub (by fun_prop) (by fun_prop),sub_div,
    iteratedDeriv_fun_sum (fun j _ => (hf j).contDiff.contDiffAt),sum_div]
  change coefficient (fun _ : ℂ => 1/2) T n-
    (∑ j ∈ range 256,
      coefficient (fun z : ℂ => (criticalMomentCoefficient b j:ℂ)*
        (z^(2*j+2)/2+z^(2*j)/8)) T n)=(localGlobalCoefficient b T n:ℂ)
  rw [coefficient_const]
  unfold localGlobalCoefficient
  push_cast
  apply congrArg₂ (· - ·)
  · split_ifs <;> norm_num
  · apply sum_congr rfl
    intro j hj
    unfold coefficient
    rw [iteratedDeriv_const_mul_field,iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
      iteratedDeriv_div_const,iteratedDeriv_div_const]
    have h0 := coefficient_power (2*j+2) n (T:ℂ)
    have h1 := coefficient_power (2*j) n (T:ℂ)
    unfold coefficient at h0 h1
    calc
      _ = (criticalMomentCoefficient b j:ℂ)*
        ((iteratedDeriv n (fun z : ℂ => z^(2*j+2)) T/(n.factorial:ℂ))/2+
          (iteratedDeriv n (fun z : ℂ => z^(2*j)) T/(n.factorial:ℂ))/8) := by ring
      _ = _ := by rw [h0,h1]

lemma global_rotated_coefficient (b : ℕ → ℝ) (T : ℝ) (n : ℕ) :
    coefficient (xiPolynomial b) (CertifiedLocalXi.center T) n*I^n=
      (localGlobalCoefficient b T n:ℂ) := by
  have he : (fun z : ℂ => xiPolynomial b (CertifiedLocalXi.center T+I*z))=
      (fun z : ℂ => criticalXiPolynomial b ((T:ℂ)+z)) := by
    funext z
    rw [←global_critical_identity]
    congr 1
    unfold CertifiedLocalXi.center
    ring
  have hh := congrArg (fun F : ℂ → ℂ => coefficient F 0 n) he
  rw [coefficient_affine _ (xiPolynomial_entire b)] at hh
  unfold coefficient at hh
  rw [iteratedDeriv_comp_const_add] at hh
  simp only [add_zero] at hh
  change I^n*coefficient (xiPolynomial b) (CertifiedLocalXi.center T) n=
    coefficient (criticalXiPolynomial b) T n at hh
  rw [coefficient_criticalXi] at hh
  simpa only [mul_comm] using hh

lemma global_rotated_error (global : ℕ → ℝ) (S T v ε : ℝ) (n : ℕ)
    (h : |S*localGlobalCoefficient global T n-v|≤ ε) :
    ‖(S:ℂ)*coefficient (xiPolynomial global) (CertifiedLocalXi.center T) n*I^n-(v:ℂ)‖≤ ε := by
  rw [mul_assoc,global_rotated_coefficient,←ofReal_mul,←ofReal_sub,norm_real,Real.norm_eq_abs]
  exact h

end CertifiedPolynomialTranslation

end Height100Module32

section Height100Module33

set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

namespace CertifiedDenseGlobalPolynomial
open Complex Finset CertifiedPolynomialTranslation

end CertifiedDenseGlobalPolynomial

end Height100Module33

section Height100Module34

set_option autoImplicit false
open Finset
open scoped BigOperators

namespace CertifiedFixedPoint

end CertifiedFixedPoint

end Height100Module34

section Height100Module35

set_option autoImplicit false
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024
namespace CertifiedFixedPoint

end CertifiedFixedPoint

end Height100Module35

section Height100Module36

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CertifiedThetaPoints
open CertifiedFixedPoint

end CertifiedThetaPoints

end Height100Module36

section Height100Module37

set_option autoImplicit false
set_option maxHeartbeats 0
open Finset
open scoped BigOperators

namespace CertifiedHighPrecisionPi

end CertifiedHighPrecisionPi

end Height100Module37

section Height100Module38

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 1024
set_option Elab.async false

namespace CertifiedHighPrecisionPi

end CertifiedHighPrecisionPi

end Height100Module38

section Height100Module39

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CertifiedFixedPoint

end CertifiedFixedPoint

end Height100Module39

section Height100Module40

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option exponentiation.threshold 1024

namespace CertifiedThetaPoints
open CertifiedFixedPoint CertifiedHighPrecisionPi

end CertifiedThetaPoints

end Height100Module40

section Height100Module41

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CertifiedThetaPoints
open CertifiedFixedPoint

end CertifiedThetaPoints

end Height100Module41

section Height100Module42

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CertifiedThetaCandidates
open CertifiedThetaPoints CertifiedFixedPoint

end CertifiedThetaCandidates

end Height100Module42

section Height100Module43

namespace CertifiedStreamingODE
open CertifiedSignedODEConvolution

end CertifiedStreamingODE

end Height100Module43

section Height100Module44

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CertifiedJetRecords
open CertifiedThetaCandidates CertifiedThetaPoints CertifiedFixedPoint
open CertifiedListODEVectors CertifiedPackedConvolution CertifiedStreamingODE

end CertifiedJetRecords

end Height100Module44

section Height100Module45
namespace CertifiedJetRecords
end CertifiedJetRecords
end Height100Module45

section Height100Module46

end Height100Module46

section Height100Module47

namespace CertifiedJetRecords

end CertifiedJetRecords

end Height100Module47

section Height100Module48

set_option autoImplicit false
namespace CertifiedJetRecords
open CertifiedFixedPoint CertifiedThetaPoints CertifiedSignedODEConvolution
open CertifiedListODEVectors CertifiedStreamingODE CertifiedIntegerExponentialJets

end CertifiedJetRecords

end Height100Module48

section Height100Module49

set_option autoImplicit false
namespace CertifiedFixedPoint

end CertifiedFixedPoint

end Height100Module49

section Height100Module50

open Complex Metric Real
namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module50

section Height100Module51

open Complex Metric Finset
namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature
set_option exponentiation.threshold 512
open CertifiedTaylorQuadrature CertifiedMomentConvolution

end CertifiedZetaQuadrature

end Height100Module51

section Height100Module52

open Complex Finset
namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature
open CertifiedTaylorQuadrature CertifiedMomentConvolution CertifiedExponentialJets

end CertifiedZetaQuadrature

end Height100Module52

section Height100Module53

open Complex Finset
namespace CertifiedJetRecords
open CertifiedFixedPoint CertifiedThetaPoints CertifiedIntegerExponentialJets
open CertifiedZetaQuadrature CertifiedMomentConvolution CertifiedTaylorQuadrature

end CertifiedJetRecords

end Height100Module53

section Height100Module54

open Complex Finset
namespace CertifiedMomentConvolution
open CertifiedTaylorQuadrature

end CertifiedMomentConvolution

end Height100Module54

section Height100Module55

open Complex Finset
namespace CertifiedMomentConvolution
open CertifiedTaylorQuadrature

set_option exponentiation.threshold 512

end CertifiedMomentConvolution

end Height100Module55

section Height100Module56

open Complex Metric Finset MeasureTheory
namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module56

section Height100Module57

open Complex Metric Finset MeasureTheory
namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module57

section Height100Module58
open Complex Metric MeasureTheory
namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature
end CertifiedZetaQuadrature

end Height100Module58

section Height100Module59

open Complex MeasureTheory Finset
namespace CertifiedGlobalQuadrature
open CertifiedZetaQuadrature CertifiedTaylorQuadrature

end CertifiedGlobalQuadrature

end Height100Module59

section Height100Module60

open Complex Finset
namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature
open CertifiedMomentConvolution CertifiedTaylorQuadrature

end CertifiedZetaQuadrature

end Height100Module60

section Height100Module61

open Complex Metric Finset
namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature
open CertifiedTaylorQuadrature CertifiedMomentConvolution
set_option exponentiation.threshold 1024

end CertifiedZetaQuadrature

end Height100Module61

section Height100Module62

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
open Finset Complex
open scoped BigOperators

namespace CertifiedGlobalJetCenters
open CertifiedJetRecords CertifiedThetaPoints CertifiedFixedPoint
open CertifiedMomentConvolution CertifiedZetaQuadrature

end CertifiedGlobalJetCenters

end Height100Module62

section Height100Module63

set_option autoImplicit false
open Finset
open scoped BigOperators
namespace CertifiedPackedCorrelation
open CertifiedSignedODEConvolution CertifiedListODEVectors CertifiedPackedConvolution

end CertifiedPackedCorrelation

end Height100Module63

section Height100Module64

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace CertifiedMomentWeights
open CertifiedMomentConvolution

end CertifiedMomentWeights

end Height100Module64

section Height100Module65

namespace CertifiedExponentialIntegerSequence

end CertifiedExponentialIntegerSequence

end Height100Module65

section Height100Module66

set_option autoImplicit false
set_option maxHeartbeats 0
open Complex Finset
open scoped BigOperators
namespace CertifiedMomentArithmetic
open CertifiedFixedPoint CertifiedExponentialIntegerSequence
open CertifiedMomentConvolution

end CertifiedMomentArithmetic

end Height100Module66

section Height100Module67

set_option autoImplicit false
namespace CertifiedPackedExtraction
open CertifiedSignedODEConvolution

end CertifiedPackedExtraction

end Height100Module67

section Height100Module68

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CertifiedMomentRecords
open CertifiedGlobalJetCenters CertifiedThetaCandidates CertifiedThetaPoints
open CertifiedJetRecords CertifiedFixedPoint CertifiedPackedConvolution
open CertifiedMomentArithmetic CertifiedListODEVectors CertifiedPackedExtraction

end CertifiedMomentRecords

end Height100Module68

section Height100Module69

namespace CertifiedExponentialSequenceCheck
open CertifiedExponentialIntegerSequence

end CertifiedExponentialSequenceCheck

end Height100Module69

section Height100Module70

namespace CertifiedPackedExponentialSequence
open CertifiedPackedConvolution CertifiedExponentialSequenceCheck

end CertifiedPackedExponentialSequence

end Height100Module70

section Height100Module71

namespace CertifiedChunkedExponentialSequence
open CertifiedPackedConvolution CertifiedPackedExponentialSequence

end CertifiedChunkedExponentialSequence

end Height100Module71

section Height100Module72

namespace CertifiedChunkedEncoding
open CertifiedPackedConvolution CertifiedPackedExponentialSequence
open CertifiedChunkedExponentialSequence

end CertifiedChunkedEncoding

end Height100Module72

section Height100Module73

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CertifiedMomentSequenceCache
open CertifiedMomentRecords CertifiedMomentArithmetic CertifiedPackedConvolution
open CertifiedExponentialIntegerSequence CertifiedExponentialSequenceCheck
open CertifiedChunkedEncoding CertifiedListODEVectors CertifiedPackedExtraction

end CertifiedMomentSequenceCache

end Height100Module73

section Height100Module76

end Height100Module76

section Height100Module77
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace CertifiedLocalCandidates

end CertifiedLocalCandidates

end Height100Module77

section Height100Module78

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
set_option exponentiation.threshold 20000

namespace CertifiedGlobalTranslation
open CertifiedMomentRecords CertifiedPackedHorner CertifiedSignedODEConvolution
open CertifiedPackedExtraction CertifiedListODEVectors

end CertifiedGlobalTranslation

end Height100Module78

section Height100Module79

open Finset
namespace CertifiedPolynomialTranslation

end CertifiedPolynomialTranslation

end Height100Module79

section Height100Module80

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
set_option exponentiation.threshold 20000
namespace CertifiedTranslationConvolution
open CertifiedGlobalTranslation CertifiedPackedConvolution CertifiedListODEVectors
open CertifiedExponentialIntegerSequence CertifiedPackedExtraction

end CertifiedTranslationConvolution

end Height100Module80

section Height100Module81

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace CertifiedPackedTranslation
open CertifiedTranslationConvolution CertifiedGlobalTranslation
open CertifiedPackedConvolution CertifiedPackedExtraction CertifiedExponentialIntegerSequence

end CertifiedPackedTranslation

end Height100Module81

section Height100Module82

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CertifiedLiteralTranslation
open CertifiedTranslationConvolution CertifiedGlobalTranslation
open CertifiedPackedConvolution CertifiedPackedExtraction CertifiedExponentialIntegerSequence

end CertifiedLiteralTranslation

end Height100Module82

section Height100Module83
namespace CertifiedLiteralTranslation
end CertifiedLiteralTranslation
end Height100Module83

section Height100Module84

namespace CertifiedExponentialSequenceBound
open CertifiedExponentialSequenceCheck CertifiedPackedExponentialSequence
open CertifiedPackedConvolution
set_option maxRecDepth 100000
set_option exponentiation.threshold 8192

end CertifiedExponentialSequenceBound

end Height100Module84

section Height100Module85

set_option autoImplicit false
open Complex Finset
namespace CertifiedPackedHorner
open CertifiedTaylorQuadrature CertifiedPolynomialTranslation

end CertifiedPackedHorner

namespace CertifiedPackedHorner
open CertifiedTaylorQuadrature
end CertifiedPackedHorner

namespace CertifiedPackedHorner
open CertifiedTaylorQuadrature
end CertifiedPackedHorner

namespace CertifiedPackedHorner
open CertifiedTaylorQuadrature CertifiedPolynomialTranslation

end CertifiedPackedHorner

end Height100Module85

section Height100Module86

set_option autoImplicit false
open Finset Complex
namespace CertifiedTranslationAlgebra
open CertifiedPolynomialTranslation CertifiedPackedHorner CertifiedListODEVectors
open CertifiedPackedCorrelation CertifiedPackedConvolution CertifiedSignedODEConvolution

end CertifiedTranslationAlgebra

namespace CertifiedTranslationAlgebra
open CertifiedPackedConvolution CertifiedSignedODEConvolution

end CertifiedTranslationAlgebra

end Height100Module86

section Height100Module87

set_option autoImplicit false
set_option maxHeartbeats 0
open Finset Complex
namespace CertifiedMomentRecords
open CertifiedPackedCorrelation CertifiedMomentArithmetic CertifiedMomentConvolution
open CertifiedListODEVectors CertifiedPackedExtraction CertifiedSignedODEConvolution
open CertifiedGlobalJetCenters CertifiedFixedPoint CertifiedPackedConvolution

end CertifiedMomentRecords

end Height100Module87

section Height100Module88

set_option autoImplicit false
namespace CertifiedIntegerRounding

end CertifiedIntegerRounding

end Height100Module88

section Height100Module89
namespace CertifiedGlobalMomentEnclosure
end CertifiedGlobalMomentEnclosure
end Height100Module89

section Height100Module90

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
open Complex Finset
namespace CertifiedGlobalTranslation
open CertifiedPackedHorner CertifiedListODEVectors CertifiedPackedExtraction
open CertifiedSignedODEConvolution CertifiedTaylorQuadrature CertifiedPolynomialTranslation

end CertifiedGlobalTranslation

end Height100Module90

section Height100Module91

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
open Complex Finset
namespace CertifiedPackedTranslation
open CertifiedTranslationConvolution CertifiedGlobalTranslation
open CertifiedPackedConvolution CertifiedListODEVectors CertifiedPackedExtraction
open CertifiedSignedODEConvolution CertifiedTranslationAlgebra CertifiedPackedExponentialSequence

end CertifiedPackedTranslation

end Height100Module91

section Height100Module92

namespace CertifiedPackedTranslation
open CertifiedTranslationConvolution CertifiedGlobalTranslation CertifiedPolynomialTranslation

end CertifiedPackedTranslation

end Height100Module92

section Height100Module93

set_option autoImplicit false
set_option exponentiation.threshold 8192
namespace CertifiedLiteralTranslation
open CertifiedTranslationConvolution CertifiedGlobalTranslation
open CertifiedPackedConvolution CertifiedPackedExtraction

end CertifiedLiteralTranslation

end Height100Module93

section Height100Module94

set_option autoImplicit false
set_option maxHeartbeats 0

namespace TaoZetaPoly

end TaoZetaPoly

end Height100Module94

section Height100Module95

namespace CertifiedLocalPolynomial
open TaoZetaPoly Complex Finset CertifiedLocalXi

end CertifiedLocalPolynomial

end Height100Module95

section Height100Module96

namespace CertifiedIntegerLocalPolynomial
open Complex Finset

end CertifiedIntegerLocalPolynomial

end Height100Module96

section Height100Module97

open Finset Polynomial
open scoped unitInterval
set_option autoImplicit false

namespace TaoZetaNumerics

lemma bernstein_lower_bound (n : ℕ) (c : Fin (n + 1) → ℝ) (L : ℝ)
    (hc : ∀ i, L ≤  c i) (x : I) :
    L ≤  ∑ i : Fin (n + 1), c i * bernstein n i x := by
  calc
    L = ∑ i : Fin (n + 1), L * bernstein n i x := by
      rw [← Finset.mul_sum, bernstein.probability, mul_one]
    _ ≤  ∑ i : Fin (n + 1), c i * bernstein n i x := by
      exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hc i) bernstein_nonneg

lemma bernstein_lower_bound_two (m n : ℕ) (c : Fin (m + 1) → Fin (n + 1) → ℝ)
    (L : ℝ) (hc : ∀ i j, L ≤  c i j) (x y : I) :
    L ≤  ∑ i : Fin (m + 1), ∑ j : Fin (n + 1),
      c i j * bernstein m i x * bernstein n j y := by
  have h := bernstein_lower_bound m
    (fun i => ∑ j : Fin (n + 1), c i j * bernstein n j y) L
    (fun i => bernstein_lower_bound n (c i) L (hc i) y) x
  convert h using 1
  apply sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply sum_congr rfl
  intro j _
  ring

end TaoZetaNumerics

end Height100Module97

section Height100Module98

open Finset
open scoped unitInterval
set_option autoImplicit false
set_option maxHeartbeats 0

namespace TaoZetaNumerics

noncomputable def bernsteinValue (n i : ℕ) (x : ℝ) : ℝ :=
  (n.choose i : ℝ) * x ^ i * (1 - x) ^ (n - i)

lemma monomial_bernstein (n j : ℕ) (hj : j ≤  n) (x : ℝ) :
    x ^ j = ∑ i ∈ range (n + 1),
      ((i.choose j : ℝ) / n.choose j) * bernsteinValue n i x := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hj
  have hnz : ((j + m).choose j : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (Nat.le_add_right j m)
  have hsum0 : (∑ i ∈ range j,
      ((i.choose j : ℝ) / (j + m).choose j) * bernsteinValue (j + m) i x) = 0 := by
    apply sum_eq_zero
    intro i hi
    simp [Nat.choose_eq_zero_of_lt (mem_range.mp hi)]
  have hshift : j + m + 1 = j + (m + 1) := by omega
  rw [hshift, Finset.sum_range_add, hsum0, zero_add]
  have hterm (i : ℕ) :
      (((j + i).choose j : ℝ) / (j + m).choose j) * bernsteinValue (j + m) (j + i) x =
        (m.choose i : ℝ) * x ^ (j + i) * (1 - x) ^ (m - i) := by
    have hc : ((j + m).choose (j + i) : ℝ) * ((j + i).choose j : ℝ) =
        ((j + m).choose j : ℝ) * (m.choose i : ℝ) := by
      exact_mod_cast (by simpa only [Nat.add_sub_cancel_left] using
        (Nat.choose_mul (n := j + m) (Nat.le_add_right j i)))
    have hcoef : (((j + i).choose j : ℝ) / (j + m).choose j) *
        ((j + m).choose (j + i) : ℝ) = (m.choose i : ℝ) := by
      field_simp
      nlinarith [hc]
    unfold bernsteinValue
    have hsub : j + m - (j + i) = m - i := by omega
    rw [hsub, ← mul_assoc, ← mul_assoc, hcoef]
  simp_rw [hterm]
  calc
    x ^ j = x ^ j * (x + (1 - x)) ^ m := by simp
    _ = ∑ i ∈ range (m + 1), (m.choose i : ℝ) * x ^ (j + i) * (1 - x) ^ (m - i) := by
      rw [add_pow, Finset.mul_sum]
      apply sum_congr rfl
      intro i _
      rw [pow_add]
      ring

noncomputable def chooseFast (n k : ℕ) : ℕ :=
  if k ≤  n then n.factorial / (k.factorial * (n - k).factorial) else 0

lemma chooseFast_eq (n k : ℕ) : chooseFast n k = n.choose k := by
  by_cases h : k ≤  n
  · simp only [chooseFast, if_pos h, Nat.choose_eq_factorial_div_factorial h]
  · simp only [chooseFast, if_neg h, Nat.choose_eq_zero_of_lt (lt_of_not_ge h)]

noncomputable def bernsteinTransform (n : ℕ) (a : Fin (n + 1) → ℚ) (i : Fin (n + 1)) : ℚ :=
  ∑ j : Fin (n + 1), a j * (chooseFast i j : ℚ) / chooseFast n j

lemma bernsteinTransform_sound (n : ℕ) (a : Fin (n + 1) → ℚ) (x : I) :
    (∑ j : Fin (n + 1), (a j : ℝ) * (x : ℝ) ^ (j : ℕ)) =
      ∑ i : Fin (n + 1), (bernsteinTransform n a i : ℝ) * bernstein n i x := by
  have hm (j : Fin (n + 1)) : (x : ℝ) ^ (j : ℕ) =
      ∑ i : Fin (n + 1), ((i.val.choose j : ℝ) / n.choose j) * bernstein n i x := by
    simpa only [Finset.sum_range, bernstein_apply, bernsteinValue] using
      monomial_bernstein n j (Nat.le_of_lt_succ j.isLt) x
  simp_rw [hm, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro i _
  simp only [bernsteinTransform, Rat.cast_sum, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast,
    chooseFast_eq, Finset.sum_mul]
  apply sum_congr rfl
  intro j _
  ring

end TaoZetaNumerics

end Height100Module98

section Height100Module99

namespace CertifiedLocalPolynomial
open TaoZetaPoly Complex Finset TaoZetaNumerics
open scoped unitInterval

noncomputable def bivariatePowerValue (m n : ℕ)
    (a : Fin (m+1) → Fin (n+1) → ℚ) (x y : ℝ) : ℝ :=
  ∑ i : Fin (m+1), ∑ j : Fin (n+1), (a i j:ℝ)*x^(i:ℕ)*y^(j:ℕ)

lemma bivariate_bernstein_identity (m n : ℕ)
    (a row result : Fin (m+1) → Fin (n+1) → ℚ)
    (hr : ∀ i, row i=bernsteinTransform n (a i))
    (hc : ∀ j, (fun i => result i j)=bernsteinTransform m (fun i => row i j))
    (x y : I) :
    bivariatePowerValue m n a x y=
      ∑ i : Fin (m+1), ∑ j : Fin (n+1),
        (result i j:ℝ)*bernstein m i x*bernstein n j y := by
  have hrow (i : Fin (m+1)) := bernsteinTransform_sound n (a i) y
  simp only [←hr] at hrow
  have hcol (j : Fin (n+1)) := bernsteinTransform_sound m (fun i => row i j) x
  simp only [←hc] at hcol
  unfold bivariatePowerValue
  calc
    _ = ∑ i : Fin (m+1), (x:ℝ)^(i:ℕ)*
        (∑ j : Fin (n+1), (a i j:ℝ)*(y:ℝ)^(j:ℕ)) := by
      apply sum_congr rfl
      intro i _
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      ring
    _ = ∑ j : Fin (n+1),
        (∑ i : Fin (m+1), (row i j:ℝ)*(x:ℝ)^(i:ℕ))*bernstein n j y := by
      simp_rw [hrow,mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      rw [sum_mul]
      apply sum_congr rfl
      intro i _
      ring
    _ = _ := by
      simp_rw [hcol,sum_mul]
      rw [sum_comm]

lemma bivariate_bernstein_lower (m n : ℕ)
    (a row result : Fin (m+1) → Fin (n+1) → ℚ)
    (hr : ∀ i, row i=bernsteinTransform n (a i))
    (hc : ∀ j, (fun i => result i j)=bernsteinTransform m (fun i => row i j))
    (L : ℝ) (hL : ∀ i j, L≤ (result i j:ℝ)) (x y : I) :
    L≤ bivariatePowerValue m n a x y := by
  rw [bivariate_bernstein_identity m n a row result hr hc x y]
  exact bernstein_lower_bound_two m n (fun i j => (result i j:ℝ)) L hL x y

end CertifiedLocalPolynomial

end Height100Module99

section Height100Module100

namespace CertifiedLocalPolynomial
open TaoZetaPoly Complex Finset CertifiedLocalXi
open scoped unitInterval

end CertifiedLocalPolynomial

end Height100Module100

section Height100Module101

open Finset
set_option autoImplicit false
set_option maxHeartbeats 0
namespace TaoZetaNumerics

end TaoZetaNumerics

end Height100Module101

section Height100Module102

namespace CertifiedLocalBoxes
open CertifiedLocalCandidates CertifiedLocalPolynomial TaoZetaPoly TaoZetaNumerics
open Finset
open scoped unitInterval

end CertifiedLocalBoxes

end Height100Module102

section Height100Module103

namespace CertifiedFastLocalBoxes
open CertifiedLocalBoxes CertifiedIntegerLocalPolynomial TaoZetaNumerics Finset

end CertifiedFastLocalBoxes

end Height100Module103

section Height100Module104

namespace CertifiedStreamingBernstein
open CertifiedLocalBoxes CertifiedIntegerLocalPolynomial TaoZetaNumerics Finset

end CertifiedStreamingBernstein

end Height100Module104

section Height100Module105

namespace CertifiedStreamingLocalBoxes
open CertifiedLocalBoxes CertifiedFastLocalBoxes CertifiedStreamingBernstein
open TaoZetaNumerics

end CertifiedStreamingLocalBoxes

end Height100Module105

section Height100Module106

namespace CertifiedFastLocalBoxes
open CertifiedLocalBoxes
open CertifiedLocalPolynomial CertifiedIntegerLocalPolynomial TaoZetaNumerics Finset
open scoped unitInterval

end CertifiedFastLocalBoxes

end Height100Module106

section Height100Module107

namespace CertifiedLocalBoxes
open CertifiedLocalCandidates CertifiedLocalPolynomial CertifiedLocalXi

end CertifiedLocalBoxes

end Height100Module107

section Height100Module108

namespace CertifiedFastLocalBoxes
open CertifiedLocalBoxes CertifiedIntegerLocalPolynomial CertifiedLocalPolynomial CertifiedLocalXi
open scoped unitInterval

end CertifiedFastLocalBoxes

end Height100Module108

section Height100Module109

namespace CertifiedStreamingLocalBoxes
open CertifiedLocalBoxes CertifiedFastLocalBoxes CertifiedStreamingBernstein

end CertifiedStreamingLocalBoxes

end Height100Module109

section Height100Module110
namespace CertifiedStreamingLocalBoxes
open CertifiedLocalBoxes
end CertifiedStreamingLocalBoxes
end Height100Module110

section Height100Module111

namespace CertifiedStreamingLocalBoxes
open CertifiedFastLocalBoxes
open CertifiedLocalBoxes CertifiedLocalPolynomial CertifiedLocalXi

end CertifiedStreamingLocalBoxes

end Height100Module111

section Height100Module112

namespace CertifiedHeight100
open CertifiedPolynomialTranslation CertifiedGlobalMoments CertifiedLocalXi

end CertifiedHeight100

end Height100Module112

section Height100Module113

set_option autoImplicit false
namespace TaoFivePrimes

end TaoFivePrimes

end Height100Module113

end RH101Proof

namespace RH101Numerical
open Finset
noncomputable def denominator : ℕ := 8*10^64*2^4096
noncomputable def normalizationNat : ℕ := 10^33
noncomputable def center : ℚ := 201/2
noncomputable def roundedNumerators : List ℤ := [-42589693464, 67041240892, -5906472175, -22817930401, 10102835095, -459599376, -659038885, 160946632, -817856, -5295653, 797102, 11247, -16107, 1644, 42, -23, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
noncomputable def rounded (n : ℕ) : ℤ := roundedNumerators.getD n 0
noncomputable def chooseFast (k n : ℕ) : ℕ :=
  if n≤k then k.factorial/(n.factorial*(k-n).factorial) else 0
noncomputable def numerator (n : ℕ) : ℤ :=
  (if n=0 then (4*10^64*2^4096:ℤ) else 0)*(normalizationNat:ℤ)-
  (normalizationNat:ℤ)*∑ j ∈ range 256,
    TaoFivePrimes_RH14To100RoundedMomentData.getD j 0*(-1:ℤ)^j*
    ((2^(4096-16*j+n):ℕ):ℤ)*
    ((chooseFast (2*j+2) n:ℤ)*(201:ℤ)^(2*j+2-n)+
      (chooseFast (2*j) n:ℤ)*(201:ℤ)^(2*j-n))
noncomputable def residualCheck (n : ℕ) : Prop :=
  |(10^8:ℤ)*numerator n-rounded n*(denominator:ℤ)|≤(denominator:ℤ)
noncomputable instance (n : ℕ) : Decidable (residualCheck n) :=
  inferInstanceAs (Decidable (_≤_))
theorem residuals_checked : ∀ n : Fin 32, residualCheck n.val := by decide +kernel
end RH101Numerical

/- Checked component: RH101TranslationSoundness.lean -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option linter.unusedSimpArgs false
namespace RH101Numerical
open Finset
lemma chooseFast_eq (k n : ℕ) : chooseFast k n=Nat.choose k n := by
  by_cases h : n≤k
  · simp only [chooseFast,if_pos h,Nat.choose_eq_factorial_div_factorial h]
  · simp only [chooseFast,if_neg h,Nat.choose_eq_zero_of_lt (lt_of_not_ge h)]
lemma monomial_scaled (k n : ℕ) :
    (Nat.choose k n:ℝ)*(201/2:ℝ)^(k-n)=
      (Nat.choose k n:ℝ)*(201:ℝ)^(k-n)*2^n/2^k := by
  by_cases h : n≤k
  · rw [div_pow,pow_sub₀ (2:ℝ) (by norm_num : (2:ℝ)≠0) h]
    field_simp
  · have hc := Nat.choose_eq_zero_of_lt (lt_of_not_ge h)
    simp [hc]
lemma dyadic_scale (j n : ℕ) (hj : j<256) :
    ((2^(4096-16*j+n):ℕ):ℝ)/(2^4096:ℝ)=2^n/(256:ℝ)^(2*j) := by
  push_cast
  have hv : (256:ℝ)^(2*j)=(2:ℝ)^(16*j) := by
    rw [show (256:ℝ)=2^8 by norm_num,←pow_mul]
    congr 1
    omega
  rw [hv,pow_add,pow_sub₀ (2:ℝ) (by norm_num : (2:ℝ)≠0) (by omega : 16*j≤4096)]
  field_simp
lemma monomial_combo (j n : ℕ) :
    ((Nat.choose (2*j+2) n:ℝ)*(201/2:ℝ)^(2*j+2-n)/2+
      (Nat.choose (2*j) n:ℝ)*(201/2:ℝ)^(2*j-n)/8)/(128:ℝ)^(2*j)=
    ((chooseFast (2*j+2) n:ℝ)*(201:ℝ)^(2*j+2-n)+
      (chooseFast (2*j) n:ℝ)*(201:ℝ)^(2*j-n))*2^n/(8*(256:ℝ)^(2*j)) := by
  simp only [chooseFast_eq]
  rw [monomial_scaled,monomial_scaled,pow_add]
  norm_num
  have hv : (256:ℝ)^(2*j)=(2:ℝ)^(2*j)*(128:ℝ)^(2*j) := by
    rw [←mul_pow]
    norm_num
  rw [hv]
  field_simp
  <;> ring

lemma term_identity (j n : ℕ) (hj : j<256) :
    ((TaoFivePrimes_RH14To100RoundedMomentData.getD j 0:ℝ)*(-1:ℝ)^j*
      ((2^(4096-16*j+n):ℕ):ℝ)*
      ((chooseFast (2*j+2) n:ℝ)*(201:ℝ)^(2*j+2-n)+
        (chooseFast (2*j) n:ℝ)*(201:ℝ)^(2*j-n)))/(denominator:ℝ)=
    RH101Proof.CertifiedPolynomialTranslation.criticalMomentCoefficient
      CertifiedGlobalMomentEnclosure.candidateMoment j*
      ((Nat.choose (2*j+2) n:ℝ)*(201/2:ℝ)^(2*j+2-n)/2+
        (Nat.choose (2*j) n:ℝ)*(201/2:ℝ)^(2*j-n)/8) := by
  have hd : (denominator:ℝ)=8*(10:ℝ)^64*(2:ℝ)^4096 := by norm_num [denominator]
  rw [hd]
  unfold RH101Proof.CertifiedPolynomialTranslation.criticalMomentCoefficient
    CertifiedGlobalMomentEnclosure.candidateMoment
  have hm := monomial_combo j n
  have hs := dyadic_scale j n hj
  calc
    _ = (TaoFivePrimes_RH14To100RoundedMomentData.getD j 0:ℝ)*(-1:ℝ)^j*
        ((chooseFast (2*j+2) n:ℝ)*(201:ℝ)^(2*j+2-n)+
          (chooseFast (2*j) n:ℝ)*(201:ℝ)^(2*j-n))/(8*(10:ℝ)^64)*
          (((2^(4096-16*j+n):ℕ):ℝ)/(2^4096:ℝ)) := by ring
    _ = (TaoFivePrimes_RH14To100RoundedMomentData.getD j 0:ℝ)/(10:ℝ)^64*(-1:ℝ)^j*
        (((chooseFast (2*j+2) n:ℝ)*(201:ℝ)^(2*j+2-n)+
          (chooseFast (2*j) n:ℝ)*(201:ℝ)^(2*j-n))*2^n/(8*(256:ℝ)^(2*j))) := by rw [hs]; ring
    _ = _ := by rw [←hm]; ring
lemma denominator_pos : 0<(denominator:ℝ) := by
  exact_mod_cast (show 0<denominator by unfold denominator; positivity)
lemma numerator_real (n : ℕ) :
    (numerator n:ℝ)/(denominator:ℝ)=
      (normalizationNat:ℝ)*RH101Proof.CertifiedPolynomialTranslation.localGlobalCoefficient
        CertifiedGlobalMomentEnclosure.candidateMoment (201/2) n := by
  have hd : (denominator:ℝ)=8*(10:ℝ)^64*(2:ℝ)^4096 := by norm_num [denominator]
  have hh : (4*(10:ℝ)^64*(2:ℝ)^4096)/(denominator:ℝ)=1/2 := by
    rw [hd]
    field_simp
    <;> ring
  let f (j : ℕ) : ℝ :=
    (TaoFivePrimes_RH14To100RoundedMomentData.getD j 0:ℝ)*(-1:ℝ)^j*
      (2:ℝ)^(4096-16*j+n)*
      ((chooseFast (2*j+2) n:ℝ)*(201:ℝ)^(2*j+2-n)+
        (chooseFast (2*j) n:ℝ)*(201:ℝ)^(2*j-n))
  have hs : (∑ j ∈ range 256, f j)/(denominator:ℝ)=
      ∑ j ∈ range 256,
        RH101Proof.CertifiedPolynomialTranslation.criticalMomentCoefficient
          CertifiedGlobalMomentEnclosure.candidateMoment j*
          ((Nat.choose (2*j+2) n:ℝ)*(201/2:ℝ)^(2*j+2-n)/2+
            (Nat.choose (2*j) n:ℝ)*(201/2:ℝ)^(2*j-n)/8) := by
    rw [sum_div]
    apply sum_congr rfl
    intro j hj
    simpa only [f,Nat.cast_pow,Nat.cast_ofNat] using term_identity j n (mem_range.mp hj)
  have he : (numerator n:ℝ)/(denominator:ℝ)=
      (normalizationNat:ℝ)*
        (((if n=0 then 4*(10:ℝ)^64*(2:ℝ)^4096 else 0)/(denominator:ℝ))-
          (∑ j ∈ range 256, f j)/(denominator:ℝ)) := by
    unfold numerator
    push_cast
    dsimp only [f]
    split_ifs <;> ring
  rw [he,hs]
  unfold RH101Proof.CertifiedPolynomialTranslation.localGlobalCoefficient
  split_ifs <;> simp only [zero_div,hh]

attribute [local irreducible] numerator rounded denominator
noncomputable def proposed (n : ℕ) : ℝ := (rounded n:ℝ)/(10^8:ℝ)
lemma rounding_error (n : ℕ) (hn : n<32) :
    |(numerator n:ℝ)/(denominator:ℝ)-proposed n|≤1/10^8 := by
  have h0 := residuals_checked (⟨n,hn⟩:Fin 32)
  change |(10^8:ℤ)*numerator n-rounded n*(denominator:ℤ)|≤(denominator:ℤ) at h0
  have h : |(10^8:ℝ)*(numerator n:ℝ)-(rounded n:ℝ)*(denominator:ℝ)|≤(denominator:ℝ) := by
    exact_mod_cast h0
  have hd := denominator_pos
  have he : (numerator n:ℝ)/(denominator:ℝ)-proposed n=
      ((10^8:ℝ)*(numerator n:ℝ)-(rounded n:ℝ)*(denominator:ℝ))/
        ((10^8:ℝ)*(denominator:ℝ)) := by
    unfold proposed
    field_simp
    <;> ring
  rw [he,abs_div,abs_of_pos (mul_pos (by positivity) hd)]
  apply (div_le_iff₀ (mul_pos (by positivity) hd)).mpr
  convert h using 1 <;> first | ring | (congr 1 <;> ring)
lemma translated_error (n : ℕ) (hn : n<32) :
    |(normalizationNat:ℝ)*RH101Proof.CertifiedPolynomialTranslation.localGlobalCoefficient
      CertifiedGlobalMomentEnclosure.candidateMoment (201/2) n-proposed n|≤1/10^8 := by
  rw [←numerator_real]
  exact rounding_error n hn
end RH101Numerical

/- Checked component: RH101BernsteinData.lean -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace RH101Numerical
noncomputable def powerMatrix : List (List ℚ) := [
  [(24281234781211:ℚ)/32768000000, (-166396709552723:ℚ)/327680000000, (-354934575147939:ℚ)/819200000000, (172765933656721:ℚ)/409600000000, (-16580859549211:ℚ)/204800000000, (-2376110616299:ℚ)/102400000000, (595162623409:ℚ)/51200000000, (-26950040939:ℚ)/25600000000, (-798382291:ℚ)/2560000000, (110268327:ℚ)/1280000000, (-13303721:ℚ)/3200000000, (-2172813:ℚ)/1600000000, (38883:ℚ)/160000000, (-97:ℚ)/16000000, (-549:ℚ)/200000000, (39:ℚ)/100000000, (-1:ℚ)/50000000],
  [(354934575147939:ℚ)/3276800000000, (-518297800970163:ℚ)/1638400000000, (49742578647633:ℚ)/409600000000, (2376110616299:ℚ)/40960000000, (-1785487870227:ℚ)/40960000000, (565950859719:ℚ)/102400000000, (5588676037:ℚ)/2560000000, (-992414943:ℚ)/1280000000, (119733489:ℚ)/2560000000, (23900943:ℚ)/1280000000, (-1283139:ℚ)/320000000, (3783:ℚ)/32000000, (49959:ℚ)/800000000, (-819:ℚ)/80000000, (3:ℚ)/5000000, 0, 0],
  [(-16580859549211:ℚ)/3276800000000, (-2376110616299:ℚ)/327680000000, (1785487870227:ℚ)/163840000000, (-188650286573:ℚ)/81920000000, (-5588676037:ℚ)/4096000000, (6946904601:ℚ)/10240000000, (-279378141:ℚ)/5120000000, (-71702829:ℚ)/2560000000, (3849417:ℚ)/512000000, (-13871:ℚ)/51200000, (-549549:ℚ)/3200000000, (10647:ℚ)/320000000, (-91:ℚ)/40000000, 0, 0, 0, 0],
  [(-595162623409:ℚ)/3276800000000, (188650286573:ℚ)/1638400000000, (5588676037:ℚ)/40960000000, (-2315634867:ℚ)/20480000000, (279378141:ℚ)/20480000000, (501919803:ℚ)/51200000000, (-8981973:ℚ)/2560000000, (41613:ℚ)/256000000, (1648647:ℚ)/12800000000, (-39039:ℚ)/1280000000, (1001:ℚ)/400000000, 0, 0, 0, 0, 0, 0],
  [(-798382291:ℚ)/655360000000, (992414943:ℚ)/327680000000, (-119733489:ℚ)/163840000000, (-71702829:ℚ)/81920000000, (3849417:ℚ)/8192000000, (-124839:ℚ)/4096000000, (-1648647:ℚ)/51200000000, (50193:ℚ)/5120000000, (-1287:ℚ)/1280000000, 0, 0, 0, 0, 0, 0, 0, 0],
  [(13303721:ℚ)/3276800000000, (23900943:ℚ)/1638400000000, (-1283139:ℚ)/81920000000, (13871:ℚ)/8192000000, (549549:ℚ)/204800000000, (-117117:ℚ)/102400000000, (1001:ℚ)/6400000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [(38883:ℚ)/655360000000, (-1261:ℚ)/65536000000, (-49959:ℚ)/819200000000, (3549:ℚ)/81920000000, (-91:ℚ)/10240000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [(549:ℚ)/3276800000000, (-117:ℚ)/327680000000, (3:ℚ)/20480000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [(-1:ℚ)/3276800000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
noncomputable def rowMatrix : List (List ℚ) := [
  [(24281234781211:ℚ)/32768000000, (3718600855441037:ℚ)/5242880000000, (44165928773505299:ℚ)/65536000000000, (583269196989213017:ℚ)/917504000000000, (1775292939854587081:ℚ)/2981888000000000, (792248990765152049:ℚ)/1431306240000000, (6701671177013360557:ℚ)/13120307200000000, (8766656606749589533:ℚ)/18743296000000000, (1791546056824850197:ℚ)/4217241600000000, (7169263804645945251:ℚ)/18743296000000000, (4475968420249023179:ℚ)/13120307200000000, (2154751907237682379:ℚ)/7156531200000000, (783011532630351691:ℚ)/2981888000000000, (207235382359961063:ℚ)/917504000000000, (12523939943195269:ℚ)/65536000000000, (4152715732778879:ℚ)/26214400000000, (209550057367037:ℚ)/1638400000000],
  [(354934575147939:ℚ)/3276800000000, (2321178800213349:ℚ)/26214400000000, (4573525936304809:ℚ)/65536000000000, (6834434395496459:ℚ)/131072000000000, (106435420576605137:ℚ)/2981888000000000, (48897098156226451:ℚ)/2385510400000000, (86451229061106303:ℚ)/13120307200000000, (-112739149838993391:ℚ)/18743296000000000, (-10142257794590349:ℚ)/585728000000000, (-512250138741054801:ℚ)/18743296000000000, (-94695944732426451:ℚ)/2624061440000000, (-14868809874106581:ℚ)/340787200000000, (-149127026973944161:ℚ)/2981888000000000, (-50726362615510669:ℚ)/917504000000000, (-3901055545367497:ℚ)/65536000000000, (-1646131309289253:ℚ)/26214400000000, (-213545360973531:ℚ)/3276800000000],
  [(-16580859549211:ℚ)/3276800000000, (-144527429475183:ℚ)/26214400000000, (-77013666031521:ℚ)/13107200000000, (-161254384321021:ℚ)/26214400000000, (-540592126425127:ℚ)/85196800000000, (-2202399283399359:ℚ)/340787200000000, (-12201258927611397:ℚ)/1874329600000000, (-24337705472209543:ℚ)/3748659200000000, (-375873420059211:ℚ)/58572800000000, (-943251103104657:ℚ)/149946368000000, (-11468936258747611:ℚ)/1874329600000000, (-2013566622046417:ℚ)/340787200000000, (-482685071441593:ℚ)/85196800000000, (-28288657194743:ℚ)/5242880000000, (-66904107218559:ℚ)/13107200000000, (-125748049108961:ℚ)/26214400000000, (-14673445402037:ℚ)/3276800000000],
  [(-595162623409:ℚ)/3276800000000, (-4572650700699:ℚ)/26214400000000, (-6531291212893:ℚ)/39321600000000, (-4111224190657:ℚ)/26214400000000, (-12508721032777:ℚ)/85196800000000, (-27860620067869:ℚ)/204472320000000, (-21351680868753:ℚ)/170393600000000, (-7779292520437:ℚ)/68157440000000, (-16436026135037:ℚ)/159744000000000, (-12019017045439:ℚ)/131072000000000, (-2749408512259:ℚ)/34078720000000, (-71496775653839:ℚ)/1022361600000000, (-1014691202939:ℚ)/17039360000000, (-6501479828827:ℚ)/131072000000000, (-7893934975247:ℚ)/196608000000000, (-818994276357:ℚ)/26214400000000, (-75080141127:ℚ)/3276800000000],
  [(-798382291:ℚ)/655360000000, (-1078928677:ℚ)/1048576000000, (-11085393431:ℚ)/13107200000000, (-122982821473:ℚ)/183500800000000, (-23103473167:ℚ)/45875200000000, (-12736411691:ℚ)/36700160000000, (-18468288443:ℚ)/91750400000000, (-1755032299:ℚ)/26214400000000, (91095171:ℚ)/1638400000000, (4356120251:ℚ)/26214400000000, (194330567:ℚ)/734003200000, (64497300743:ℚ)/183500800000000, (19571584247:ℚ)/45875200000000, (90019962257:ℚ)/183500800000000, (7127544103:ℚ)/13107200000000, (3076704841:ℚ)/5242880000000, (2032666027:ℚ)/3276800000000],
  [(13303721:ℚ)/3276800000000, (130330711:ℚ)/26214400000000, (3016199:ℚ)/524288000000, (235125447:ℚ)/36700160000000, (1591266399:ℚ)/229376000000000, (1348875189:ℚ)/183500800000000, (702219683:ℚ)/91750400000000, (205866961:ℚ)/26214400000000, (6518867:ℚ)/819200000000, (1045314923:ℚ)/131072000000000, (726138941:ℚ)/91750400000000, (285662351:ℚ)/36700160000000, (348275901:ℚ)/45875200000000, (1348181661:ℚ)/183500800000000, (462509109:ℚ)/65536000000000, (35287253:ℚ)/5242880000000, (20885999:ℚ)/3276800000000],
  [(38883:ℚ)/655360000000, (304759:ℚ)/5242880000000, (3697369:ℚ)/65536000000000, (7114029:ℚ)/131072000000000, (1696587:ℚ)/32768000000000, (1284111:ℚ)/26214400000000, (602487:ℚ)/13107200000000, (5606873:ℚ)/131072000000000, (20209:ℚ)/512000000000, (4731063:ℚ)/131072000000000, (428521:ℚ)/13107200000000, (768193:ℚ)/26214400000000, (850677:ℚ)/32768000000000, (2974179:ℚ)/131072000000000, (1279239:ℚ)/65536000000000, (431613:ℚ)/26214400000000, (44369:ℚ)/3276800000000],
  [(549:ℚ)/3276800000000, (3807:ℚ)/26214400000000, (1627:ℚ)/13107200000000, (2733:ℚ)/26214400000000, (561:ℚ)/6553600000000, (1787:ℚ)/26214400000000, (681:ℚ)/13107200000000, (969:ℚ)/26214400000000, (19:ℚ)/819200000000, (279:ℚ)/26214400000000, (-9:ℚ)/13107200000000, (-283:ℚ)/26214400000000, (-129:ℚ)/6553600000000, (-717:ℚ)/26214400000000, (-443:ℚ)/13107200000000, (-1023:ℚ)/26214400000000, (-141:ℚ)/3276800000000],
  [(-1:ℚ)/3276800000000, (-1:ℚ)/3276800000000, (-1:ℚ)/3276800000000, (-1:ℚ)/3276800000000, (-1:ℚ)/3276800000000, (-1:ℚ)/3276800000000, (-1:ℚ)/3276800000000, (-1:ℚ)/3276800000000, (-1:ℚ)/3276800000000, (-1:ℚ)/3276800000000, (-1:ℚ)/3276800000000, (-1:ℚ)/3276800000000, (-1:ℚ)/3276800000000, (-1:ℚ)/3276800000000, (-1:ℚ)/3276800000000, (-1:ℚ)/3276800000000, (-1:ℚ)/3276800000000]]
noncomputable def bernsteinMatrix : List (List ℚ) := [
  [(24281234781211:ℚ)/32768000000, (3718600855441037:ℚ)/5242880000000, (44165928773505299:ℚ)/65536000000000, (583269196989213017:ℚ)/917504000000000, (1775292939854587081:ℚ)/2981888000000000, (792248990765152049:ℚ)/1431306240000000, (6701671177013360557:ℚ)/13120307200000000, (8766656606749589533:ℚ)/18743296000000000, (1791546056824850197:ℚ)/4217241600000000, (7169263804645945251:ℚ)/18743296000000000, (4475968420249023179:ℚ)/13120307200000000, (2154751907237682379:ℚ)/7156531200000000, (783011532630351691:ℚ)/2981888000000000, (207235382359961063:ℚ)/917504000000000, (12523939943195269:ℚ)/65536000000000, (4152715732778879:ℚ)/26214400000000, (209550057367037:ℚ)/1638400000000],
  [(19779922400116739:ℚ)/26214400000000, (151065213017854829:ℚ)/209715200000000, (357900956124347201:ℚ)/524288000000000, (4713994616682179349:ℚ)/7340032000000000, (220135060606358489:ℚ)/367001600000000, (31836650925074761313:ℚ)/57252249600000000, (53699820645167990759:ℚ)/104962457600000000, (70020513704157722873:ℚ)/149946368000000000, (17824180248097188829:ℚ)/42172416000000000, (56841860298426507207:ℚ)/149946368000000000, (35334267638330053177:ℚ)/104962457600000000, (1301982326965016987:ℚ)/4404019200000000, (873566462009838481:ℚ)/3407872000000000, (45918762750405081:ℚ)/209715200000000, (19258092800038931:ℚ)/104857600000000, (31575594552941779:ℚ)/209715200000000, (3139255556899061:ℚ)/26214400000000],
  [(35227709276938581:ℚ)/45875200000000, (6708848049172043:ℚ)/9175040000000, (126827561888212443:ℚ)/183500800000000, (37189243075058159:ℚ)/57344000000000, (3602452109681413913:ℚ)/5963776000000000, (999066494495095141:ℚ)/1789132800000000, (13440467339093468567:ℚ)/26240614400000000, (73484231494217099:ℚ)/157696000000000, (31015660570002617959:ℚ)/73801728000000000, (12314733073188187581:ℚ)/32800768000000000, (348378500421504257:ℚ)/1049624576000000, (9976829232846577:ℚ)/34406400000000, (1490252839095127319:ℚ)/5963776000000000, (48594246899654063:ℚ)/229376000000000, (161514204527901129:ℚ)/917504000000000, (10217516924187:ℚ)/71680000000, (5112656120168659:ℚ)/45875200000000],
  [(35832115133242411:ℚ)/45875200000000, (272270314275104723:ℚ)/367001600000000, (275037295769185423:ℚ)/393216000000000, (240240925528427293:ℚ)/367001600000000, (3626342368292148591:ℚ)/5963776000000000, (2674187585317549351:ℚ)/4771020800000000, (537992806812349787:ℚ)/1049624576000000, (121958244340437186543:ℚ)/262406144000000000, (2370919677285913609:ℚ)/5677056000000000, (97503090774961198177:ℚ)/262406144000000000, (8579585838996282189:ℚ)/26240614400000000, (1355413711655021257:ℚ)/4771020800000000, (290110263034882989:ℚ)/1192755200000000, (75072708548705811:ℚ)/367001600000000, (463056536878501831:ℚ)/2752512000000000, (49307004062903197:ℚ)/367001600000000, (4724259523027661:ℚ)/45875200000000],
  [(910698304501941:ℚ)/1146880000000, (690280377871491:ℚ)/917504000000, (243439343558245043:ℚ)/344064000000000, (530223769815319191:ℚ)/802816000000000, (3192743602893064799:ℚ)/5218304000000000, (234768923506520033:ℚ)/417464320000000, (58856677522821880707:ℚ)/114802688000000000, (690777348335939873:ℚ)/1490944000000000, (1913191599982311613:ℚ)/4612608000000000, (547889233145905123:ℚ)/1490944000000000, (295536471644361281:ℚ)/918421504000000, (2901401768572326099:ℚ)/10436608000000000, (1233426627372003521:ℚ)/5218304000000000, (158207115585300037:ℚ)/802816000000000, (55133094223038221:ℚ)/344064000000000, (2889815064311321:ℚ)/22937600000000, (2705305668530179:ℚ)/28672000000000],
  [(9253752508337441:ℚ)/11468800000000, (69969569666994371:ℚ)/91750400000000, (492291558056141437:ℚ)/688128000000000, (2138949500438926467:ℚ)/3211264000000000, (917489694865736029:ℚ)/1490944000000000, (672705785484523451:ℚ)/1192755200000000, (4707434392778860021:ℚ)/9184215040000000, (30283233203735161943:ℚ)/65601536000000000, (1519142724275702147:ℚ)/3690086400000000, (952936789650208369:ℚ)/2624061440000000, (14529138681577950967:ℚ)/45921075200000000, (324067972945147877:ℚ)/1192755200000000, (341870979775421683:ℚ)/1490944000000000, (608143445249092573:ℚ)/3211264000000000, (104641333482379459:ℚ)/688128000000000, (10775899749755229:ℚ)/91750400000000, (981331702070791:ℚ)/11468800000000],
  [(2349574844833191:ℚ)/2867200000000, (632963253538287:ℚ)/819200000000, (4975518146578523:ℚ)/6881280000000, (134766392342189379:ℚ)/200704000000000, (1614223383786303949:ℚ)/2609152000000000, (885092610595595953:ℚ)/1565491200000000, (5880146257532907527:ℚ)/11480268800000000, (13180295825547453:ℚ)/28672000000000, (1883574192019836229:ℚ)/4612608000000000, (133662194418111241:ℚ)/372736000000000, (3567788724813220041:ℚ)/11480268800000000, (415130040997064689:ℚ)/1565491200000000, (579296177374815907:ℚ)/2609152000000000, (36426773306807651:ℚ)/200704000000000, (3531753294829067:ℚ)/24576000000000, (623538790423609:ℚ)/5734400000000, (219672200261457:ℚ)/2867200000000],
  [(340735202394481:ℚ)/409600000000, (512819220281113:ℚ)/655360000000, (17952049395237431:ℚ)/24576000000000, (77600867725467537:ℚ)/114688000000000, (231744877275130003:ℚ)/372736000000000, (506787671840398933:ℚ)/894566400000000, (839028820094353051:ℚ)/1640038400000000, (16491165033062113:ℚ)/36044800000000, (266731500542232799:ℚ)/658944000000000, (828942819527523439:ℚ)/2342912000000000, (500100243267356213:ℚ)/1640038400000000, (6605401184818217:ℚ)/25559040000000, (15993614090938649:ℚ)/74547200000000, (19888589052909503:ℚ)/114688000000000, (3321749760661241:ℚ)/24576000000000, (327191960866227:ℚ)/3276800000000, (5529923472971:ℚ)/81920000000],
  [(21608422286591:ℚ)/25600000000, (40556750304461:ℚ)/51200000000, (1133049512063927:ℚ)/1536000000000, (174475957721457:ℚ)/256000000000, (14549752733480599:ℚ)/23296000000000, (17430925098719:ℚ)/30720000000, (7478869390859629:ℚ)/14643200000000, (16660329135265003:ℚ)/36608000000000, (33027837335434043:ℚ)/82368000000000, (12768343405004023:ℚ)/36608000000000, (30633993737688501:ℚ)/102502400000000, (3515086122455893:ℚ)/13977600000000, (4818861344247649:ℚ)/23296000000000, (295924709449379:ℚ)/1792000000000, (194197702771481:ℚ)/1536000000000, (929700367381:ℚ)/10240000000, (1490689701669:ℚ)/25600000000]]
noncomputable def entry (m : List (List ℚ)) (i j : ℕ) : ℚ :=
  (m.getD i []).getD j 0
noncomputable def a (i : Fin 9) (j : Fin 17) : ℚ := entry powerMatrix i j
noncomputable def r (i : Fin 9) (j : Fin 17) : ℚ := entry rowMatrix i j
noncomputable def b (i : Fin 9) (j : Fin 17) : ℚ := entry bernsteinMatrix i j
theorem bernstein_checked :
    (∀ i : Fin 9, ∀ j : Fin 17,
      r i j=RH101Proof.TaoZetaNumerics.bernsteinTransform 16 (a i) j) ∧
    (∀ i : Fin 9, ∀ j : Fin 17,
      b i j=RH101Proof.TaoZetaNumerics.bernsteinTransform 8 (fun u => r u j) i) ∧
    (∀ i : Fin 9, ∀ j : Fin 17, (1:ℚ)≤b i j) := by decide +kernel
end RH101Numerical

/- Checked component: RH101PolynomialIdentity.lean -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
namespace RH101Numerical
noncomputable def c (n : ℕ) : ℝ := (rounded n:ℝ)/(10^8:ℝ)
noncomputable def imaginaryValue (x y : ℝ) : ℝ :=
    (-16760310223:ℝ)/25000000*x^1*y^0 +
    (236258887:ℝ)/2000000*x^1*y^1 +
    (68453791203:ℝ)/100000000*x^1*y^2 +
    (-22817930401:ℝ)/100000000*x^3*y^0 +
    (-2020567019:ℝ)/5000000*x^1*y^3 +
    (2020567019:ℝ)/5000000*x^3*y^1 +
    (28724961:ℝ)/1250000*x^1*y^4 +
    (-28724961:ℝ)/625000*x^3*y^2 +
    (28724961:ℝ)/6250000*x^5*y^0 +
    (395423331:ℝ)/10000000*x^1*y^5 +
    (-131807777:ℝ)/1000000*x^3*y^3 +
    (395423331:ℝ)/10000000*x^5*y^1 +
    (-140828303:ℝ)/12500000*x^1*y^6 +
    (140828303:ℝ)/2500000*x^3*y^4 +
    (-422484909:ℝ)/12500000*x^5*y^2 +
    (20118329:ℝ)/12500000*x^7*y^0 +
    (25558:ℝ)/390625*x^1*y^7 +
    (-178906:ℝ)/390625*x^3*y^5 +
    (178906:ℝ)/390625*x^5*y^3 +
    (-25558:ℝ)/390625*x^7*y^1 +
    (47660877:ℝ)/100000000*x^1*y^8 +
    (-111208713:ℝ)/25000000*x^3*y^6 +
    (333626139:ℝ)/50000000*x^5*y^4 +
    (-47660877:ℝ)/25000000*x^7*y^2 +
    (5295653:ℝ)/100000000*x^9*y^0 +
    (-398551:ℝ)/5000000*x^1*y^9 +
    (1195653:ℝ)/1250000*x^3*y^7 +
    (-25108713:ℝ)/12500000*x^5*y^5 +
    (1195653:ℝ)/1250000*x^7*y^3 +
    (-398551:ℝ)/5000000*x^9*y^1 +
    (-123717:ℝ)/100000000*x^1*y^10 +
    (371151:ℝ)/20000000*x^3*y^8 +
    (-2598057:ℝ)/50000000*x^5*y^6 +
    (371151:ℝ)/10000000*x^7*y^4 +
    (-123717:ℝ)/20000000*x^9*y^2 +
    (11247:ℝ)/100000000*x^11*y^0 +
    (48321:ℝ)/25000000*x^1*y^11 +
    (-177177:ℝ)/5000000*x^3*y^9 +
    (1594593:ℝ)/12500000*x^5*y^7 +
    (-1594593:ℝ)/12500000*x^7*y^5 +
    (177177:ℝ)/5000000*x^9*y^3 +
    (-48321:ℝ)/25000000*x^11*y^1 +
    (-5343:ℝ)/25000000*x^1*y^12 +
    (58773:ℝ)/12500000*x^3*y^10 +
    (-528957:ℝ)/25000000*x^5*y^8 +
    (176319:ℝ)/6250000*x^7*y^6 +
    (-58773:ℝ)/5000000*x^9*y^4 +
    (16029:ℝ)/12500000*x^11*y^2 +
    (-411:ℝ)/25000000*x^13*y^0 +
    (-147:ℝ)/25000000*x^1*y^13 +
    (1911:ℝ)/12500000*x^3*y^11 +
    (-21021:ℝ)/25000000*x^5*y^9 +
    (9009:ℝ)/6250000*x^7*y^7 +
    (-21021:ℝ)/25000000*x^9*y^5 +
    (1911:ℝ)/12500000*x^11*y^3 +
    (-147:ℝ)/25000000*x^13*y^1 +
    (69:ℝ)/20000000*x^1*y^14 +
    (-2093:ℝ)/20000000*x^3*y^12 +
    (69069:ℝ)/100000000*x^5*y^10 +
    (-29601:ℝ)/20000000*x^7*y^8 +
    (23023:ℝ)/20000000*x^9*y^6 +
    (-6279:ℝ)/20000000*x^11*y^4 +
    (483:ℝ)/20000000*x^13*y^2 +
    (-23:ℝ)/100000000*x^15*y^0 +
    (-1:ℝ)/3125000*x^1*y^15 +
    (7:ℝ)/625000*x^3*y^13 +
    (-273:ℝ)/3125000*x^5*y^11 +
    (143:ℝ)/625000*x^7*y^9 +
    (-143:ℝ)/625000*x^9*y^7 +
    (273:ℝ)/3125000*x^11*y^5 +
    (-7:ℝ)/625000*x^13*y^3 +
    (1:ℝ)/3125000*x^15*y^1
lemma complex_identity (x y : ℝ) :
    (∑ n ∈ Finset.range 32, (c n:ℂ)*((y:ℂ)-Complex.I*x)^n)+
      (RH101Proof.CertifiedLocalPolynomial.bivariatePowerValue 8 16 a
        (4*x^2) (y+1/2):ℂ)=Complex.I*(imaginaryValue x y:ℂ) := by
  norm_num [c,rounded,roundedNumerators,Finset.sum_range_succ,
    RH101Proof.CertifiedLocalPolynomial.bivariatePowerValue,
    a,entry,powerMatrix,Fin.sum_univ_succ,imaginaryValue]
  push_cast
  ring_nf
  norm_num [Complex.I_pow_eq_pow_mod]
  try simp only [Complex.I_sq,Complex.I_pow_three,pow_zero,pow_one]
  apply Complex.ext <;>
    simp [←Complex.ofReal_pow,Complex.mul_re,Complex.mul_im] <;> ring
lemma power_identity (s : ℂ) :
    -(RH101Proof.CertifiedLocalXi.rotatedPolynomial c (201/2) s).re=
      RH101Proof.CertifiedLocalPolynomial.bivariatePowerValue 8 16 a
        (4*(s.re-1/2)^2) (s.im-100) := by
  have h := complex_identity (s.re-1/2) (s.im-201/2)
  have hw : RH101Proof.CertifiedLocalXi.rotatedVariable (201/2) s=
      ((s.im-201/2:ℝ):ℂ)-Complex.I*((s.re-1/2:ℝ):ℂ) := by
    apply Complex.ext <;> simp [RH101Proof.CertifiedLocalXi.rotatedVariable,
      RH101Proof.CertifiedLocalXi.center] <;> ring
  unfold RH101Proof.CertifiedLocalXi.rotatedPolynomial
  simp only [hw]
  have hr := congrArg Complex.re h
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,
    Complex.I_re,Complex.I_im,Complex.ofReal_im,zero_mul,mul_zero,sub_zero] at hr
  have he : s.im-201/2+1/2=s.im-100 := by ring
  rw [he] at hr
  linarith
end RH101Numerical

/- Checked component: RH101AnalyticApproximation.lean -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option linter.unusedSimpArgs false
namespace RH101Proof.CertifiedLocalXi
open Complex Metric
lemma center_norm_bound_1000 (T : ℝ) (hT : |T| ≤ 1000) : ‖center T‖ ≤ 1001 := by
  have h := Complex.norm_le_abs_re_add_abs_im (center T)
  norm_num [center] at h
  unfold center
  linarith
lemma center_sub_one_norm_bound_1000 (T : ℝ) (hT : |T| ≤ 1000) : ‖center T-1‖ ≤ 1001 := by
  have h := Complex.norm_le_abs_re_add_abs_im (center T-1)
  norm_num [center] at h
  unfold center
  linarith
lemma xi_circle_bound_1000 (T : ℝ) (hT : |T| ≤ 1000) (z : ℂ)
    (hz : z ∈ Metric.sphere (center T) 24) : ‖xi z‖ ≤ 400000000 := by
  have hzdist : ‖z-center T‖=24 := mem_sphere_iff_norm.mp hz
  have hre : |z.re-1/2| ≤ 24 := by
    have h := Complex.abs_re_le_norm (z-center T)
    rw [hzdist] at h
    simpa [center] using h
  have hΛ := TaoZetaWide.norm_completedRiemannZeta₀_le (s:=z)
    (by linarith [(abs_le.mp hre).1]) (by linarith [(abs_le.mp hre).2])
  have hz0 : ‖z‖ ≤ 1025 := by
    have h := norm_add_le (z-center T) (center T)
    rw [sub_add_cancel,hzdist] at h
    linarith [center_norm_bound_1000 T hT]
  have hz1 : ‖z-1‖ ≤ 1025 := by
    have h := norm_add_le (z-center T) (center T-1)
    rw [sub_add_sub_cancel,hzdist] at h
    linarith [center_sub_one_norm_bound_1000 T hT]
  unfold xi
  calc
    _ ≤ ‖(1/2:ℂ)‖+‖z*(z-1)/2*completedRiemannZeta₀ z‖ := norm_add_le _ _
    _ = 1/2+‖z‖*‖z-1‖/2*‖completedRiemannZeta₀ z‖ := by
      simp only [norm_mul,norm_div]
      norm_num
    _ ≤ 1/2+1025*1025/2*(640:ℝ) := by gcongr
    _ ≤ _ := by norm_num
lemma local_tail_norm_32 (T : ℝ) (hT : |T|≤1000) (z : ℂ)
    (hz : ‖z-center T‖≤1) :
    ‖RH101Proof.CertifiedComplexTaylor.remainder xi (center T) 32 z‖≤3/10^36 := by
  have h := RH101Proof.CertifiedComplexTaylor.remainder_bound xi xi_entire (center T)
    24 400000000 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (xi_circle_bound_1000 T hT) 32 z hz
  apply h.trans
  norm_num
end RH101Proof.CertifiedLocalXi
namespace RH101Numerical
open Complex
lemma coefficients_rounded (n : ℕ) (hn : n<32) :
    ‖(normalizationNat:ℂ)*RH101Proof.CertifiedTaylorQuadrature.coefficient
      RH101Proof.CertifiedLocalXi.xi (RH101Proof.CertifiedLocalXi.center (201/2)) n*
      I^n-(proposed n:ℂ)‖≤1/10^6 := by
  have hg := RH101Proof.CertifiedGlobalMoments.local_coefficient_error
    CertifiedGlobalMomentEnclosure.candidateMoment
    TaoFivePrimes.rh14to100_moments_enclosed (201/2) (by norm_num) n
  have hr := RH101Proof.CertifiedPolynomialTranslation.global_rotated_error
    CertifiedGlobalMomentEnclosure.candidateMoment (normalizationNat:ℝ)
    (201/2) (proposed n) (1/10^8) n (translated_error n hn)
  have he :
      (normalizationNat:ℂ)*RH101Proof.CertifiedTaylorQuadrature.coefficient
        RH101Proof.CertifiedLocalXi.xi (RH101Proof.CertifiedLocalXi.center (201/2)) n*
        I^n-(proposed n:ℂ)=
      (normalizationNat:ℂ)*(RH101Proof.CertifiedTaylorQuadrature.coefficient
        RH101Proof.CertifiedLocalXi.xi (RH101Proof.CertifiedLocalXi.center (201/2)) n-
        RH101Proof.CertifiedTaylorQuadrature.coefficient
          (RH101Proof.CertifiedGlobalMoments.xiPolynomial
            CertifiedGlobalMomentEnclosure.candidateMoment)
          (RH101Proof.CertifiedLocalXi.center (201/2)) n)*I^n+
      ((normalizationNat:ℂ)*RH101Proof.CertifiedTaylorQuadrature.coefficient
        (RH101Proof.CertifiedGlobalMoments.xiPolynomial
          CertifiedGlobalMomentEnclosure.candidateMoment)
        (RH101Proof.CertifiedLocalXi.center (201/2)) n*I^n-(proposed n:ℂ)) := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  have hnS : 0≤(normalizationNat:ℝ) := Nat.cast_nonneg _
  have hS : (normalizationNat:ℝ)=(10:ℝ)^33 := by norm_num [normalizationNat]
  have hfirst : ‖(normalizationNat:ℂ)*(RH101Proof.CertifiedTaylorQuadrature.coefficient
        RH101Proof.CertifiedLocalXi.xi (RH101Proof.CertifiedLocalXi.center (201/2)) n-
        RH101Proof.CertifiedTaylorQuadrature.coefficient
          (RH101Proof.CertifiedGlobalMoments.xiPolynomial
            CertifiedGlobalMomentEnclosure.candidateMoment)
          (RH101Proof.CertifiedLocalXi.center (201/2)) n)*I^n‖≤1/10^8 := by
    simp only [norm_mul,norm_pow,norm_I,one_pow,mul_one]
    rw [show ‖(normalizationNat:ℂ)‖=(normalizationNat:ℝ) by
      norm_cast]
    calc
      _ ≤ (normalizationNat:ℝ)*(1/10^41) := mul_le_mul_of_nonneg_left hg hnS
      _ ≤ 1/10^8 := by rw [hS]; norm_num
  have hsecond : ‖(normalizationNat:ℂ)*RH101Proof.CertifiedTaylorQuadrature.coefficient
      (RH101Proof.CertifiedGlobalMoments.xiPolynomial CertifiedGlobalMomentEnclosure.candidateMoment)
      (RH101Proof.CertifiedLocalXi.center (201/2)) n*I^n-(proposed n:ℂ)‖≤1/10^8 := by
    simpa only [Complex.ofReal_natCast] using hr
  linarith
lemma xi_approximation (z : ℂ)
    (hz : ‖z-RH101Proof.CertifiedLocalXi.center (201/2)‖≤1) :
    ‖(normalizationNat:ℂ)*RH101Proof.CertifiedLocalXi.xi z-
      RH101Proof.CertifiedLocalXi.rotatedPolynomial proposed (201/2) z‖≤1/100 := by
  have he :
      (normalizationNat:ℂ)*RH101Proof.CertifiedLocalXi.xi z-
        RH101Proof.CertifiedLocalXi.rotatedPolynomial proposed (201/2) z=
      (normalizationNat:ℂ)*RH101Proof.CertifiedComplexTaylor.remainder
        RH101Proof.CertifiedLocalXi.xi (RH101Proof.CertifiedLocalXi.center (201/2)) 32 z+
      ((normalizationNat:ℂ)*RH101Proof.CertifiedComplexTaylor.polynomial
        RH101Proof.CertifiedLocalXi.xi (RH101Proof.CertifiedLocalXi.center (201/2)) 32 z-
        RH101Proof.CertifiedLocalXi.rotatedPolynomial proposed (201/2) z) := by
    unfold RH101Proof.CertifiedComplexTaylor.remainder
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  have ht := RH101Proof.CertifiedLocalXi.local_tail_norm_32 (201/2) (by norm_num) z hz
  have hp := RH101Proof.CertifiedLocalXi.rounded_polynomial_error
    (normalizationNat:ℝ) (201/2) proposed coefficients_rounded z hz
  have hfirst : ‖(normalizationNat:ℂ)*RH101Proof.CertifiedComplexTaylor.remainder
      RH101Proof.CertifiedLocalXi.xi (RH101Proof.CertifiedLocalXi.center (201/2)) 32 z‖≤3/1000 := by
    rw [norm_mul]
    rw [show ‖(normalizationNat:ℂ)‖=(10:ℝ)^33 by norm_num [normalizationNat]]
    calc
      _ ≤ (10:ℝ)^33*(3/10^36) := mul_le_mul_of_nonneg_left ht (by positivity)
      _ ≤ 3/1000 := by norm_num
  have hsecond : ‖(normalizationNat:ℂ)*RH101Proof.CertifiedComplexTaylor.polynomial
      RH101Proof.CertifiedLocalXi.xi (RH101Proof.CertifiedLocalXi.center (201/2)) 32 z-
      RH101Proof.CertifiedLocalXi.rotatedPolynomial proposed (201/2) z‖≤32/10^6 := by
    simpa only [Complex.ofReal_natCast] using hp
  linarith
end RH101Numerical

/- Checked component: RH101RectangleRoot.lean -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
namespace RH101Numerical
attribute [local irreducible] a r b
lemma candidate_negative (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : 100 ≤ s.im) (hb : s.im ≤ 101) :
    1≤-(RH101Proof.CertifiedLocalXi.rotatedPolynomial proposed (201/2) s).re := by
  let x : Set.Icc (0:ℝ) 1 := ⟨4*(s.re-1/2)^2,⟨by positivity,by
    nlinarith [mul_nonneg h0 (show 0≤1-s.re by linarith)]⟩⟩
  let y : Set.Icc (0:ℝ) 1 := ⟨s.im-100,⟨by linarith,by linarith⟩⟩
  have hr : ∀ i, r i=RH101Proof.TaoZetaNumerics.bernsteinTransform 16 (a i) := by
    intro i
    funext j
    exact bernstein_checked.1 i j
  have hc : ∀ j, (fun i => b i j)=RH101Proof.TaoZetaNumerics.bernsteinTransform 8
      (fun i => r i j) := by
    intro j
    funext i
    exact bernstein_checked.2.1 i j
  have hl : ∀ i j, (1:ℝ)≤(b i j:ℝ) := by
    intro i j
    exact_mod_cast bernstein_checked.2.2 i j
  have h := RH101Proof.CertifiedLocalPolynomial.bivariate_bernstein_lower
    8 16 a r b hr hc 1 hl x y
  have he : c=proposed := rfl
  rw [←he,power_identity]
  exact h
lemma rectangle_norm (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : 100 ≤ s.im) (hb : s.im ≤ 101) :
    ‖s-RH101Proof.CertifiedLocalXi.center (201/2)‖≤1 := by
  have hx : |s.re-1/2|≤1/2 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hy : |s.im-201/2|≤1/2 := abs_le.mpr ⟨by linarith,by linarith⟩
  have h := Complex.norm_le_abs_re_add_abs_im
    (s-RH101Proof.CertifiedLocalXi.center (201/2))
  have he : ‖s-RH101Proof.CertifiedLocalXi.center (201/2)‖≤
      |s.re-1/2|+|s.im-201/2| := by
    simpa [RH101Proof.CertifiedLocalXi.center] using h
  linarith
lemma xi_nonzero_rectangle (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : 100 ≤ s.im) (hb : s.im ≤ 101) : RH101Proof.CertifiedLocalXi.xi s≠0 := by
  have he := xi_approximation s (rectangle_norm s h0 h1 ha hb)
  have hp := candidate_negative s h0 h1 ha hb
  intro hz
  rw [hz,mul_zero,zero_sub,norm_neg] at he
  have hreal := Complex.abs_re_le_norm
    (RH101Proof.CertifiedLocalXi.rotatedPolynomial proposed (201/2) s)
  have hle : -(RH101Proof.CertifiedLocalXi.rotatedPolynomial proposed (201/2) s).re≤
      |(RH101Proof.CertifiedLocalXi.rotatedPolynomial proposed (201/2) s).re| :=
    neg_le_abs _
  linarith
end RH101Numerical

theorem solution (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1)
    (ha : 100 ≤ s.im) (hb : s.im ≤ 101) : riemannZeta s≠0 :=
  RH101Proof.CertifiedLocalXi.xi_nonzero_implies_zeta h0 h1
    (RH101Numerical.xi_nonzero_rectangle s h0.le h1.le ha hb)
