-- Prove2me | solution 1 for TaoFivePrimes.rh124p5_xi_polynomial_derivative_bound
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:56:41.619125+00:00
-- url     : https://prove2.me/submissions/90201b99-b633-4858-b673-a8d960a3ba0d

/- Adapted local xi estimate for the height-106–107 slice.
The analytic foundations and proposed Mellin moments are retained from the
ACCEPTED height-14–100 pilot: original proof/certificate sometik179,
theta/Mellin foundations Gabewhigham. New local coefficients are computed
exactly at height 106.5 and will be checked by ordinary Lean proofs. -/
import Theorems.Thm_TaoFivePrimes_rh_moments_320_enclosed_tight
import Mathlib.Tactic
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Definitions.Def_TaoFivePrimes_RHLocalRationalPolynomial
import Definitions.Def_TaoFivePrimes_RH124p5RoundedCoefficients14
import Theorems.Thm_TaoFivePrimes_rh124p5_translation_precision14
import Theorems.Thm_TaoFivePrimes_rh124p5_translation_tail60
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option linter.ambiguousOpen false
noncomputable def RH124p5RoundingBound (n : ℕ) : ℝ :=
  if n < 22 then 1/10^14 else if n < 25 then 1/10^15
  else if n < 30 then 1/10^18 else 1/10^24

lemma RH124p5RoundingBound_nonneg (n : ℕ) : 0 ≤ RH124p5RoundingBound n := by
  unfold RH124p5RoundingBound
  split_ifs <;> norm_num

noncomputable def RH124p5RoundingBound60 (n : ℕ) : ℝ :=
  if n < 40 then RH124p5RoundingBound n else 1/10^32

lemma RH124p5RoundingBound60_nonneg (n : ℕ) : 0 ≤ RH124p5RoundingBound60 n := by
  unfold RH124p5RoundingBound60
  split_ifs
  · exact RH124p5RoundingBound_nonneg n
  · norm_num

namespace RH124p5Proof
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

namespace TaoZetaWide272
open ZetaSix

noncomputable def maj (t : ℝ) : ℝ :=
  if t ≤  1 then 21 / 10 * (t ^ (-138 : ℝ) * rexp (-π / t))
  else 21 / 10 * (t ^ (136 : ℝ) * rexp (-π * t))

lemma integrableOn_outer :
    IntegrableOn (fun t : ℝ => t ^ (136 : ℝ) * rexp (-π * t)) (Ioi 1) := by
  simpa only [Real.rpow_ofNat] using
    (ZetaSix.integrableOn_pow_mul_exp 136).mono_set (Ioi_subset_Ioi zero_le_one)

lemma outer_le :
    (∫ t in Ioi (1 : ℝ), t ^ (136 : ℝ) * rexp (-π * t)) ≤  (((65*10^163)) : ℝ) / (21 / 10) := by
  have h := MeasureTheory.setIntegral_mono_set
    (ZetaSix.integrableOn_pow_mul_exp 136)
    (Filter.Eventually.of_forall (fun x : ℝ => by positivity :
      ∀ x : ℝ, 0 ≤  x ^ 136 * rexp (-π * x)))
    (Filter.Eventually.of_forall (Ioi_subset_Ioi (show (0 : ℝ) ≤  1 by norm_num)))
  simp only [Real.rpow_ofNat] at *
  rw [ZetaSix.integral_pow_mul_exp] at h
  have hp : (157/50 : ℝ) ^ 137 ≤ π ^ 137 := pow_le_pow_left₀ (by norm_num) (by linarith [Real.pi_gt_d2] : (157/50:ℝ)≤π) 137
  have hpi : (0 : ℝ) < π ^ 137 := by positivity
  have hb : (Nat.factorial 136 : ℝ) / π ^ 137 ≤  ((65*10^163)) / (21 / 10) := by
    rw [div_le_iff₀ hpi]
    norm_num [Nat.factorial] at *
    nlinarith
  exact h.trans hb

/-- The kernel of the substituted integral: `u^{-1/2} e^{-π u}` cut off below `1`. -/
private noncomputable def gInd : ℝ → ℝ :=
  Set.indicator (Ioi 1) fun u => u ^ (136 : ℝ) * rexp (-π * u)

private lemma gInd_integrableOn : IntegrableOn gInd (Ioi (0 : ℝ)) := by
  rw [gInd]
  exact (integrableOn_outer.integrable_indicator measurableSet_Ioi).integrableOn

private lemma integral_gInd : (∫ y in Ioi (0 : ℝ), gInd y)
    = ∫ u in Ioi (1 : ℝ), u ^ (136 : ℝ) * rexp (-π * u) := by
  rw [gInd, MeasureTheory.integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, Set.Ioi_inter_Ioi]
  norm_num

private lemma cov_ptwise (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
    (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • gInd (x ^ (-1 : ℝ))
      = (Ioo (0 : ℝ) 1).indicator (fun x => x ^ (-138 : ℝ) * rexp (-π / x)) x := by
  have hx0 : 0 < x := hx
  have hinv : x ^ (-1 : ℝ) = x⁻¹ := by rw [Real.rpow_neg_one]
  rcases lt_or_ge x 1 with h | h
  · have h1 : (1 : ℝ) < x⁻¹ := by rw [lt_inv_comm₀ (by norm_num) hx0]; simpa using h
    rw [Set.indicator_of_mem (show x ∈ Ioo (0 : ℝ) 1 from ⟨hx0, h⟩), gInd, hinv,
      Set.indicator_of_mem (mem_Ioi.mpr h1)]
    have hd : -π * x⁻¹ = -π / x := by field_simp
    have hpow : (x⁻¹) ^ (136 : ℝ) = x ^ (-136 : ℝ) := by
      rw [← Real.rpow_neg_one x, ← Real.rpow_mul hx0.le]
      norm_num
    rw [hd, hpow, smul_eq_mul]
    have hxx : x ^ ((-1 : ℝ) - 1) * x ^ (-136 : ℝ) = x ^ (-138 : ℝ) := by
      rw [← Real.rpow_add hx0]
      norm_num
    rw [show |(-1 : ℝ)| = 1 by norm_num, one_mul, ← mul_assoc, hxx]
  · have h1 : x⁻¹ ≤  1 := by rw [inv_le_one_iff₀]; right; exact h
    rw [Set.indicator_of_notMem (by simp; intro _; exact h), gInd, hinv,
      Set.indicator_of_notMem (by simp [not_lt.2 h1])]
    simp

lemma integrableOn_inner :
    IntegrableOn (fun x : ℝ => x ^ (-138 : ℝ) * rexp (-π / x)) (Ioc (0 : ℝ) 1) := by
  have h1 : IntegrableOn
      (fun x : ℝ => (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • gInd (x ^ (-1 : ℝ))) (Ioi 0) :=
    (MeasureTheory.integrableOn_Ioi_comp_rpow_iff gInd (by norm_num : (-1 : ℝ) ≠ 0)).mpr
      gInd_integrableOn
  have h2 : IntegrableOn
      ((Ioo (0 : ℝ) 1).indicator fun x => x ^ (-138 : ℝ) * rexp (-π / x)) (Ioi 0) :=
    h1.congr_fun cov_ptwise measurableSet_Ioi
  have h3 := (MeasureTheory.integrable_indicator_iff measurableSet_Ioo).mp h2
  rw [IntegrableOn, Measure.restrict_restrict measurableSet_Ioo,
    show Ioo (0 : ℝ) 1 ∩ Ioi 0 = Ioo (0 : ℝ) 1 by
      ext x; simp only [mem_inter_iff, mem_Ioo, mem_Ioi]; tauto] at h3
  rw [IntegrableOn, ← MeasureTheory.Measure.restrict_congr_set
    (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := 1))]
  exact h3

lemma integral_inner : (∫ x in Ioc (0 : ℝ) 1, x ^ (-138 : ℝ) * rexp (-π / x))
    = ∫ u in Ioi (1 : ℝ), u ^ (136 : ℝ) * rexp (-π * u) := by
  have hcov := MeasureTheory.integral_comp_rpow_Ioi gInd (by norm_num : (-1 : ℝ) ≠ 0)
  rw [integral_gInd] at hcov
  rw [setIntegral_congr_fun measurableSet_Ioi cov_ptwise] at hcov
  rw [MeasureTheory.integral_indicator measurableSet_Ioo, Measure.restrict_restrict
    measurableSet_Ioo, show Ioo (0 : ℝ) 1 ∩ Ioi 0 = Ioo (0 : ℝ) 1 by
      ext x; simp only [mem_inter_iff, mem_Ioo, mem_Ioi]; tauto] at hcov
  rw [← MeasureTheory.Measure.restrict_congr_set (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := 1))]
  exact hcov

lemma integrableOn_maj_Ioc : IntegrableOn maj (Ioc (0 : ℝ) 1) := by
  have h : IntegrableOn (fun x : ℝ => 21 / 10 * (x ^ (-138 : ℝ) * rexp (-π / x)))
      (Ioc (0 : ℝ) 1) := integrableOn_inner.const_mul (21 / 10)
  refine h.congr_fun ?_ measurableSet_Ioc
  intro t ht
  simp [maj, ht.2]

lemma integrableOn_maj_Ioi : IntegrableOn maj (Ioi (1 : ℝ)) := by
  have h : IntegrableOn (fun t : ℝ => 21 / 10 * (t ^ (136 : ℝ) * rexp (-π * t)))
      (Ioi (1 : ℝ)) := integrableOn_outer.const_mul (21 / 10)
  refine h.congr_fun ?_ measurableSet_Ioi
  intro t ht
  simp [maj, not_le.2 (mem_Ioi.mp ht)]

lemma integrableOn_maj : IntegrableOn maj (Ioi 0) := by
  rw [show Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 from (Ioc_union_Ioi_eq_Ioi zero_le_one).symm]
  exact integrableOn_maj_Ioc.union integrableOn_maj_Ioi

lemma integral_maj_le : ∫ t in Ioi (0 : ℝ), maj t ≤  (2*(65*10^163)) := by
  have hsplit : ∫ t in Ioi (0 : ℝ), maj t
      = (∫ t in Ioc (0 : ℝ) 1, maj t) + ∫ t in Ioi (1 : ℝ), maj t := by
    rw [show Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 from (Ioc_union_Ioi_eq_Ioi zero_le_one).symm]
    exact setIntegral_union (by simp [Set.disjoint_left]) measurableSet_Ioi
      integrableOn_maj_Ioc integrableOn_maj_Ioi
  have h1 : ∫ t in Ioc (0 : ℝ) 1, maj t
      = 21 / 10 * ∫ u in Ioi (1 : ℝ), u ^ (136 : ℝ) * rexp (-π * u) := by
    rw [setIntegral_congr_fun measurableSet_Ioc
      (g := fun t : ℝ => 21 / 10 * (t ^ (-138 : ℝ) * rexp (-π / t)))
      (fun t ht => by simp [maj, ht.2]), integral_const_mul, integral_inner]
  have h2 : ∫ t in Ioi (1 : ℝ), maj t
      = 21 / 10 * ∫ u in Ioi (1 : ℝ), u ^ (136 : ℝ) * rexp (-π * u) := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (g := fun t : ℝ => 21 / 10 * (t ^ (136 : ℝ) * rexp (-π * t)))
      (fun t ht => by simp [maj, not_le.2 (mem_Ioi.mp ht)]), integral_const_mul]
  rw [hsplit, h1, h2]
  have hJ := outer_le
  linarith

lemma norm_integrand_le {s : ℂ} (h0 : -272 ≤  s.re) (h1 : s.re ≤  273) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (s / 2 - 1) • P.f_modif t‖ ≤  maj t := by
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
    show (s / 2 - 1).re = s.re / 2 - 1 by simp]
  rcases lt_trichotomy t 1 with hlt | rfl | hgt
  · have hmaj : maj t = 21 / 10 * (t ^ (-138 : ℝ) * rexp (-π / t)) := by simp [maj, hlt.le]
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
    have hexp : t ^ (s.re / 2 - 3 / 2) ≤  t ^ (-138 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge ht hlt.le (by linarith)
    have hnn : (0 : ℝ) ≤  rexp (-π / t) := (Real.exp_pos _).le
    nlinarith [Real.rpow_pos_of_pos ht (-138 : ℝ), Real.rpow_pos_of_pos ht (s.re / 2 - 3 / 2)]
  · have hm : maj (1 : ℝ) = 21 / 10 * ((1 : ℝ) ^ (-138 : ℝ) * rexp (-π / 1)) := if_pos le_rfl
    rw [hm, f_modif_one]
    simp only [norm_zero, mul_zero]
    positivity
  · have hmaj : maj t = 21 / 10 * (t ^ (136 : ℝ) * rexp (-π * t)) := by
      simp [maj, not_le.2 hgt]
    rw [hmaj]
    have hstep : t ^ (s.re / 2 - 1) * ‖P.f_modif t‖
        ≤  t ^ (s.re / 2 - 1) * (21 / 10 * rexp (-π * t)) :=
      mul_le_mul_of_nonneg_left (norm_f_modif_le_of_one_lt hgt) (Real.rpow_nonneg ht.le _)
    refine hstep.trans ?_
    have hexp : t ^ (s.re / 2 - 1) ≤  t ^ (136 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hgt.le (by linarith)
    have hnn : (0 : ℝ) ≤  rexp (-π * t) := (Real.exp_pos _).le
    nlinarith [Real.rpow_pos_of_pos ht (136 : ℝ), Real.rpow_pos_of_pos ht (s.re / 2 - 1)]

/-- **Sharpened bound on the entire part of the completed zeta function.**
In the critical strip, `‖Λ₀ s‖ ≤  ((65*10^163))`. -/
theorem norm_completedRiemannZeta₀_le {s : ℂ} (h0 : -272 ≤  s.re) (h1 : s.re ≤  273) :
    ‖completedRiemannZeta₀ s‖ ≤  ((65*10^163)) := by
  have hdef : completedRiemannZeta₀ s = mellin P.f_modif (s / 2) / 2 := rfl
  rw [hdef, norm_div, Complex.norm_ofNat]
  have hb : ‖mellin P.f_modif (s / 2)‖ ≤  ∫ t in Ioi (0 : ℝ), maj t := by
    rw [mellin]
    refine norm_integral_le_of_norm_le integrableOn_maj ?_
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0 : ℝ)))] with t ht
    exact norm_integrand_le h0 h1 ht
  have := hb.trans integral_maj_le
  linarith

end TaoZetaWide272

end Height100Module17

section Height100Module18

open Complex Finset Metric
open scoped BigOperators
set_option autoImplicit false
set_option exponentiation.threshold 1024

namespace TaoZetaGlobal

lemma norm_iteratedDeriv_completedZeta (n : ℕ) :
    ‖iteratedDeriv n completedRiemannZeta₀ (1 / 2)‖ ≤ 
      n.factorial * ((65*10^163)) / (272 : ℝ) ^ n := by
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (by norm_num)
    differentiable_completedZeta₀.diffContOnCl
  intro z hz
  have habs : |z.re - 1 / 2| ≤  (272 : ℝ) := by
    have h := Complex.abs_re_le_norm (z - (1 / 2 : ℂ))
    rw [mem_sphere_iff_norm.mp hz] at h
    simpa using h
  apply TaoZetaWide272.norm_completedRiemannZeta₀_le <;> linarith [(abs_le.mp habs).1, (abs_le.mp habs).2]

noncomputable def taylorTerm (z : ℂ) (n : ℕ) : ℂ :=
  (n.factorial : ℂ)⁻¹ • (z - 1 / 2) ^ n •
    iteratedDeriv n completedRiemannZeta₀ (1 / 2)

lemma norm_taylorTerm_le (z : ℂ) (n : ℕ) :
    ‖taylorTerm z n‖ ≤  ((65*10^163)) * (‖z - 1 / 2‖ / 272) ^ n := by
  have h := norm_iteratedDeriv_completedZeta n
  have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
  unfold taylorTerm
  simp only [norm_smul, norm_inv, Complex.norm_natCast, norm_pow]
  calc
    (n.factorial : ℝ)⁻¹ * (‖z - 1 / 2‖ ^ n *
        ‖iteratedDeriv n completedRiemannZeta₀ (1 / 2)‖) ≤ 
      (n.factorial : ℝ)⁻¹ * (‖z - 1 / 2‖ ^ n *
        (n.factorial * ((65*10^163)) / (272 : ℝ) ^ n)) := by gcongr
    _ = ((65*10^163)) * (‖z - 1 / 2‖ / 272) ^ n := by
      rw [div_pow]
      field_simp

/-- A uniform certified truncation bound, with no assumptions about computed coefficients. -/
lemma norm_taylor_remainder_le (z : ℂ) (hz : ‖z - 1 / 2‖ < 272) (N : ℕ) :
    ‖completedRiemannZeta₀ z - ∑ n ∈ range N, taylorTerm z n‖ ≤ 
      ((65*10^163)) * (‖z - 1 / 2‖ / 272) ^ N / (1 - ‖z - 1 / 2‖ / 272) := by
  let q : ℝ := ‖z - 1 / 2‖ / 272
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
  have hgeo : HasSum (fun n : ℕ => (((65*10^163)) * q ^ N) * q ^ n)
      ((((65*10^163)) * q ^ N) * (1 - q)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0 hq1).mul_left (((65*10^163)) * q ^ N)
  have hbound := tsum_of_norm_bounded hgeo (fun n : ℕ => by
    calc ‖taylorTerm z (n + N)‖ ≤  ((65*10^163)) * q ^ (n + N) := norm_taylorTerm_le z (n + N)
      _ = (((65*10^163)) * q ^ N) * q ^ n := by rw [pow_add]; ring)
  simpa only [q, div_eq_mul_inv] using hbound

lemma norm_taylor_remainder_640 (z : ℂ) (hz : ‖z - 1 / 2‖ ≤  (255/2)) :
    ‖completedRiemannZeta₀ z - ∑ n ∈ range 640, taylorTerm z n‖ ≤  31 / 10 ^ 47 := by
  have hr := norm_taylor_remainder_le z (by linarith) 640
  have hq : ‖z - 1 / 2‖ / 272 ≤  (255 / 544 : ℝ) := by linarith
  have hq0 : 0 ≤  ‖z - 1 / 2‖ / 272 := by positivity
  apply hr.trans
  calc
    ((65*10^163)) * (‖z - 1 / 2‖ / 272) ^ 640 / (1 - ‖z - 1 / 2‖ / 272) ≤ 
        ((65*10^163)) * (255 / 544 : ℝ) ^ 640 / (1 - 255 / 544) := by
      gcongr
    _ ≤  31 / 10 ^ 47 := by norm_num

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
  ∑ j ∈ range 320, (b j:ℂ)*(scaledVariable z)^(2*j)
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
    (∑ n ∈ range 640, TaoZetaGlobal.taylorTerm z n)=polynomial moment z := by
  rw [show 640=2*320 by norm_num,sum_even_odd]
  simp_rw [even_term,odd_term,add_zero]
  rfl

lemma polynomial_entire (b : ℕ → ℝ) : Differentiable ℂ (polynomial b) := by
  unfold polynomial scaledVariable
  fun_prop

lemma xiPolynomial_entire (b : ℕ → ℝ) : Differentiable ℂ (xiPolynomial b) := by
  have h := polynomial_entire b
  unfold xiPolynomial
  fun_prop

lemma scaledVariable_norm (z : ℂ) (hz : ‖z-1/2‖≤ (255/2)) : ‖scaledVariable z‖≤ 255/256 := by
  rw [scaledVariable,norm_div]
  norm_num
  linarith

lemma polynomial_error (b : ℕ → ℝ) (ε : ℝ) (hε : 0≤ ε)
    (hb : ∀ j<320, |moment j-b j|≤ ε) (z : ℂ) (hz : ‖z-1/2‖≤ (255/2)) :
    ‖polynomial moment z-polynomial b z‖≤ 129*ε := by
  have hv := scaledVariable_norm z hz
  have hgeo := hasSum_geometric_of_lt_one (by norm_num : (0:ℝ)≤ 65025/65536) (by norm_num : (65025/65536:ℝ)<1)
  have hs := sum_le_hasSum (range 320) (fun n _ => pow_nonneg (by norm_num : (0:ℝ)≤ 65025/65536) n) hgeo
  have he : polynomial moment z-polynomial b z =
      ∑ j ∈ range 320, ((moment j-b j:ℝ):ℂ)*(scaledVariable z)^(2*j) := by
    unfold polynomial
    simp_rw [ofReal_sub,sub_mul,sum_sub_distrib]
  rw [he]
  calc
    _ ≤  ∑ j ∈ range 320, ‖((moment j-b j:ℝ):ℂ)*(scaledVariable z)^(2*j)‖ := norm_sum_le _ _
    _ ≤  ε*∑ j ∈ range 320, (65025/65536:ℝ)^j := by
      rw [mul_sum]
      apply sum_le_sum
      intro j hj
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,norm_pow]
      have hp : ‖scaledVariable z‖^(2*j)≤ (65025/65536:ℝ)^j := by
        calc
          _ ≤  (255/256:ℝ)^(2*j) := pow_le_pow_left₀ (norm_nonneg _) hv _
          _ = _ := by rw [pow_mul]; norm_num
      exact mul_le_mul (hb j (mem_range.mp hj)) hp (by positivity) hε
    _ ≤  ε*(1-(65025/65536:ℝ))⁻¹ := mul_le_mul_of_nonneg_left hs hε
    _ ≤  129*ε := by norm_num; linarith

lemma completedZeta_error (b : ℕ → ℝ) (ε : ℝ) (hε : 0≤ ε)
    (hb : ∀ j<320, |moment j-b j|≤ ε) (z : ℂ) (hz : ‖z-1/2‖≤ (255/2)) :
    ‖completedRiemannZeta₀ z-polynomial b z‖≤ 31/10^47+129*ε := by
  have ht := TaoZetaGlobal.norm_taylor_remainder_640 z hz
  rw [taylor_sum_eq] at ht
  have hp := polynomial_error b ε hε hb z hz
  have he : completedRiemannZeta₀ z-polynomial b z =
      (completedRiemannZeta₀ z-polynomial moment z)+(polynomial moment z-polynomial b z) := by ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add ht hp)

lemma xi_error (b : ℕ → ℝ)
    (hb : ∀ j<320, |moment j-b j|≤ 17/10^50) (z : ℂ) (hz : ‖z-1/2‖≤ (255/2)) :
    ‖CertifiedLocalXi.xi z-xiPolynomial b z‖≤ (28/10^43:ℝ) := by
  have h0 : ‖z‖≤ 128 := by
    have h := norm_add_le (z-(1/2:ℂ)) (1/2:ℂ)
    rw [sub_add_cancel] at h
    norm_num at h
    linarith
  have h1 : ‖z-1‖≤ 128 := by
    have h := norm_sub_le (z-(1/2:ℂ)) (1/2:ℂ)
    rw [show z-(1/2:ℂ)-1/2=z-1 by ring] at h
    norm_num at h
    linarith
  have hp : ‖z*(z-1)/2‖≤ 8200 := by
    rw [norm_div,norm_mul]
    norm_num
    nlinarith [norm_nonneg z,norm_nonneg (z-1),mul_nonneg (sub_nonneg.mpr h0) (sub_nonneg.mpr h1)]
  have he : CertifiedLocalXi.xi z-xiPolynomial b z=
      (z*(z-1)/2)*(completedRiemannZeta₀ z-polynomial b z) := by
    unfold CertifiedLocalXi.xi xiPolynomial
    ring
  rw [he,norm_mul]
  have hc := completedZeta_error b (17/10^50) (by positivity) hb z hz
  calc
    _ ≤  8200*((31/10^47)+129*(17/10^50:ℝ)) := mul_le_mul hp hc (norm_nonneg _) (by norm_num)
    _ ≤  _ := by norm_num

lemma local_coefficient_error (b : ℕ → ℝ)
    (hb : ∀ j<320, |moment j-b j|≤ 17/10^50) (T : ℝ) (hT : |T|≤ (249/2)) (n : ℕ) :
    ‖CertifiedTaylorQuadrature.coefficient CertifiedLocalXi.xi (CertifiedLocalXi.center T) n-
      CertifiedTaylorQuadrature.coefficient (xiPolynomial b) (CertifiedLocalXi.center T) n‖≤ ((28/10^43:ℝ))/(3:ℝ)^n := by
  have hs : ∀ z ∈ Metric.sphere (CertifiedLocalXi.center T) (3:ℝ),
      ‖CertifiedLocalXi.xi z-xiPolynomial b z‖≤ (28/10^43:ℝ) := by
    intro z hz
    apply xi_error b hb
    have h := norm_add_le (z-CertifiedLocalXi.center T) (CertifiedLocalXi.center T-(1/2:ℂ))
    rw [sub_add_sub_cancel,mem_sphere_iff_norm.mp hz] at h
    have hc : ‖CertifiedLocalXi.center T-(1/2:ℂ)‖=|T| := by
      simp [CertifiedLocalXi.center,Real.norm_eq_abs]
    rw [hc] at h
    linarith
  have h := CertifiedComplexTaylor.coefficient_error CertifiedLocalXi.xi (xiPolynomial b)
    CertifiedLocalXi.xi_entire (xiPolynomial_entire b) (CertifiedLocalXi.center T) (3) ((28/10^43:ℝ))
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
  ∑ n ∈ range 60, (b n : ℂ)*rotatedVariable T z^n

lemma rotatedVariable_norm (T : ℝ) (z : ℂ) :
    ‖rotatedVariable T z‖=‖z-center T‖ := by
  simp [rotatedVariable]

lemma scaled_taylor_rotated (S T : ℝ) (z : ℂ) :
    (S:ℂ)*CertifiedComplexTaylor.polynomial xi (center T) 60 z=
      ∑ n ∈ range 60,
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
    (hb : ∀ n<60,
      ‖(S:ℂ)*CertifiedTaylorQuadrature.coefficient xi (center T) n*I^n-(b n:ℂ)‖
        ≤ (28/1000:ℝ)/(3:ℝ)^n+RH124p5RoundingBound60 n)
    (z : ℂ) (hz : ‖z-center T‖≤ (14/5:ℝ)) :
    ‖(S:ℂ)*CertifiedComplexTaylor.polynomial xi (center T) 60 z-
      rotatedPolynomial b T z‖≤
      ∑ n ∈ range 60, (((28/1000:ℝ)/(3:ℝ)^n+RH124p5RoundingBound60 n)*(14/5:ℝ)^n) := by
  rw [scaled_taylor_rotated]
  unfold rotatedPolynomial
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ range 60,
      ‖((S:ℂ)*CertifiedTaylorQuadrature.coefficient xi (center T) n*I^n-(b n:ℂ))*
        rotatedVariable T z^n‖ := by
      simpa only [sub_mul] using
        (norm_sum_le (s:=range 60) (f:=fun n =>
          ((S:ℂ)*CertifiedTaylorQuadrature.coefficient xi (center T) n*I^n)*
            rotatedVariable T z^n-(b n:ℂ)*rotatedVariable T z^n))
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul,norm_pow]
      have hp : ‖rotatedVariable T z‖^n ≤ (14/5:ℝ)^n := by
        apply pow_le_pow_left₀ (norm_nonneg _)
        simpa only [rotatedVariable_norm] using hz
      exact mul_le_mul (hb n (mem_range.mp hn)) hp (by positivity)
        (add_nonneg (by positivity) (RH124p5RoundingBound60_nonneg n))

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
  1/2-∑ j ∈ range 320, (criticalMomentCoefficient b j:ℂ)*(z^(2*j+2)/2+z^(2*j)/8)

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
  (if n=0 then 1/2 else 0)-∑ j ∈ range 320, criticalMomentCoefficient b j*
    ((Nat.choose (2*j+2) n:ℝ)*T^(2*j+2-n)/2+(Nat.choose (2*j) n:ℝ)*T^(2*j-n)/8)

lemma coefficient_criticalXi (b : ℕ → ℝ) (T : ℝ) (n : ℕ) :
    coefficient (criticalXiPolynomial b) T n=(localGlobalCoefficient b T n:ℂ) := by
  have hf : ∀ j : ℕ, Differentiable ℂ (fun z : ℂ =>
      (criticalMomentCoefficient b j:ℂ)*(z^(2*j+2)/2+z^(2*j)/8)) := by intro j; fun_prop
  unfold criticalXiPolynomial coefficient
  rw [iteratedDeriv_fun_sub (by fun_prop) (by fun_prop),sub_div,
    iteratedDeriv_fun_sum (fun j _ => (hf j).contDiff.contDiffAt),sum_div]
  change coefficient (fun _ : ℂ => 1/2) T n-
    (∑ j ∈ range 320,
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

end RH124p5Proof


namespace RH124p5Numerical
open Finset
noncomputable def denominator : ℕ := 8*10^64*2^5120
noncomputable def normalizationNat : ℕ := 10^40
noncomputable def center : ℚ := 249/2
noncomputable def roundedNumerators : List ℤ := [-1169047172479564, -4528863711391416, 1606893257001687, 1683668189166007, -896314021023779, -13416179774571, 94394826460726, -19757144035686, -1070095983435, 962747766022, -113468412540, -8743098942, 3476362857, -245903899, -26301355, 5809248, -236989, -37720, 5182, -99, -30, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
noncomputable def rounded (n : ℕ) : ℤ := roundedNumerators.getD n 0
noncomputable def chooseFast (k n : ℕ) : ℕ :=
  if n≤k then k.factorial/(n.factorial*(k-n).factorial) else 0
noncomputable def numerator (n : ℕ) : ℤ :=
  (if n=0 then (4*10^64*2^5120:ℤ) else 0)*(normalizationNat:ℤ)-
  (normalizationNat:ℤ)*∑ j ∈ range 320,
    RH320TranslationArithmetic.momentInteger j*(-1:ℤ)^j*
    ((2^(5120-16*j+n):ℕ):ℤ)*
    ((chooseFast (2*j+2) n:ℤ)*(249:ℤ)^(2*j+2-n)+
      (chooseFast (2*j) n:ℤ)*(249:ℤ)^(2*j-n))
theorem precision_checked : ∀ n : Fin 40,
    (if n.val < 22 then (1:ℤ) else if n.val < 25 then 10
      else if n.val < 30 then 10^4 else 10^10) *
      |(10^14:ℤ)*numerator n.val-rounded n.val*(denominator:ℤ)| ≤ (denominator:ℤ) := by
  exact TaoFivePrimes.rh124p5_translation_precision14
theorem tail_checked : ∀ n : Fin 20,
    (10^32:ℤ)*|numerator (n.val+40)| ≤ (denominator:ℤ) := by
  exact TaoFivePrimes.rh124p5_translation_tail60
end RH124p5Numerical

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option linter.unusedSimpArgs false
namespace RH124p5Numerical
open Finset
lemma chooseFast_eq (k n : ℕ) : chooseFast k n=Nat.choose k n := by
  by_cases h : n≤k
  · simp only [chooseFast,if_pos h,Nat.choose_eq_factorial_div_factorial h]
  · simp only [chooseFast,if_neg h,Nat.choose_eq_zero_of_lt (lt_of_not_ge h)]
lemma monomial_scaled (k n : ℕ) :
    (Nat.choose k n:ℝ)*(249/2:ℝ)^(k-n)=
      (Nat.choose k n:ℝ)*(249:ℝ)^(k-n)*2^n/2^k := by
  by_cases h : n≤k
  · rw [div_pow,pow_sub₀ (2:ℝ) (by norm_num : (2:ℝ)≠0) h]
    field_simp
  · have hc := Nat.choose_eq_zero_of_lt (lt_of_not_ge h)
    simp [hc]
lemma dyadic_scale (j n : ℕ) (hj : j<320) :
    ((2^(5120-16*j+n):ℕ):ℝ)/(2^5120:ℝ)=2^n/(256:ℝ)^(2*j) := by
  push_cast
  have hv : (256:ℝ)^(2*j)=(2:ℝ)^(16*j) := by
    rw [show (256:ℝ)=2^8 by norm_num,←pow_mul]
    congr 1
    omega
  rw [hv,pow_add,pow_sub₀ (2:ℝ) (by norm_num : (2:ℝ)≠0) (by omega : 16*j≤5120)]
  field_simp
lemma monomial_combo (j n : ℕ) :
    ((Nat.choose (2*j+2) n:ℝ)*(249/2:ℝ)^(2*j+2-n)/2+
      (Nat.choose (2*j) n:ℝ)*(249/2:ℝ)^(2*j-n)/8)/(128:ℝ)^(2*j)=
    ((chooseFast (2*j+2) n:ℝ)*(249:ℝ)^(2*j+2-n)+
      (chooseFast (2*j) n:ℝ)*(249:ℝ)^(2*j-n))*2^n/(8*(256:ℝ)^(2*j)) := by
  simp only [chooseFast_eq]
  rw [monomial_scaled,monomial_scaled,pow_add]
  norm_num
  have hv : (256:ℝ)^(2*j)=(2:ℝ)^(2*j)*(128:ℝ)^(2*j) := by
    rw [←mul_pow]
    norm_num
  rw [hv]
  field_simp
  <;> ring

lemma momentInteger_real (j : ℕ) :
    (RH320TranslationArithmetic.momentInteger j:ℝ)/(10:ℝ)^64=TaoFivePrimes_RHMoments320 j := by
  unfold RH320TranslationArithmetic.momentInteger TaoFivePrimes_RHMoments320
  by_cases h : j<304
  · simp only [h,if_pos]
    unfold RH304TranslationArithmetic.momentInteger TaoFivePrimes_RHMoments304
    by_cases hk : j<272
    · simp only [hk,if_pos]
      unfold RH272TranslationArithmetic.momentInteger TaoFivePrimes_RHMoments272
      split_ifs <;> simp [CertifiedGlobalMomentEnclosure.candidateMoment]
    · simp [hk]
  · simp [h]

lemma term_identity (j n : ℕ) (hj : j<320) :
    ((RH320TranslationArithmetic.momentInteger j:ℝ)*(-1:ℝ)^j*
      ((2^(5120-16*j+n):ℕ):ℝ)*
      ((chooseFast (2*j+2) n:ℝ)*(249:ℝ)^(2*j+2-n)+
        (chooseFast (2*j) n:ℝ)*(249:ℝ)^(2*j-n)))/(denominator:ℝ)=
    RH124p5Proof.CertifiedPolynomialTranslation.criticalMomentCoefficient
      TaoFivePrimes_RHMoments320 j*
      ((Nat.choose (2*j+2) n:ℝ)*(249/2:ℝ)^(2*j+2-n)/2+
        (Nat.choose (2*j) n:ℝ)*(249/2:ℝ)^(2*j-n)/8) := by
  have hd : (denominator:ℝ)=8*(10:ℝ)^64*(2:ℝ)^5120 := by norm_num [denominator]
  rw [hd]
  unfold RH124p5Proof.CertifiedPolynomialTranslation.criticalMomentCoefficient
  rw [←momentInteger_real]
  have hm := monomial_combo j n
  have hs := dyadic_scale j n hj
  calc
    _ = (RH320TranslationArithmetic.momentInteger j:ℝ)*(-1:ℝ)^j*
        ((chooseFast (2*j+2) n:ℝ)*(249:ℝ)^(2*j+2-n)+
          (chooseFast (2*j) n:ℝ)*(249:ℝ)^(2*j-n))/(8*(10:ℝ)^64)*
          (((2^(5120-16*j+n):ℕ):ℝ)/(2^5120:ℝ)) := by ring
    _ = (RH320TranslationArithmetic.momentInteger j:ℝ)/(10:ℝ)^64*(-1:ℝ)^j*
        (((chooseFast (2*j+2) n:ℝ)*(249:ℝ)^(2*j+2-n)+
          (chooseFast (2*j) n:ℝ)*(249:ℝ)^(2*j-n))*2^n/(8*(256:ℝ)^(2*j))) := by rw [hs]; ring
    _ = _ := by rw [←hm]; ring
lemma denominator_pos : 0<(denominator:ℝ) := by
  exact_mod_cast (show 0<denominator by unfold denominator; positivity)
lemma numerator_real (n : ℕ) :
    (numerator n:ℝ)/(denominator:ℝ)=
      (normalizationNat:ℝ)*RH124p5Proof.CertifiedPolynomialTranslation.localGlobalCoefficient
        TaoFivePrimes_RHMoments320 (249/2) n := by
  have hd : (denominator:ℝ)=8*(10:ℝ)^64*(2:ℝ)^5120 := by norm_num [denominator]
  have hh : (4*(10:ℝ)^64*(2:ℝ)^5120)/(denominator:ℝ)=1/2 := by
    rw [hd]
    field_simp
    <;> ring
  let f (j : ℕ) : ℝ :=
    (RH320TranslationArithmetic.momentInteger j:ℝ)*(-1:ℝ)^j*
      (2:ℝ)^(5120-16*j+n)*
      ((chooseFast (2*j+2) n:ℝ)*(249:ℝ)^(2*j+2-n)+
        (chooseFast (2*j) n:ℝ)*(249:ℝ)^(2*j-n))
  have hs : (∑ j ∈ range 320, f j)/(denominator:ℝ)=
      ∑ j ∈ range 320,
        RH124p5Proof.CertifiedPolynomialTranslation.criticalMomentCoefficient
          TaoFivePrimes_RHMoments320 j*
          ((Nat.choose (2*j+2) n:ℝ)*(249/2:ℝ)^(2*j+2-n)/2+
            (Nat.choose (2*j) n:ℝ)*(249/2:ℝ)^(2*j-n)/8) := by
    rw [sum_div]
    apply sum_congr rfl
    intro j hj
    simpa only [f,Nat.cast_pow,Nat.cast_ofNat] using term_identity j n (mem_range.mp hj)
  have he : (numerator n:ℝ)/(denominator:ℝ)=
      (normalizationNat:ℝ)*
        (((if n=0 then 4*(10:ℝ)^64*(2:ℝ)^5120 else 0)/(denominator:ℝ))-
          (∑ j ∈ range 320, f j)/(denominator:ℝ)) := by
    unfold numerator
    push_cast
    dsimp only [f]
    split_ifs <;> ring
  rw [he,hs]
  unfold RH124p5Proof.CertifiedPolynomialTranslation.localGlobalCoefficient
  split_ifs <;> simp only [zero_div,hh]

attribute [local irreducible] numerator rounded denominator
noncomputable def proposed (n : ℕ) : ℝ := (rounded n:ℝ)/(10^14:ℝ)
lemma rounding_precision (n : ℕ) (hn : n < 40) :
    |(numerator n:ℝ)/(denominator:ℝ)-proposed n| ≤ RH124p5RoundingBound n := by
  have h0 := precision_checked (⟨n,hn⟩:Fin 40)
  change (if n < 22 then (1:ℤ) else if n < 25 then 10
      else if n < 30 then 10^4 else 10^10) *
      |(10^14:ℤ)*numerator n-rounded n*(denominator:ℤ)| ≤ (denominator:ℤ) at h0
  have h : (if n < 22 then (1:ℝ) else if n < 25 then 10
      else if n < 30 then 10^4 else 10^10) *
      |(10^14:ℝ)*(numerator n:ℝ)-(rounded n:ℝ)*(denominator:ℝ)| ≤ (denominator:ℝ) := by
    exact_mod_cast h0
  have hd := denominator_pos
  have he : (numerator n:ℝ)/(denominator:ℝ)-proposed n =
      ((10^14:ℝ)*(numerator n:ℝ)-(rounded n:ℝ)*(denominator:ℝ))/
        ((10^14:ℝ)*(denominator:ℝ)) := by
    unfold proposed
    field_simp <;> ring
  rw [he,abs_div,abs_of_pos (mul_pos (by positivity) hd)]
  apply (div_le_iff₀ (mul_pos (by positivity) hd)).2
  unfold RH124p5RoundingBound
  split_ifs at h ⊢ <;> norm_num at h ⊢ <;> linarith only [h]

lemma rounding_precision60 (n : ℕ) (hn : n < 60) :
    |(numerator n:ℝ)/(denominator:ℝ)-proposed n| ≤ RH124p5RoundingBound60 n := by
  by_cases h40 : n < 40
  · simpa [RH124p5RoundingBound60,h40] using rounding_precision n h40
  · have hge : 40 ≤ n := by omega
    have hindex : n-40 < 20 := by omega
    have ht := tail_checked (⟨n-40,hindex⟩:Fin 20)
    have he : n-40+40=n := Nat.sub_add_cancel hge
    rw [he] at ht
    have h : (10^32:ℝ)*|(numerator n:ℝ)| ≤ (denominator:ℝ) := by
      exact_mod_cast ht
    have hz : rounded n = 0 := by
      unfold rounded
      apply List.getD_eq_default
      have hlen : roundedNumerators.length = 40 := by norm_num [roundedNumerators]
      omega
    simp only [proposed,hz,Int.cast_zero,zero_div,sub_zero,RH124p5RoundingBound60,if_neg h40]
    rw [abs_div,abs_of_pos denominator_pos]
    apply (div_le_iff₀ denominator_pos).2
    norm_num at h ⊢
    linarith only [h]

lemma translated_error_precision (n : ℕ) (hn : n<60) :
    |(normalizationNat:ℝ)*RH124p5Proof.CertifiedPolynomialTranslation.localGlobalCoefficient
      TaoFivePrimes_RHMoments320 (249/2) n-proposed n|≤ RH124p5RoundingBound60 n := by
  rw [←numerator_real]
  exact rounding_precision60 n hn

end RH124p5Numerical


set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option linter.unusedSimpArgs false
namespace RH124p5Proof.CertifiedLocalXi
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
lemma local_tail_norm_60 (T : ℝ) (hT : |T|≤1000) (z : ℂ)
    (hz : ‖z-center T‖≤ (14/5:ℝ)) :
    ‖RH124p5Proof.CertifiedComplexTaylor.remainder xi (center T) 60 z‖≤1/10^45 := by
  have h := RH124p5Proof.CertifiedComplexTaylor.remainder_bound xi xi_entire (center T)
    24 400000000 (14/5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (xi_circle_bound_1000 T hT) 60 z hz
  apply h.trans
  norm_num

end RH124p5Proof.CertifiedLocalXi
namespace RH124p5Numerical
open Complex
lemma coefficients_rounded (n : ℕ) (hn : n<60) :
    ‖(normalizationNat:ℂ)*RH124p5Proof.CertifiedTaylorQuadrature.coefficient
      RH124p5Proof.CertifiedLocalXi.xi (RH124p5Proof.CertifiedLocalXi.center (249/2)) n*
      Complex.I^n-(proposed n:ℂ)‖≤ (28/1000:ℝ)/(3:ℝ)^n+RH124p5RoundingBound60 n := by
  have hg := RH124p5Proof.CertifiedGlobalMoments.local_coefficient_error
    TaoFivePrimes_RHMoments320
    TaoFivePrimes.rh_moments_320_enclosed_tight (249/2) (by norm_num) n
  have hr := RH124p5Proof.CertifiedPolynomialTranslation.global_rotated_error
    TaoFivePrimes_RHMoments320 (normalizationNat:ℝ)
    (249/2) (proposed n) (RH124p5RoundingBound60 n) n (translated_error_precision n hn)
  have he :
      (normalizationNat:ℂ)*RH124p5Proof.CertifiedTaylorQuadrature.coefficient
        RH124p5Proof.CertifiedLocalXi.xi (RH124p5Proof.CertifiedLocalXi.center (249/2)) n*
        Complex.I^n-(proposed n:ℂ)=
      (normalizationNat:ℂ)*(RH124p5Proof.CertifiedTaylorQuadrature.coefficient
        RH124p5Proof.CertifiedLocalXi.xi (RH124p5Proof.CertifiedLocalXi.center (249/2)) n-
        RH124p5Proof.CertifiedTaylorQuadrature.coefficient
          (RH124p5Proof.CertifiedGlobalMoments.xiPolynomial
            TaoFivePrimes_RHMoments320)
          (RH124p5Proof.CertifiedLocalXi.center (249/2)) n)*Complex.I^n+
      ((normalizationNat:ℂ)*RH124p5Proof.CertifiedTaylorQuadrature.coefficient
        (RH124p5Proof.CertifiedGlobalMoments.xiPolynomial
          TaoFivePrimes_RHMoments320)
        (RH124p5Proof.CertifiedLocalXi.center (249/2)) n*Complex.I^n-(proposed n:ℂ)) := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  have hnS : 0≤(normalizationNat:ℝ) := Nat.cast_nonneg _
  have hS : (normalizationNat:ℝ)=(10:ℝ)^40 := by norm_num [normalizationNat]
  have hfirst : ‖(normalizationNat:ℂ)*(RH124p5Proof.CertifiedTaylorQuadrature.coefficient
        RH124p5Proof.CertifiedLocalXi.xi (RH124p5Proof.CertifiedLocalXi.center (249/2)) n-
        RH124p5Proof.CertifiedTaylorQuadrature.coefficient
          (RH124p5Proof.CertifiedGlobalMoments.xiPolynomial
            TaoFivePrimes_RHMoments320)
          (RH124p5Proof.CertifiedLocalXi.center (249/2)) n)*Complex.I^n‖≤ (28/1000:ℝ)/(3:ℝ)^n := by
    simp only [norm_mul,norm_pow,norm_I,one_pow,mul_one]
    rw [show ‖(normalizationNat:ℂ)‖=(normalizationNat:ℝ) by
      norm_cast]
    calc
      _ ≤ (normalizationNat:ℝ)*((28/10^43:ℝ)/(3:ℝ)^n) := mul_le_mul_of_nonneg_left hg hnS
      _ = (28/1000:ℝ)/(3:ℝ)^n := by rw [hS]; norm_num; ring
  have hsecond : ‖(normalizationNat:ℂ)*RH124p5Proof.CertifiedTaylorQuadrature.coefficient
      (RH124p5Proof.CertifiedGlobalMoments.xiPolynomial TaoFivePrimes_RHMoments320)
      (RH124p5Proof.CertifiedLocalXi.center (249/2)) n*Complex.I^n-(proposed n:ℂ)‖≤RH124p5RoundingBound60 n := by
    simpa only [Complex.ofReal_natCast] using hr
  linarith
lemma xi_approximation (z : ℂ)
    (hz : ‖z-RH124p5Proof.CertifiedLocalXi.center (249/2)‖≤ (14/5:ℝ)) :
    ‖(normalizationNat:ℂ)*RH124p5Proof.CertifiedLocalXi.xi z-
      RH124p5Proof.CertifiedLocalXi.rotatedPolynomial proposed (249/2) z‖≤21/50 := by
  have he :
      (normalizationNat:ℂ)*RH124p5Proof.CertifiedLocalXi.xi z-
        RH124p5Proof.CertifiedLocalXi.rotatedPolynomial proposed (249/2) z=
      (normalizationNat:ℂ)*RH124p5Proof.CertifiedComplexTaylor.remainder
        RH124p5Proof.CertifiedLocalXi.xi (RH124p5Proof.CertifiedLocalXi.center (249/2)) 60 z+
      ((normalizationNat:ℂ)*RH124p5Proof.CertifiedComplexTaylor.polynomial
        RH124p5Proof.CertifiedLocalXi.xi (RH124p5Proof.CertifiedLocalXi.center (249/2)) 60 z-
        RH124p5Proof.CertifiedLocalXi.rotatedPolynomial proposed (249/2) z) := by
    unfold RH124p5Proof.CertifiedComplexTaylor.remainder
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  have ht := RH124p5Proof.CertifiedLocalXi.local_tail_norm_60 (249/2) (by norm_num) z hz
  have hp := RH124p5Proof.CertifiedLocalXi.rounded_polynomial_error
    (normalizationNat:ℝ) (249/2) proposed coefficients_rounded z hz
  have hfirst : ‖(normalizationNat:ℂ)*RH124p5Proof.CertifiedComplexTaylor.remainder
      RH124p5Proof.CertifiedLocalXi.xi (RH124p5Proof.CertifiedLocalXi.center (249/2)) 60 z‖≤1/10^5 := by
    rw [norm_mul]
    rw [show ‖(normalizationNat:ℂ)‖=(10:ℝ)^40 by norm_num [normalizationNat]]
    calc
      _ ≤ (10:ℝ)^40*(1/10^45) := mul_le_mul_of_nonneg_left ht (by positivity)
      _ ≤ 1/10^5 := by norm_num
  have hsecond : ‖(normalizationNat:ℂ)*RH124p5Proof.CertifiedComplexTaylor.polynomial
      RH124p5Proof.CertifiedLocalXi.xi (RH124p5Proof.CertifiedLocalXi.center (249/2)) 60 z-
      RH124p5Proof.CertifiedLocalXi.rotatedPolynomial proposed (249/2) z‖≤419/1000 := by
    apply hp.trans
    norm_num [Finset.sum_range_succ,RH124p5RoundingBound60,RH124p5RoundingBound]
  linarith
end RH124p5Numerical

-- Candidate wider-domain estimates.  This file is appended to the analytic
-- framework; it is not a standalone theorem or a completed proof.
namespace RH124p5Wide
open Complex Finset Metric
open RH124p5Proof
open RH124p5Proof.CertifiedGlobalMoments
open _root_.CertifiedGlobalMoments

lemma global_tail_128 (z : ℂ) (hz : ‖z - 1/2‖ ≤ (128:ℝ)) :
    ‖completedRiemannZeta₀ z - ∑ n ∈ range 640, TaoZetaGlobal.taylorTerm z n‖ ≤ 4/10^45 := by
  have hr := TaoZetaGlobal.norm_taylor_remainder_le z (by linarith) 640
  have hq : ‖z-1/2‖/272 ≤ (8/17:ℝ) := by linarith
  have hq0 : 0 ≤ ‖z-1/2‖/272 := by positivity
  apply hr.trans
  calc
    (65*10^163) * (‖z-1/2‖/272)^640 / (1-‖z-1/2‖/272) ≤
        (65*10^163) * (8/17:ℝ)^640 / (1-8/17) := by gcongr
    _ ≤ 4/10^45 := by norm_num

lemma polynomial_error_128 (b : ℕ → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hb : ∀ j<320, |moment j-b j| ≤ ε) (z : ℂ) (hz : ‖z-1/2‖ ≤ (128:ℝ)) :
    ‖polynomial moment z-polynomial b z‖ ≤ 320*ε := by
  have hv : ‖scaledVariable z‖ ≤ 1 := by
    rw [scaledVariable,norm_div]
    norm_num
    linarith
  have he : polynomial moment z-polynomial b z =
      ∑ j ∈ range 320, ((moment j-b j:ℝ):ℂ)*(scaledVariable z)^(2*j) := by
    unfold polynomial
    simp_rw [ofReal_sub,sub_mul,sum_sub_distrib]
  rw [he]
  calc
    _ ≤ ∑ j ∈ range 320, ‖((moment j-b j:ℝ):ℂ)*(scaledVariable z)^(2*j)‖ := norm_sum_le _ _
    _ ≤ ε*∑ _j ∈ range 320, (1:ℝ) := by
      rw [mul_sum]
      apply sum_le_sum
      intro j hj
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,norm_pow]
      have hp : ‖scaledVariable z‖^(2*j) ≤ 1 := by
        simpa using pow_le_pow_left₀ (norm_nonneg _) hv (2*j)
      exact mul_le_mul (hb j (mem_range.mp hj)) hp (by positivity) hε
    _ = 320*ε := by simp; ring

lemma xi_error_128 (b : ℕ → ℝ)
    (hb : ∀ j<320, |moment j-b j| ≤ 17/10^50) (z : ℂ) (hz : ‖z-1/2‖ ≤ (128:ℝ)) :
    ‖CertifiedLocalXi.xi z-xiPolynomial b z‖ ≤ (35/10^42:ℝ) := by
  have h0 : ‖z‖ ≤ 129 := by
    have h := norm_add_le (z-(1/2:ℂ)) (1/2:ℂ)
    rw [sub_add_cancel] at h
    norm_num at h
    linarith
  have h1 : ‖z-1‖ ≤ 129 := by
    have h := norm_sub_le (z-(1/2:ℂ)) (1/2:ℂ)
    rw [show z-(1/2:ℂ)-1/2=z-1 by ring] at h
    norm_num at h
    linarith
  have hp : ‖z*(z-1)/2‖ ≤ 8400 := by
    rw [norm_div,norm_mul]
    norm_num
    nlinarith [norm_nonneg z,norm_nonneg (z-1),mul_nonneg (sub_nonneg.mpr h0) (sub_nonneg.mpr h1)]
  have ht := global_tail_128 z hz
  rw [taylor_sum_eq] at ht
  have hq := polynomial_error_128 b (17/10^50) (by positivity) hb z hz
  have he : completedRiemannZeta₀ z-polynomial b z =
      (completedRiemannZeta₀ z-polynomial moment z)+(polynomial moment z-polynomial b z) := by ring
  have hc : ‖completedRiemannZeta₀ z-polynomial b z‖ ≤ 4/10^45+320*(17/10^50:ℝ) := by
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add ht hq)
  have hxi : CertifiedLocalXi.xi z-xiPolynomial b z =
      (z*(z-1)/2)*(completedRiemannZeta₀ z-polynomial b z) := by
    unfold CertifiedLocalXi.xi xiPolynomial
    ring
  rw [hxi,norm_mul]
  calc
    _ ≤ 8400*(4/10^45+320*(17/10^50:ℝ)) := mul_le_mul hp hc (norm_nonneg _) (by norm_num)
    _ ≤ _ := by norm_num

end RH124p5Wide

namespace RH124p5Wide
open Complex Finset Metric
open RH124p5Proof
open RH124p5Proof.CertifiedGlobalMoments
open RH124p5Proof.CertifiedComplexTaylor
open _root_.CertifiedGlobalMoments

noncomputable def Q : ℂ → ℂ := xiPolynomial TaoFivePrimes_RHMoments320
noncomputable def c : ℂ := CertifiedLocalXi.center (249/2)
noncomputable def P : ℂ → ℂ := CertifiedLocalXi.rotatedPolynomial RH124p5Numerical.proposed (249/2)
noncomputable def G (z : ℂ) : ℂ := (10^40:ℂ)*(CertifiedLocalXi.xi z-Q z)
noncomputable def H (z : ℂ) : ℂ := (10^40:ℂ)*Q z-P z

lemma Q_entire : Differentiable ℂ Q := xiPolynomial_entire _
lemma P_entire : Differentiable ℂ P := by
  unfold P CertifiedLocalXi.rotatedPolynomial CertifiedLocalXi.rotatedVariable
  fun_prop
lemma G_entire : Differentiable ℂ G := by
  unfold G
  exact (CertifiedLocalXi.xi_entire.sub Q_entire).const_mul _
lemma H_entire : Differentiable ℂ H := by
  unfold H
  exact (Q_entire.const_mul _).sub P_entire

lemma global_difference (z : ℂ) (hz : ‖z-1/2‖ ≤ (128:ℝ)) :
    ‖CertifiedLocalXi.xi z-Q z‖ ≤ (35/10^42:ℝ) := by
  exact xi_error_128 TaoFivePrimes_RHMoments320 TaoFivePrimes.rh_moments_320_enclosed_tight z hz

lemma circle_global (w : ℂ) (hw : ‖w-c‖ ≤ (7/2:ℝ)) : ‖w-1/2‖ ≤ (128:ℝ) := by
  have h := norm_add_le (w-c) (c-(1/2:ℂ))
  rw [sub_add_sub_cancel] at h
  have hc : ‖c-(1/2:ℂ)‖ = (249/2:ℝ) := by
    simp [c,CertifiedLocalXi.center]
  rw [hc] at h
  linarith

lemma G_bound (w : ℂ) (hw : ‖w-c‖ ≤ (7/2:ℝ)) : ‖G w‖ ≤ (7/20:ℝ) := by
  have h := global_difference w (circle_global w hw)
  unfold G
  rw [norm_mul]
  have hS : ‖(10^40:ℂ)‖ = (10:ℝ)^40 := by norm_num
  rw [hS]
  calc
    _ ≤ (10:ℝ)^40*(35/10^42) := mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ 7/20 := by norm_num

lemma scaled_taylor_rotated_Q (z : ℂ) :
    (10^40:ℂ)*polynomial Q c 60 z = ∑ n ∈ range 60,
      ((10^40:ℂ)*CertifiedTaylorQuadrature.coefficient Q c n*I^n)*
        CertifiedLocalXi.rotatedVariable (249/2) z^n := by
  unfold CertifiedComplexTaylor.polynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have he : I*CertifiedLocalXi.rotatedVariable (249/2) z = z-c := by
    simp [CertifiedLocalXi.rotatedVariable,c,← mul_assoc]
  rw [mul_assoc,← mul_pow,he]
  ring

lemma Q_taylor_coefficient (n : ℕ) (hn : n<60) :
    ‖(10^40:ℂ)*CertifiedTaylorQuadrature.coefficient Q c n*I^n-
      (RH124p5Numerical.proposed n:ℂ)‖ ≤ RH124p5RoundingBound60 n := by
  have h := CertifiedPolynomialTranslation.global_rotated_error
    TaoFivePrimes_RHMoments320 (RH124p5Numerical.normalizationNat:ℝ)
    (249/2) (RH124p5Numerical.proposed n) (RH124p5RoundingBound60 n) n
    (RH124p5Numerical.translated_error_precision n hn)
  norm_num [Q,c,RH124p5Numerical.normalizationNat] at h ⊢
  exact h

lemma Q_polynomial_rounding (z : ℂ) (hz : ‖z-c‖ ≤ (16/5:ℝ)) :
    ‖(10^40:ℂ)*polynomial Q c 60 z-P z‖ ≤ (13/1000:ℝ) := by
  have hs : ‖(10^40:ℂ)*polynomial Q c 60 z-P z‖ ≤
      ∑ n ∈ range 60, RH124p5RoundingBound60 n*(16/5:ℝ)^n := by
    rw [scaled_taylor_rotated_Q]
    unfold P CertifiedLocalXi.rotatedPolynomial
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ n ∈ range 60,
        ‖((10^40:ℂ)*CertifiedTaylorQuadrature.coefficient Q c n*I^n-
           (RH124p5Numerical.proposed n:ℂ))*CertifiedLocalXi.rotatedVariable (249/2) z^n‖ := by
        simpa only [sub_mul] using
          (norm_sum_le (s:=range 60) (f:=fun n =>
            ((10^40:ℂ)*CertifiedTaylorQuadrature.coefficient Q c n*I^n)*
              CertifiedLocalXi.rotatedVariable (249/2) z^n-
                (RH124p5Numerical.proposed n:ℂ)*CertifiedLocalXi.rotatedVariable (249/2) z^n))
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_mul,norm_pow]
        have hp : ‖CertifiedLocalXi.rotatedVariable (249/2) z‖^n ≤ (16/5:ℝ)^n := by
          apply pow_le_pow_left₀ (norm_nonneg _)
          simpa only [CertifiedLocalXi.rotatedVariable_norm,c] using hz
        exact mul_le_mul (Q_taylor_coefficient n (mem_range.mp hn)) hp (by positivity)
          (RH124p5RoundingBound60_nonneg n)
  apply hs.trans
  norm_num [Finset.sum_range_succ,RH124p5RoundingBound60,RH124p5RoundingBound]

lemma remainder_sub (f g : ℂ → ℂ) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (z : ℂ) : remainder (fun w => f w-g w) c 60 z = remainder f c 60 z-remainder g c 60 z := by
  unfold remainder CertifiedComplexTaylor.polynomial
  simp_rw [coefficient_sub f g hf hg,sub_mul,Finset.sum_sub_distrib]
  ring

lemma xi_tail_scaled (z : ℂ) (hz : ‖z-c‖ ≤ (16/5:ℝ)) :
    ‖(10^40:ℂ)*remainder CertifiedLocalXi.xi c 60 z‖ ≤ (1/5000:ℝ) := by
  have h := remainder_bound CertifiedLocalXi.xi CertifiedLocalXi.xi_entire c
    24 400000000 (16/5) (by norm_num) (by positivity) (by norm_num) (by norm_num)
    (CertifiedLocalXi.xi_circle_bound_1000 (249/2) (by norm_num)) 60 z (by simpa [c] using hz)
  rw [norm_mul]
  have hS : ‖(10^40:ℂ)‖=(10:ℝ)^40 := by norm_num
  rw [hS]
  calc
    _ ≤ (10:ℝ)^40*(400000000*((16/5:ℝ)/24)^60/(1-(16/5:ℝ)/24)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ 1/5000 := by norm_num

lemma difference_tail_scaled (z : ℂ) (hz : ‖z-c‖ ≤ (16/5:ℝ)) :
    ‖(10^40:ℂ)*remainder (fun w => CertifiedLocalXi.xi w-Q w) c 60 z‖ ≤ (19/1000:ℝ) := by
  have hd := CertifiedLocalXi.xi_entire.sub Q_entire
  have hcircle : ∀ w ∈ sphere c (7/2:ℝ),
      ‖CertifiedLocalXi.xi w-Q w‖ ≤ (35/10^42:ℝ) := by
    intro w hw
    apply global_difference w
    apply circle_global w
    exact (mem_sphere_iff_norm.mp hw).le
  have h := remainder_bound (fun w => CertifiedLocalXi.xi w-Q w) hd c
    (7/2) (35/10^42) (16/5) (by norm_num) (by positivity) (by norm_num) (by norm_num)
    hcircle 60 z hz
  rw [norm_mul]
  have hS : ‖(10^40:ℂ)‖=(10:ℝ)^40 := by norm_num
  rw [hS]
  calc
    _ ≤ (10:ℝ)^40*((35/10^42:ℝ)*((16/5:ℝ)/(7/2))^60/(1-(16/5:ℝ)/(7/2))) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ 19/1000 := by norm_num

lemma H_bound (z : ℂ) (hz : ‖z-c‖ ≤ (16/5:ℝ)) : ‖H z‖ ≤ (33/1000:ℝ) := by
  have he : H z = ((10^40:ℂ)*polynomial Q c 60 z-P z)+
      (10^40:ℂ)*remainder CertifiedLocalXi.xi c 60 z-
      (10^40:ℂ)*remainder (fun w => CertifiedLocalXi.xi w-Q w) c 60 z := by
    rw [remainder_sub _ _ CertifiedLocalXi.xi_entire Q_entire]
    unfold H remainder
    ring
  rw [he]
  have hp := Q_polynomial_rounding z hz
  have hx := xi_tail_scaled z hz
  have hd := difference_tail_scaled z hz
  calc
    _ ≤ ‖((10^40:ℂ)*polynomial Q c 60 z-P z)+
        (10^40:ℂ)*remainder CertifiedLocalXi.xi c 60 z‖+
        ‖(10^40:ℂ)*remainder (fun w => CertifiedLocalXi.xi w-Q w) c 60 z‖ := norm_sub_le _ _
    _ ≤ (‖(10^40:ℂ)*polynomial Q c 60 z-P z‖+
        ‖(10^40:ℂ)*remainder CertifiedLocalXi.xi c 60 z‖)+
        ‖(10^40:ℂ)*remainder (fun w => CertifiedLocalXi.xi w-Q w) c 60 z‖ :=
          add_le_add (norm_add_le _ _) (le_refl _)
    _ ≤ (13/1000:ℝ)+1/5000+19/1000 := add_le_add (add_le_add hp hx) hd
    _ ≤ 33/1000 := by norm_num

lemma derivative_on_circle (f : ℂ → ℂ) (hf : Differentiable ℂ f) (z : ℂ)
    (R M : ℝ) (hR : 0 < R) (hb : ∀ w ∈ sphere z R, ‖f w‖ ≤ M) :
    ‖deriv f z‖ ≤ M/R := by
  have h := CertifiedTaylorQuadrature.coefficient_bound f hf z R M hR hb 1
  simpa [CertifiedTaylorQuadrature.coefficient,iteratedDeriv_one] using h

lemma G_derivative (z : ℂ) (hz : ‖z-c‖ ≤ (63/20:ℝ)) : ‖deriv G z‖ ≤ 1 := by
  have hc : ∀ w ∈ sphere z (7/20:ℝ), ‖G w‖ ≤ 7/20 := by
    intro w hw
    apply G_bound
    have h := norm_add_le (w-z) (z-c)
    rw [sub_add_sub_cancel,mem_sphere_iff_norm.mp hw] at h
    linarith
  have h := derivative_on_circle G G_entire z (7/20) (7/20) (by norm_num) hc
  norm_num at h
  exact h

lemma H_derivative (z : ℂ) (hz : ‖z-c‖ ≤ (63/20:ℝ)) : ‖deriv H z‖ ≤ (33/50:ℝ) := by
  have hc : ∀ w ∈ sphere z (1/20:ℝ), ‖H w‖ ≤ 33/1000 := by
    intro w hw
    apply H_bound
    have h := norm_add_le (w-z) (z-c)
    rw [sub_add_sub_cancel,mem_sphere_iff_norm.mp hw] at h
    linarith
  have h := derivative_on_circle H H_entire z (1/20) (33/1000) (by norm_num) hc
  norm_num at h ⊢
  exact h

lemma error_derivative (z : ℂ) (hz : ‖z-c‖ ≤ (63/20:ℝ)) :
    ‖deriv (fun w => (10^40:ℂ)*CertifiedLocalXi.xi w-P w) z‖ ≤ 2 := by
  have he : (fun w => (10^40:ℂ)*CertifiedLocalXi.xi w-P w) = G+H := by
    funext w
    simp only [Pi.add_apply,G,H]
    ring
  rw [he,deriv_add (G_entire z) (H_entire z)]
  have hg := G_derivative z hz
  have hh := H_derivative z hz
  have h := norm_add_le (deriv G z) (deriv H z)
  linarith

end RH124p5Wide

theorem solution (z : ℂ)
    (hz : ‖z-RH1000Analytic.CertifiedLocalXi.center (249/2)‖ ≤ (63/20:ℝ)) :
    ‖deriv (fun w : ℂ => ((10^40:ℕ):ℂ)*RH1000Analytic.CertifiedLocalXi.xi w-
      TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH124p5RoundedCoefficients14
        (10^14) 60 (249/2) w) z‖ ≤ 2 := by
  have h := RH124p5Wide.error_derivative z (by
    simpa [RH124p5Wide.c,RH124p5Proof.CertifiedLocalXi.center,
      RH1000Analytic.CertifiedLocalXi.center] using hz)
  simpa only [RH124p5Wide.P,RH124p5Numerical.proposed,RH124p5Numerical.rounded,
    RH124p5Numerical.roundedNumerators,RH124p5Proof.CertifiedLocalXi.xi,
    RH1000Analytic.CertifiedLocalXi.xi,RH124p5Proof.CertifiedLocalXi.rotatedPolynomial,
    RH124p5Proof.CertifiedLocalXi.rotatedVariable,RH124p5Proof.CertifiedLocalXi.center,
    TaoFivePrimes_RHLocalRationalPolynomial,RH1000Analytic.CertifiedLocalXi.center,
    TaoFivePrimes_RH124p5RoundedCoefficients14,Complex.ofReal_div,Nat.cast_pow,Nat.cast_ofNat] using h
