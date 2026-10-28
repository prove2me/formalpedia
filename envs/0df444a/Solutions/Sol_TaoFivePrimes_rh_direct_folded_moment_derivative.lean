-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_folded_moment_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:54:16.36034+00:00
-- url     : https://prove2.me/submissions/49779650-3daa-4249-a454-a73436b6fe4b

import Definitions.Def_TaoFivePrimes_RHDirectOscillatoryQuadrature
/- Adapted local xi estimate for the height-106–107 slice.
The analytic foundations and proposed Mellin moments are retained from the
ACCEPTED height-14–100 pilot: original proof/certificate sometik179,
theta/Mellin foundations Gabewhigham. New local coefficients are computed
exactly at height 106.5 and will be checked by ordinary Lean proofs. -/
import Theorems.Thm_TaoFivePrimes_rh_moments_336_enclosed_1e55
import Mathlib.Tactic
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Definitions.Def_TaoFivePrimes_RHLocalRationalPolynomial
import Definitions.Def_TaoFivePrimes_RH128RoundedCoefficients14
import Theorems.Thm_TaoFivePrimes_rh128_translation_precision14
import Theorems.Thm_TaoFivePrimes_rh128_translation_tail60
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option linter.ambiguousOpen false
noncomputable def RH128RoundingBound (n : ℕ) : ℝ :=
  if n < 22 then 1/10^14 else if n < 25 then 2/10^15
  else if n < 30 then 1/10^18 else 1/10^24

lemma RH128RoundingBound_nonneg (n : ℕ) : 0 ≤ RH128RoundingBound n := by
  unfold RH128RoundingBound
  split_ifs <;> norm_num

noncomputable def RH128RoundingBound60 (n : ℕ) : ℝ :=
  if n < 40 then RH128RoundingBound n else 1/10^32

lemma RH128RoundingBound60_nonneg (n : ℕ) : 0 ≤ RH128RoundingBound60 n := by
  unfold RH128RoundingBound60
  split_ifs
  · exact RH128RoundingBound_nonneg n
  · norm_num

namespace RH128Proof
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

lemma norm_taylor_remainder_672 (z : ℂ) (hz : ‖z - 1 / 2‖ ≤  (131)) :
    ‖completedRiemannZeta₀ z - ∑ n ∈ range 672, taylorTerm z n‖ ≤  8 / 10 ^ 49 := by
  have hr := norm_taylor_remainder_le z (by linarith) 672
  have hq : ‖z - 1 / 2‖ / 272 ≤  (131 / 272 : ℝ) := by linarith
  have hq0 : 0 ≤  ‖z - 1 / 2‖ / 272 := by positivity
  apply hr.trans
  calc
    ((65*10^163)) * (‖z - 1 / 2‖ / 272) ^ 672 / (1 - ‖z - 1 / 2‖ / 272) ≤ 
        ((65*10^163)) * (131 / 272 : ℝ) ^ 672 / (1 - 131 / 272) := by
      gcongr
    _ ≤  8 / 10 ^ 49 := by norm_num

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


section DirectFoldedMoment

open Complex MeasureTheory Set HurwitzZeta
open scoped Topology
namespace DirectFoldedMoment

noncomputable def integrand (n : ℕ) (τ t : ℝ) : ℂ :=
  (t:ℂ)^((1/4:ℂ)+Complex.I*(τ:ℂ)-1) • TaoZetaCertificate.logKernel n t

noncomputable def outer (n : ℕ) (τ t : ℝ) : ℂ :=
  ((t^(-3/4:ℝ)*(Real.log t)^n*(evenKernel 0 t-1):ℝ):ℂ) *
    Complex.exp (Complex.I*(τ:ℂ)*(Real.log t:ℂ))

lemma cpow_phase (t τ : ℝ) (ht : 0<t) :
    (t:ℂ)^(((-3/4:ℝ):ℂ)+Complex.I*(τ:ℂ)) =
      ((t^(-3/4:ℝ):ℝ):ℂ)*Complex.exp (Complex.I*(τ:ℂ)*(Real.log t:ℂ)) := by
  have htn : (t:ℂ)≠0 := by exact_mod_cast ne_of_gt ht
  rw [Complex.cpow_add _ _ htn,← Complex.ofReal_cpow ht.le,
    Complex.cpow_def_of_ne_zero htn,Complex.ofReal_log ht.le]
  congr 1
  ring

lemma integrand_outer (n : ℕ) (τ : ℝ) {t : ℝ} (ht : 1<t) :
    integrand n τ t = outer n τ t := by
  have ht0 : 0<t := by linarith
  unfold integrand outer
  rw [TaoZetaCertificate.logKernel_eq, ZetaSix.f_modif_of_one_lt ht]
  have he : (1/4:ℂ)+Complex.I*(τ:ℂ)-1 =
      ((-3/4:ℝ):ℂ)+Complex.I*(τ:ℂ) := by norm_num; ring
  rw [he,cpow_phase t τ ht0]
  simp only [Complex.real_smul,smul_eq_mul]
  push_cast
  ring

lemma integrand_inner (n : ℕ) (τ : ℝ) {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    integrand n τ t =
      ((t^(-5/4:ℝ)*(Real.log t)^n*(evenKernel 0 (1/t)-1):ℝ):ℂ) *
        Complex.exp (Complex.I*(τ:ℂ)*(Real.log t:ℂ)) := by
  unfold integrand
  rw [TaoZetaCertificate.logKernel_eq, ZetaSix.f_modif_of_lt_one ht ht1,
    ZetaSix.evenKernel_eq_of_pos ht]
  have he : (1/4:ℂ)+Complex.I*(τ:ℂ)-1 =
      ((-3/4:ℝ):ℂ)+Complex.I*(τ:ℂ) := by norm_num; ring
  rw [he,cpow_phase t τ ht]
  have hpow : t^(-5/4:ℝ)=t^(-3/4:ℝ)*t^(-(1:ℝ)/2) := by
    rw [← Real.rpow_add ht]
    norm_num
  rw [hpow]
  simp only [Complex.real_smul,smul_eq_mul]
  push_cast
  ring

private noncomputable def outerIndicator (n : ℕ) (τ : ℝ) : ℝ → ℂ :=
  (Ioi 1).indicator (outer n τ)

private lemma integral_outerIndicator (n : ℕ) (τ : ℝ) :
    (∫ t in Ioi (0:ℝ), outerIndicator n τ t) =
      ∫ t in Ioi 1, outer n τ t := by
  rw [outerIndicator,integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi,Ioi_inter_Ioi]
  norm_num

private lemma reciprocal_integrand (n : ℕ) (τ : ℝ) (t : ℝ) (ht : t∈Ioi (0:ℝ)) :
    (|(-1:ℝ)| * t^((-1:ℝ)-1)) • outerIndicator n (-τ) (t^(-1:ℝ)) =
      (-1:ℂ)^n * (Ioo (0:ℝ) 1).indicator (integrand n τ) t := by
  have ht0 : 0<t := ht
  rw [Real.rpow_neg_one]
  rcases lt_or_ge t 1 with h | h
  · have hinv : 1<t⁻¹ := by rw [lt_inv_comm₀ (by norm_num) ht0]; simpa using h
    rw [indicator_of_mem (show t∈Ioo (0:ℝ) 1 from ⟨ht0,h⟩),
      outerIndicator,indicator_of_mem (show t⁻¹∈Ioi (1:ℝ) from hinv),
      integrand_inner n τ ht0 h]
    unfold outer
    have hpow : (t⁻¹)^(-3/4:ℝ)=t^(3/4:ℝ) := by
      rw [← Real.rpow_neg_one t,← Real.rpow_mul ht0.le]
      norm_num
    have hlog : (Real.log t⁻¹)^n=(-1:ℝ)^n*(Real.log t)^n := by
      rw [Real.log_inv,neg_pow]
    have hphase : Complex.exp (Complex.I*((-τ:ℝ):ℂ)*(Real.log t⁻¹:ℂ)) =
        Complex.exp (Complex.I*(τ:ℂ)*(Real.log t:ℂ)) := by
      rw [Real.log_inv]
      congr 1
      push_cast
      ring
    rw [hpow,hlog,hphase]
    have he : t^(-2:ℝ)*t^(3/4:ℝ)=t^(-(5/4):ℝ) := by
      rw [← Real.rpow_add ht0]
      norm_num
    norm_num only [abs_neg,abs_one,one_mul]
    rw [Complex.real_smul]
    push_cast
    have heC : ((t^(-2:ℝ):ℝ):ℂ)*((t^(3/4:ℝ):ℝ):ℂ) =
        ((t^(-(5/4):ℝ):ℝ):ℂ) := by exact_mod_cast he
    simp only [one_div]
    rw [←heC]
    ring
  · have hinv : t⁻¹≤1 := by rw [inv_le_one_iff₀]; right; exact h
    rw [indicator_of_notMem (by simp; intro _; exact h),outerIndicator,
      indicator_of_notMem (by simpa using not_lt.mpr hinv)]
    simp

lemma integral_inner (n : ℕ) (τ : ℝ) :
    (∫ t in Ioc (0:ℝ) 1, integrand n τ t) =
      (-1:ℂ)^n * ∫ t in Ioi 1, outer n (-τ) t := by
  have h := integral_comp_rpow_Ioi (outerIndicator n (-τ)) (by norm_num : (-1:ℝ)≠0)
  rw [integral_outerIndicator, setIntegral_congr_fun measurableSet_Ioi (reciprocal_integrand n τ)] at h
  rw [integral_const_mul,integral_indicator measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo,
    show Ioo (0:ℝ) 1 ∩ Ioi 0 = Ioo (0:ℝ) 1 by ext t; simp; tauto] at h
  rw [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (a := (0:ℝ)) (b := 1))]
  rw [←h,←mul_assoc,← mul_pow]
  norm_num

lemma mellin_folded (n : ℕ) (τ : ℝ) :
    mellin (TaoZetaCertificate.logKernel n) ((1/4:ℂ)+Complex.I*(τ:ℂ)) =
      (∫ t in Ioi 1, outer n τ t) +
        (-1:ℂ)^n * ∫ t in Ioi 1, outer n (-τ) t := by
  have hi : IntegrableOn (integrand n τ) (Ioi (0:ℝ)) :=
    TaoZetaCertificate.logKernel_mellin_convergent n ((1/4:ℂ)+Complex.I*(τ:ℂ))
  have hi0 := hi.mono_set (Ioc_subset_Ioi_self : Ioc (0:ℝ) 1 ⊆ Ioi 0)
  have hi1 := hi.mono_set (Ioi_subset_Ioi (show (0:ℝ)≤1 by norm_num))
  change (∫ t in Ioi (0:ℝ), integrand n τ t) = _
  rw [show Ioi (0:ℝ)=Ioc 0 1 ∪ Ioi 1 from (Ioc_union_Ioi_eq_Ioi zero_le_one).symm]
  rw [setIntegral_union (by simp [Set.disjoint_left]) measurableSet_Ioi hi0 hi1,
    integral_inner n τ,
    setIntegral_congr_fun measurableSet_Ioi (fun t ht => integrand_outer n τ ht)]
  ring

lemma outer_eq_raw (n : ℕ) (τ t : ℝ) :
    outer n τ t = (n.factorial:ℂ) *
      (((CertifiedZetaQuadrature.momentWeight 1 n t * (evenKernel 0 t-1):ℝ):ℂ) *
        Complex.exp (Complex.I*(τ:ℂ)*(Real.log t:ℂ))) := by
  have hn : (n.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  unfold outer CertifiedZetaQuadrature.momentWeight
  push_cast
  field_simp

lemma outer_integral (n : ℕ) (τ : ℝ) :
    (∫ t in Ioi 1, outer n τ t) =
      (n.factorial:ℂ)*RHDirectOscillatory.rawIntegral τ n := by
  unfold RHDirectOscillatory.rawIntegral
  rw [← integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => outer_eq_raw n τ t)

lemma folded_deriv (n : ℕ) (τ : ℝ) :
    iteratedDeriv n completedRiemannZeta₀ ((1/2:ℂ)+2*Complex.I*(τ:ℂ)) /
      (n.factorial:ℂ) =
      (RHDirectOscillatory.rawIntegral τ n +
        (-1:ℂ)^n*RHDirectOscillatory.rawIntegral (-τ) n)/(2:ℂ)^(n+1) := by
  rw [TaoZetaCertificate.completedZeta_derivative_moment]
  have hc : ((1/2:ℂ)+2*Complex.I*(τ:ℂ))/2 =
      (1/4:ℂ)+Complex.I*(τ:ℂ) := by ring
  rw [hc,mellin_folded,outer_integral,outer_integral]
  have hn : (n.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

end DirectFoldedMoment
end DirectFoldedMoment
end RH128Proof

theorem solution (n : ℕ) (τ : ℝ) :
    iteratedDeriv n completedRiemannZeta₀ ((1/2:ℂ)+2*Complex.I*(τ:ℂ)) /
      (n.factorial:ℂ) =
      (RHDirectOscillatory.rawIntegral τ n +
        (-1:ℂ)^n*RHDirectOscillatory.rawIntegral (-τ) n)/(2:ℂ)^(n+1) :=
  RH128Proof.DirectFoldedMoment.folded_deriv n τ
