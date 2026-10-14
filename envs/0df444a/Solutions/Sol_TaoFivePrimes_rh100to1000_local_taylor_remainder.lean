-- Prove2me | solution 1 for TaoFivePrimes.rh100to1000_local_taylor_remainder
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-14T02:53:50.000232+00:00
-- url     : https://prove2.me/submissions/da08fb65-aa8c-4929-a7f7-2f69e3968a3d

/- Local analytic extension for the existing height-100–1000 milestone.
The general Cauchy bound and strip estimate are copied from the accepted pilot;
only the explicit vertical bound and Taylor order are extended. Original
analytic proof: sometik179, with theta/Mellin attribution to Gabewhigham. -/
import Definitions.Def_TaoFivePrimes_RH100To1000LocalAnalyticModel
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false
set_option linter.unusedSimpArgs false
namespace RH1000Analytic
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
open TaoZetaBounds

end CertifiedZetaQuadrature

end Height100Module12

section Height100Module13

open Complex Finset Metric

namespace CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module13

section Height100Module14

open Real MeasureTheory Set Filter HurwitzZeta
namespace CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module14

section Height100Module15

open Complex MeasureTheory Metric Set Finset
namespace CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module15

section Height100Module16

open Real MeasureTheory Set Filter Finset
namespace CertifiedZetaQuadrature

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

end TaoZetaWide256

end Height100Module17

section Height100Module18

open Complex Finset Metric
open scoped BigOperators
set_option autoImplicit false
set_option exponentiation.threshold 1024

namespace TaoZetaGlobal

end TaoZetaGlobal

end Height100Module18

section Height100Module19

open Complex MeasureTheory Set Filter Asymptotics
open scoped Topology
set_option autoImplicit false

namespace TaoZetaCertificate

end TaoZetaCertificate

end Height100Module19

section Height100Module20

open Complex MeasureTheory Set HurwitzZeta
set_option autoImplicit false

namespace TaoZetaCertificate

end TaoZetaCertificate

end Height100Module20

section Height100Module21

open Complex MeasureTheory Set
open scoped ComplexConjugate
set_option autoImplicit false

namespace TaoZetaCertificate

lemma conj_kernel {t : ℝ} (ht : 0 < t) :
    conj (ZetaSix.P.f_modif t) = ZetaSix.P.f_modif t := by
  rcases lt_trichotomy t 1 with h | rfl | h
  · rw [ZetaSix.f_modif_of_lt_one ht h]
    simp
  · rw [ZetaSix.f_modif_one]
    simp
  · rw [ZetaSix.f_modif_of_one_lt h]
    simp

lemma completedZeta_conj (s : ℂ) :
    completedRiemannZeta₀ (conj s) = conj (completedRiemannZeta₀ s) := by
  change mellin ZetaSix.P.f_modif (conj s / 2) / 2 =
    conj (mellin ZetaSix.P.f_modif (s / 2) / 2)
  rw [map_div₀, map_ofNat]
  congr 1
  rw [mellin, mellin, ← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht0 : 0 < t := ht
  have htarg : (t : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg ht0.le]
    exact ne_of_lt Real.pi_pos
  have he : conj s / 2 - 1 = conj (s / 2 - 1) := by
    simp only [map_sub, map_div₀, map_one, map_ofNat]
  dsimp only
  rw [he, Complex.cpow_conj _ _ htarg]
  simp only [smul_eq_mul, map_mul, conj_ofReal, conj_kernel ht0]

end TaoZetaCertificate

end Height100Module21

section Height100Module22

open Complex Finset Metric Filter
namespace CertifiedComplexTaylor
open CertifiedTaylorQuadrature

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

end CertifiedComplexTaylor

end Height100Module22

section Height100Module23

open Complex MeasureTheory Set HurwitzZeta Real
open scoped Real
set_option autoImplicit false

namespace TaoZetaWide
open ZetaSix

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

lemma xi_entire : Differentiable ℂ xi := by
  unfold xi
  have hΛ := differentiable_completedZeta₀
  fun_prop

end CertifiedLocalXi

end Height100Module24

section Height100Module25

open Complex MeasureTheory Set Finset
namespace CertifiedGlobalMoments
open CertifiedZetaQuadrature TaoZetaCertificate

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

lemma xi_critical_real (T : ℝ) : (xi (center T)).im=0 := by
  have hc : conj (center T)=1-center T := by
    apply Complex.ext <;> simp [center]
    ring
  have he := TaoZetaCertificate.completedZeta_conj (center T)
  rw [hc,completedRiemannZeta₀_one_sub] at he
  have hi := congrArg Complex.im he
  simp only [conj_im] at hi
  have hΛ : (completedRiemannZeta₀ (center T)).im=0 := by linarith
  have hf : (center T*(center T-1)/2).im=0 := by
    norm_num [center,mul_im]
    ring
  unfold xi
  simp [mul_im,hf,hΛ]

end CertifiedLocalXi

end Height100Module28

section Height100Module29

open Complex Finset
namespace CertifiedLocalXi

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

end CertifiedPolynomialTranslation

end Height100Module31

section Height100Module32

open Complex Finset
namespace CertifiedPolynomialTranslation
open CertifiedTaylorQuadrature CertifiedGlobalMoments

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

end CertifiedZetaQuadrature

end Height100Module50

section Height100Module51

open Complex Metric Finset
namespace CertifiedZetaQuadrature
set_option exponentiation.threshold 512
open CertifiedTaylorQuadrature CertifiedMomentConvolution

end CertifiedZetaQuadrature

end Height100Module51

section Height100Module52

open Complex Finset
namespace CertifiedZetaQuadrature
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

end CertifiedZetaQuadrature

end Height100Module56

section Height100Module57

open Complex Metric Finset MeasureTheory
namespace CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module57

section Height100Module58
open Complex Metric MeasureTheory
namespace CertifiedZetaQuadrature
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
open CertifiedMomentConvolution CertifiedTaylorQuadrature

end CertifiedZetaQuadrature

end Height100Module60

section Height100Module61

open Complex Metric Finset
namespace CertifiedZetaQuadrature
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

end TaoZetaNumerics

end Height100Module97

section Height100Module98

open Finset
open scoped unitInterval
set_option autoImplicit false
set_option maxHeartbeats 0

namespace TaoZetaNumerics

end TaoZetaNumerics

end Height100Module98

section Height100Module99

namespace CertifiedLocalPolynomial
open TaoZetaPoly Complex Finset TaoZetaNumerics
open scoped unitInterval

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

open Complex Metric
namespace CertifiedLocalXi
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
lemma local_tail_norm_1000 (T : ℝ) (hT : |T| ≤ 1000) (z : ℂ)
    (hz : ‖z-center T‖ ≤ 1) :
    ‖CertifiedComplexTaylor.remainder xi (center T) 272 z‖ ≤ 1/10^365 := by
  have h := CertifiedComplexTaylor.remainder_bound xi xi_entire (center T)
    24 400000000 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (xi_circle_bound_1000 T hT) 272 z hz
  apply h.trans
  norm_num
end CertifiedLocalXi

end RH1000Analytic

theorem TaoFivePrimes.rh100to1000_local_taylor_remainder (T : ℝ) (hT : |T| ≤ 1000) (z : ℂ)
    (hz : ‖z-RH1000Analytic.CertifiedLocalXi.center T‖ ≤ 1) :
    ‖RH1000Analytic.CertifiedComplexTaylor.remainder
      RH1000Analytic.CertifiedLocalXi.xi
      (RH1000Analytic.CertifiedLocalXi.center T) 272 z‖ ≤ 1/10^365 :=
  RH1000Analytic.CertifiedLocalXi.local_tail_norm_1000 T hT z hz

theorem solution (T : ℝ) (hT : |T| ≤ 1000) (z : ℂ)
    (hz : ‖z-RH1000Analytic.CertifiedLocalXi.center T‖ ≤ 1) :
    ‖RH1000Analytic.CertifiedComplexTaylor.remainder
      RH1000Analytic.CertifiedLocalXi.xi
      (RH1000Analytic.CertifiedLocalXi.center T) 272 z‖ ≤ 1/10^365 :=
  TaoFivePrimes.rh100to1000_local_taylor_remainder T hT z hz
