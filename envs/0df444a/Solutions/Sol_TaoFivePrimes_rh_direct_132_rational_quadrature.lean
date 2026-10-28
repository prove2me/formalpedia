-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_132_rational_quadrature
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:49:05.426323+00:00
-- url     : https://prove2.me/submissions/4909aa32-f762-4f11-a4fc-822cec2d8b57

import Definitions.Def_TaoFivePrimes_RHDirectOscillatoryQuadrature
import Definitions.Def_TaoFivePrimes_RHDirect132Rule
import Theorems.Thm_TaoFivePrimes_rh_direct_oscillatory_quadrature
import Theorems.Thm_TaoFivePrimes_rh_direct_phase_132_panels
import Theorems.Thm_TaoFivePrimes_rh_direct_base_theta_jets
import Theorems.Thm_TaoFivePrimes_rh_moment_kernel_radius_11o10
import Definitions.Def_TaoFivePrimes_RH14To100MomentModel
import Theorems.Thm_TaoFivePrimes_rh14to100_theta_checks
import Definitions.Def_TaoFivePrimes_RHExtendedMomentRule
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

import Mathlib.Algebra.BigOperators.Intervals

import Mathlib.Algebra.BigOperators.Ring.Finset

import Mathlib.Analysis.Calculus.Deriv.Star

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

import Mathlib.Analysis.Calculus.MeanValue

import Mathlib.Analysis.Complex.Exponential

import Mathlib.Analysis.Complex.ExponentialBounds

import Mathlib.Analysis.Complex.Liouville

import Mathlib.Analysis.Complex.TaylorSeries

import Mathlib.Analysis.MellinTransform

import Mathlib.Analysis.Real.Pi.Bounds

import Mathlib.Analysis.SpecialFunctions.Bernstein

import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

import Mathlib.Analysis.SpecificLimits.Normed

import Mathlib.Data.Complex.Basic

import Mathlib.Data.Int.Basic

import Mathlib.Data.Int.Cast.Lemmas

import Mathlib.Data.List.GetD

import Mathlib.Data.List.OfFn

import Mathlib.Data.Nat.Bitwise

import Mathlib.Data.Nat.Cast.Field

import Mathlib.Data.Nat.Cast.Order.Field

import Mathlib.Data.Nat.Choose.Cast

import Mathlib.Data.Nat.Digits.Lemmas

import Mathlib.Data.Nat.Factorial.Basic

import Mathlib.MeasureTheory.Integral.Gamma

import Mathlib.MeasureTheory.Integral.IntegralEqImproper

import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

import Mathlib.NumberTheory.LSeries.HurwitzZetaEven

import Mathlib.NumberTheory.LSeries.Nonvanishing

import Mathlib.NumberTheory.LSeries.RiemannZeta

import Mathlib.Tactic

import Mathlib.Tactic.GCongr

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.ambiguousOpen false
namespace RH14MomentEnclosureProof
section Height100Module0

open Finset
namespace CertifiedPackedConvolution
open _root_.CertifiedPackedConvolution

noncomputable def coefficient : List ℕ → ℕ → ℕ
  | [], _ => 0
  | x::_, 0 => x
  | _::xs, n+1 => coefficient xs n

noncomputable def addLists : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | xs, [] => xs
  | x::xs, y::ys => (x+y)::addLists xs ys

noncomputable def convolution : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | x::xs, ys => addLists (ys.map (x*·)) (0::convolution xs ys)

lemma coefficient_eq_getD (xs : List ℕ) (k : ℕ) : coefficient xs k=xs.getD k 0 := by
  induction xs generalizing k with
  | nil => simp [coefficient,List.getD]
  | cons x xs ih => cases k <;> simp [coefficient,List.getD,ih]

lemma coefficient_add (xs ys : List ℕ) (k : ℕ) :
    coefficient (addLists xs ys) k=coefficient xs k+coefficient ys k := by
  induction xs generalizing ys k with
  | nil => simp [addLists,coefficient]
  | cons x xs ih =>
    cases ys with
    | nil => simp [addLists,coefficient]
    | cons y ys => cases k <;> simp [addLists,coefficient,ih]

lemma coefficient_map (a : ℕ) (xs : List ℕ) (k : ℕ) :
    coefficient (xs.map (a*·)) k=a*coefficient xs k := by
  induction xs generalizing k with
  | nil => simp [coefficient]
  | cons x xs ih => cases k <;> simp [coefficient,ih]

lemma ofDigits_add (B : ℕ) (xs ys : List ℕ) :
    Nat.ofDigits B (addLists xs ys)=Nat.ofDigits B xs+Nat.ofDigits B ys := by
  induction xs generalizing ys with
  | nil => simp [addLists]
  | cons x xs ih =>
    cases ys with
    | nil => simp [addLists]
    | cons y ys => simp only [addLists,Nat.ofDigits_cons,ih]; ring

lemma ofDigits_map_mul (B a : ℕ) (xs : List ℕ) :
    Nat.ofDigits B (xs.map (a*·))=a*Nat.ofDigits B xs := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,Nat.ofDigits_cons,ih]; ring

lemma ofDigits_convolution (B : ℕ) (xs ys : List ℕ) :
    Nat.ofDigits B (convolution xs ys)=Nat.ofDigits B xs*Nat.ofDigits B ys := by
  induction xs with
  | nil => simp [convolution]
  | cons x xs ih =>
    rw [convolution,ofDigits_add,ofDigits_map_mul,Nat.ofDigits_cons,ih,Nat.ofDigits_cons]
    ring

lemma sum_convolution (xs ys : List ℕ) : (convolution xs ys).sum=xs.sum*ys.sum := by
  simpa only [Nat.ofDigits_one] using ofDigits_convolution 1 xs ys

lemma coefficient_convolution (xs ys : List ℕ) (k : ℕ) :
    coefficient (convolution xs ys) k=
      ∑ i ∈ range (k+1), coefficient xs i*coefficient ys (k-i) := by
  induction xs generalizing k with
  | nil => simp [convolution,coefficient]
  | cons x xs ih =>
    cases k with
    | zero => simp [convolution,coefficient_add,coefficient_map,coefficient]
    | succ k =>
      rw [convolution,coefficient_add,coefficient_map,coefficient,ih]
      conv_rhs => rw [sum_range_succ']
      simp only [coefficient,Nat.add_sub_add_right,Nat.sub_zero]
      rw [add_comm]

lemma member_le_sum (xs : List ℕ) (x : ℕ) (hx : x∈xs) : x≤ xs.sum := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    rcases List.mem_cons.mp hx with rfl|hx
    · simp
    · have h := ih hx
      simp only [List.sum_cons]
      omega

lemma digit_ofDigits (B : ℕ) (hB : 0< B) (xs : List ℕ)
    (hsmall : ∀ x∈xs,x< B) (k : ℕ) :
    (Nat.ofDigits B xs/B^k)%B=coefficient xs k := by
  induction k generalizing xs with
  | zero =>
    cases xs with
    | nil => simp [coefficient]
    | cons x xs =>
      have hx := hsmall x List.mem_cons_self
      simp [Nat.ofDigits_cons,coefficient,Nat.add_mod,Nat.mod_eq_of_lt hx]
  | succ k ih =>
    rw [Nat.pow_succ',← Nat.div_div_eq_div_mul,
      Nat.ofDigits_div_eq_ofDigits_tail hB xs hsmall]
    rw [ih xs.tail (fun x hx => hsmall x (List.mem_of_mem_tail hx))]
    cases xs <;> simp [coefficient]

/-- One scalar no-carry check suffices for every convolution digit. -/
theorem packed_product_digit (B : ℕ) (hB : 0< B) (xs ys : List ℕ)
    (hcarry : xs.sum*ys.sum< B) (k : ℕ) :
    ((Nat.ofDigits B xs*Nat.ofDigits B ys)/B^k)%B =
      ∑ i ∈ range (k+1), xs.getD i 0*ys.getD (k-i) 0 := by
  rw [← ofDigits_convolution]
  have hs : ∀ x∈convolution xs ys,x< B := by
    intro x hx
    have h := member_le_sum (convolution xs ys) x hx
    rw [sum_convolution] at h
    exact h.trans_lt hcarry
  rw [digit_ofDigits B hB _ hs,coefficient_convolution]
  simp_rw [coefficient_eq_getD]

lemma encode_eq_ofDigits (bits : ℕ) (xs : List ℕ) :
    encode bits xs=Nat.ofDigits (2^bits) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [encode,Nat.ofDigits_cons,Nat.shiftLeft_eq',Nat.shiftLeft_eq,ih]; ring

/-- Binary-stride encoding has the same verified digit-extraction rule. -/
theorem shift_product_digit (bits : ℕ) (xs ys : List ℕ)
    (hcarry : xs.sum*ys.sum<2^bits) (k : ℕ) :
    ((encode bits xs*encode bits ys)/(2^bits)^k)%(2^bits) =
      ∑ i ∈ range (k+1), xs.getD i 0*ys.getD (k-i) 0 := by
  rw [encode_eq_ofDigits,encode_eq_ofDigits]
  exact packed_product_digit _ (by positivity) xs ys hcarry k

/-- Direct bit-shift extraction avoids constructing a large divisor in executable checks. -/
theorem shiftRight_product_digit (bits : ℕ) (xs ys : List ℕ)
    (hcarry : xs.sum*ys.sum<2^bits) (k : ℕ) :
    ((encode bits xs*encode bits ys) >>> (bits*k))%(2^bits) =
      ∑ i ∈ range (k+1), xs.getD i 0*ys.getD (k-i) 0 := by
  rw [Nat.shiftRight_eq_div_pow,pow_mul]
  exact shift_product_digit bits xs ys hcarry k

end CertifiedPackedConvolution

end Height100Module0

section Height100Module1

set_option autoImplicit false
open Finset
open scoped BigOperators

namespace CertifiedMomentConvolution
open _root_.CertifiedMomentConvolution

lemma sum_triangle {R : Type*} [AddCommMonoid R] (N : ℕ) (f : ℕ → ℕ → R) :
    (∑ j ∈ range N, ∑ m ∈ range (j+1), f m (j-m)) =
      ∑ m ∈ range N, ∑ l ∈ range (N-m), f m l := by
  classical
  rw [sum_sigma', sum_sigma']
  apply sum_bij (fun x _ => ⟨x.2, x.1-x.2⟩)
  · intro x hx
    simp only [mem_sigma, mem_range] at hx ⊢
    omega
  · intro x hx y hy hxy
    simp only [mem_sigma, mem_range] at hx hy
    have h1 := congrArg Sigma.fst hxy
    have h2 := congrArg (fun z : Sigma (fun _ : ℕ => ℕ) => z.2) hxy
    apply Sigma.ext <;> simp_all
    omega
  · intro y hy
    simp only [mem_sigma, mem_range] at hy
    refine ⟨⟨y.1+y.2, y.1⟩, ?_, ?_⟩
    · simp only [mem_sigma, mem_range]
      omega
    · simp
  · intro x hx
    rfl

/-- A truncated convolution can be integrated by first correlating the base
coefficients with the integration weights. -/
theorem integrated_convolution {R : Type*} [CommSemiring R]
    (N : ℕ) (a h w : ℕ → R) :
    (∑ j ∈ range N, (∑ m ∈ range (j+1), a m * h (j-m)) * w j) =
      ∑ m ∈ range N, a m * (∑ l ∈ range (N-m), h l * w (m+l)) := by
  simp_rw [sum_mul]
  calc
    (∑ j ∈ range N, ∑ m ∈ range (j+1), a m * h (j-m) * w j) =
        ∑ j ∈ range N, ∑ m ∈ range (j+1), a m * h (j-m) * w (m+(j-m)) := by
      apply sum_congr rfl
      intro j hj
      apply sum_congr rfl
      intro m hm
      congr 2
      have hmj : m≤ j := by simpa using mem_range.mp hm
      omega
    _ = ∑ m ∈ range N, ∑ l ∈ range (N-m), a m * h l * w (m+l) :=
      sum_triangle N (fun m l => a m * h l * w (m+l))
    _ = _ := by simp_rw [mul_sum, mul_assoc]

/-- The common base correlation is independent of the moment order. -/
noncomputable def correlation {R : Type*} [Semiring R] (N : ℕ) (h w : ℕ → R) (m : ℕ) : R :=
  ∑ l ∈ range (N-m), h l * w (m+l)

end CertifiedMomentConvolution

end Height100Module1

section Height100Module2

open Complex MeasureTheory Finset Metric Set

namespace CertifiedTaylorQuadrature
open _root_.CertifiedTaylorQuadrature

noncomputable def coefficient (f : ℂ → ℂ) (c : ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n f c / (n.factorial:ℂ)

noncomputable def polynomial (f : ℂ → ℂ) (c : ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ range N, coefficient f c n * (x:ℂ)^n

noncomputable def panel (f : ℂ → ℂ) (c : ℂ) (h : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ range N, coefficient f c n *
    (((h:ℂ)^(n+1)-(-h:ℂ)^(n+1))/(n+1))

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

lemma series_sum (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c : ℂ) (x : ℝ) :
    HasSum (fun n : ℕ => coefficient f c n*(x:ℂ)^n) (f (c+x)) := by
  have h := Complex.hasSum_taylorSeries_of_entire hf c (c+x)
  convert! h using 1
  ext n
  simp only [coefficient, add_sub_cancel_left, smul_eq_mul]
  ring

lemma point_error (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c : ℂ)
    (R M h : ℝ) (hR : 0< R) (hM : 0≤ M) (hh : 0≤ h) (hhR : h< R)
    (hb : ∀ z ∈ sphere c R, ‖f z‖≤ M) (N : ℕ) (x : ℝ) (hx : |x|≤ h) :
    ‖f (c+x)-polynomial f c N x‖ ≤  M*(h/R)^N/(1-h/R) := by
  have hq0 : 0≤ h/R := div_nonneg hh hR.le
  have hq1 : h/R<1 := (div_lt_one hR).mpr hhR
  have hs := series_sum f hf c x
  have he : f (c+x)-polynomial f c N x =
      ∑' n : ℕ, coefficient f c (n+N)*(x:ℂ)^(n+N) := by
    have h := hs.summable.sum_add_tsum_nat_add N
    rw [hs.tsum_eq] at h
    unfold polynomial
    apply sub_eq_iff_eq_add.mpr
    simpa [add_comm] using h.symm
  rw [he]
  have hgeo : HasSum (fun n : ℕ => (M*(h/R)^N)*(h/R)^n)
      ((M*(h/R)^N)*(1-h/R)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0 hq1).mul_left (M*(h/R)^N)
  have hterms : ∀ n : ℕ, ‖coefficient f c (n+N)*(x:ℂ)^(n+N)‖ ≤  (M*(h/R)^N)*(h/R)^n := by
    intro n
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    calc
      ‖coefficient f c (n+N)‖*|x|^(n+N) ≤  (M/R^(n+N))*h^(n+N) := by
        gcongr
        exact coefficient_bound f hf c R M hR hb (n+N)
      _ = (M*(h/R)^N)*(h/R)^n := by rw [div_pow, div_pow, pow_add, pow_add]; ring
  have ht := tsum_of_norm_bounded hgeo hterms
  simpa only [div_eq_mul_inv] using ht

lemma polynomial_integrable (f : ℂ → ℂ) (c : ℂ) (N : ℕ) (a b : ℝ) :
    IntervalIntegrable (polynomial f c N) volume a b := by
  apply Continuous.intervalIntegrable
  unfold polynomial
  fun_prop

lemma integral_polynomial (f : ℂ → ℂ) (c : ℂ) (h : ℝ) (N : ℕ) :
    (∫ x in -h..h, polynomial f c N x) = panel f c h N := by
  unfold polynomial panel
  rw [intervalIntegral.integral_finsetSum (fun n _ => (by
    apply Continuous.intervalIntegrable
    fun_prop))]
  apply sum_congr rfl
  intro n _
  rw [intervalIntegral.integral_const_mul]
  congr 1
  rw [show (fun x : ℝ => (x:ℂ)^n) = (fun x : ℝ => ((x^n:ℝ):ℂ)) by ext x; push_cast; rfl,
    intervalIntegral.integral_ofReal, integral_pow]
  push_cast
  rfl

/-- A complex analytic function can be integrated by a finite Taylor polynomial with a
geometric, arbitrarily high-order error bound. Every coefficient remains exact. -/
theorem panel_error (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c : ℂ)
    (R M h : ℝ) (hR : 0< R) (hM : 0≤ M) (hh : 0≤ h) (hhR : h< R)
    (hb : ∀ z ∈ sphere c R, ‖f z‖≤ M) (N : ℕ) :
    ‖(∫ x in -h..h, f (c+x))-panel f c h N‖ ≤ 
      2*h*M*(h/R)^N/(1-h/R) := by
  rw [← integral_polynomial]
  have hfint : IntervalIntegrable (fun x : ℝ => f (c+x)) volume (-h) h :=
    (hf.continuous.comp (by fun_prop)).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub hfint (polynomial_integrable f c N (-h) h)]
  have he := intervalIntegral.norm_integral_le_of_norm_le_const (a:=-h) (b:=h)
    (f:=fun x : ℝ => f (c+x)-polynomial f c N x) (C:=M*(h/R)^N/(1-h/R)) (by
      intro x hx
      rw [uIoc_of_le (by linarith : -h≤ h)] at hx
      exact point_error f hf c R M h hR hM hh hhR hb N x
        (abs_le.mpr ⟨hx.1.le,hx.2⟩))
  have ha : |h-(-h)|=2*h := by rw [sub_neg_eq_add, abs_of_nonneg (by linarith)]; ring
  rw [ha] at he
  convert he using 1
  ring

end CertifiedTaylorQuadrature

end Height100Module2

section Height100Module3

set_option autoImplicit false
open Complex Finset
open scoped BigOperators

namespace CertifiedMomentConvolution
open _root_.CertifiedMomentConvolution
open CertifiedTaylorQuadrature
open _root_.CertifiedTaylorQuadrature

lemma coefficient_mul (f g : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (c : ℂ) (n : ℕ) :
    coefficient (fun z => f z * g z) c n =
      ∑ m ∈ range (n+1), coefficient f c m * coefficient g c (n-m) := by
  unfold coefficient
  rw [iteratedDeriv_fun_mul hf.contDiff.contDiffAt hg.contDiff.contDiffAt, sum_div]
  apply sum_congr rfl
  intro m hm
  have hmn : m≤ n := by simpa using mem_range.mp hm
  rw [Nat.cast_choose ℂ hmn]
  have h0 : (n.factorial:ℂ)≠0 := by exact_mod_cast n.factorial_ne_zero
  have h1 : (m.factorial:ℂ)≠0 := by exact_mod_cast m.factorial_ne_zero
  have h2 : ((n-m).factorial:ℂ)≠0 := by exact_mod_cast (n-m).factorial_ne_zero
  field_simp

lemma power_moment_coefficient (a c : ℂ) (k m : ℕ) :
    coefficient (fun z => (a*z)^k / (k.factorial:ℂ)) c m =
      if m≤ k then a^k*c^(k-m)/(((k-m).factorial:ℂ)*m.factorial) else 0 := by
  have he : (fun z : ℂ => (a*z)^k/(k.factorial:ℂ)) =
      (fun z => (a^k/(k.factorial:ℂ))*z^k) := by ext z; simp [mul_pow]; ring
  rw [he, coefficient, iteratedDeriv_const_mul_field, iteratedDeriv_pow]
  by_cases hmk : m≤ k
  · rw [if_pos hmk]
    have hf : ((k-m).factorial:ℂ)*(k.descFactorial m:ℂ) = k.factorial := by
      exact_mod_cast Nat.factorial_mul_descFactorial hmk
    have h0 : (k.factorial:ℂ)≠0 := by exact_mod_cast k.factorial_ne_zero
    have h1 : (m.factorial:ℂ)≠0 := by exact_mod_cast m.factorial_ne_zero
    have h2 : ((k-m).factorial:ℂ)≠0 := by exact_mod_cast (k-m).factorial_ne_zero
    field_simp
    linear_combination (a^k*c^(k-m))*hf
  · rw [if_neg hmk, Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
    simp

noncomputable def scaledCoefficient (f : ℂ → ℂ) (c h : ℂ) (n : ℕ) : ℂ :=
  coefficient f c n * h^n

lemma scaled_power_moment_coefficient (a c h : ℂ) (k m : ℕ) :
    scaledCoefficient (fun z => (a*z)^k / (k.factorial:ℂ)) c h m =
      if m≤ k then (a*c)^(k-m)*(a*h)^m/(((k-m).factorial:ℂ)*m.factorial) else 0 := by
  rw [scaledCoefficient, power_moment_coefficient]
  by_cases hmk : m≤ k
  · rw [if_pos hmk, if_pos hmk]
    have hk : k = (k-m)+m := by omega
    conv_lhs => rw [hk]
    simp only [Nat.add_sub_cancel_right, pow_add, mul_pow]
    ring
  · simp [hmk]

lemma scaled_coefficient_mul (f g : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (c h : ℂ) (n : ℕ) :
    scaledCoefficient (fun z => f z * g z) c h n =
      ∑ m ∈ range (n+1), scaledCoefficient f c h m * scaledCoefficient g c h (n-m) := by
  unfold scaledCoefficient
  rw [coefficient_mul f g hf hg, sum_mul]
  apply sum_congr rfl
  intro m hm
  have hmn : m≤ n := by simpa using mem_range.mp hm
  have hn : n=m+(n-m) := by omega
  conv_lhs => rw [hn]
  simp only [Nat.add_sub_cancel_left, pow_add]
  ring

noncomputable def integrationWeight (j : ℕ) : ℂ :=
  (1 - (-1:ℂ)^(j+1)) / (j+1)

lemma panel_eq_scaled (f : ℂ → ℂ) (c : ℂ) (h : ℝ) (N : ℕ) :
    panel f c h N = (h:ℂ) *
      ∑ j ∈ range N, scaledCoefficient f c h j * integrationWeight j := by
  unfold panel
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  unfold scaledCoefficient integrationWeight
  rw [show (-h:ℂ) = (-1:ℂ)*(h:ℂ) by ring, mul_pow, pow_succ]
  ring

lemma sum_restrict_swap {R : Type*} [AddCommMonoid R] (N k : ℕ) (f : ℕ → R) :
    (∑ m ∈ range N, if m≤ k then f m else 0) =
      ∑ m ∈ range (k+1), if m< N then f m else 0 := by
  classical
  rw [← sum_filter, ← sum_filter]
  congr 1
  ext m
  simp only [mem_filter, mem_range]
  omega

/-- All panel moments are a scalar convolution of a common correlation vector
and the exponential coefficients of the center. -/
theorem power_moment_panel (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (a c : ℂ) (h : ℝ) (N k : ℕ) :
    panel (fun z => (a*z)^k / (k.factorial:ℂ) * f z) c h N =
      (h:ℂ) * ∑ m ∈ range (k+1),
        (if m< N then
          (a*(h:ℂ))^m/(m.factorial:ℂ) *
            correlation N (scaledCoefficient f c h) integrationWeight m
          else 0) * ((a*c)^(k-m)/((k-m).factorial:ℂ)) := by
  rw [panel_eq_scaled]
  congr 1
  have hp : Differentiable ℂ (fun z : ℂ => (a*z)^k / (k.factorial:ℂ)) := by fun_prop
  simp_rw [scaled_coefficient_mul _ _ hp hf,
    scaled_power_moment_coefficient]
  rw [integrated_convolution]
  simp only [correlation]
  simp_rw [ite_mul, zero_mul]
  rw [sum_restrict_swap]
  apply sum_congr rfl
  intro m hm
  by_cases hmn : m< N
  · simp only [if_pos hmn]
    ring
  · simp [hmn]

end CertifiedMomentConvolution

end Height100Module3


end RH14MomentEnclosureProof

open Complex Finset Metric MeasureTheory
open RH14MomentEnclosureProof.CertifiedTaylorQuadrature
open RH14MomentEnclosureProof.CertifiedMomentConvolution

namespace Direct132RuleProof

noncomputable def base : ℂ → ℂ := RHDirectOscillatory.kernel 0 0
noncomputable def phase (z : ℂ) : ℂ := Complex.exp (Complex.I*(66:ℂ)*z)
noncomputable def power (k : ℕ) (z : ℂ) : ℂ := z^k/(k.factorial:ℂ)

noncomputable def baseJet (i j : ℕ) : ℂ :=
  scaledCoefficient base (RHDirect132Rule.center i) (3/16:ℂ) j

noncomputable def exactPanel (i k : ℕ) : ℂ :=
  (3/16:ℂ) * ∑ j ∈ range 184, RHDirect132Rule.weight j *
    ∑ m ∈ range (j+1), RHDirect132Rule.powerJet i k m *
      ∑ l ∈ range (j-m+1), RHDirect132Rule.phaseJet l *
        (phase (RHDirect132Rule.center i) * baseJet i (j-m-l))

lemma base_entire : Differentiable ℂ base := by
  unfold base RHDirectOscillatory.kernel
  fun_prop

lemma phase_entire : Differentiable ℂ phase := by
  unfold phase
  fun_prop

lemma power_entire (k : ℕ) : Differentiable ℂ (power k) := by
  unfold power
  fun_prop

lemma kernel_eq (k : ℕ) :
    RHDirectOscillatory.kernel 66 k = fun z => power k z*(phase z*base z) := by
  funext z
  simp [RHDirectOscillatory.kernel,power,phase,base]
  ring

lemma scaled_power (i k m : ℕ) :
    scaledCoefficient (power k) (RHDirect132Rule.center i) (3/16:ℂ) m =
      RHDirect132Rule.powerJet i k m := by
  change scaledCoefficient (fun z : ℂ => z^k/(k.factorial:ℂ))
    (RHDirect132Rule.center i) (3/16:ℂ) m = _
  have h := scaled_power_moment_coefficient (1:ℂ) (RHDirect132Rule.center i)
    (3/16:ℂ) k m
  simpa [power,RHDirect132Rule.powerJet] using h

lemma scaled_phase (i m : ℕ) :
    scaledCoefficient phase (RHDirect132Rule.center i) (3/16:ℂ) m =
      RHDirect132Rule.phaseJet m * phase (RHDirect132Rule.center i) := by
  unfold scaledCoefficient coefficient phase RHDirect132Rule.phaseJet
  rw [iteratedDeriv_cexp_const_mul]
  simp only [mul_pow]
  ring

lemma exact_panel (i k : ℕ) :
    RHDirectOscillatory.panel 66 k (3*(2*(i:ℝ)+1)/16) = exactPanel i k := by
  have he : RHDirectOscillatory.panel 66 k (3*(2*(i:ℝ)+1)/16) =
      panel (RHDirectOscillatory.kernel 66 k) (RHDirect132Rule.center i) (3/16) 184 := by
    simp [RHDirectOscillatory.panel,RHDirect132Rule.center,panel,coefficient,Complex.ofReal_div]
  rw [he,kernel_eq,panel_eq_scaled]
  simp only [Complex.ofReal_div,Complex.ofReal_ofNat]
  unfold exactPanel
  congr 1
  apply sum_congr rfl
  intro j hj
  have hf : Differentiable ℂ (fun z => phase z*base z) := phase_entire.mul base_entire
  rw [scaled_coefficient_mul _ _ (power_entire k) hf]
  unfold RHDirect132Rule.weight integrationWeight
  rw [mul_comm]
  congr 1
  apply sum_congr rfl
  intro m hm
  rw [scaled_power,scaled_coefficient_mul _ _ phase_entire base_entire]
  congr 1
  apply sum_congr rfl
  intro l hl
  rw [scaled_phase]
  unfold baseJet
  ring

lemma center_bounds (i : ℕ) (hi : i<16) :
    0≤3*(2*(i:ℝ)+1)/16 ∧ 3*(2*(i:ℝ)+1)/16≤6 := by
  have hiN : i≤15 := by omega
  have hiR : (i:ℝ)≤15 := by exact_mod_cast hiN
  constructor
  · positivity
  · linarith

lemma baseJet_bound (i j : ℕ) (hi : i<16) :
    ‖baseJet i j‖ ≤ 11*10^84 := by
  let c : ℝ := 3*(2*(i:ℝ)+1)/16
  have hc : 0≤c := (center_bounds i hi).1
  have hb : ∀ z ∈ sphere (c:ℂ) (11/10:ℝ), ‖base z‖≤11*10^84 := by
    intro z hz
    simpa [base,RHDirectOscillatory.kernel] using
      TaoFivePrimes.rh_moment_kernel_radius_11o10 0 c hc z (mem_sphere_iff_norm.mp hz).le
  have hcoeff := coefficient_bound base base_entire (c:ℂ) (11/10) (11*10^84)
    (by norm_num) hb j
  have hR : (1:ℝ)≤(11/10:ℝ)^j := one_le_pow₀ (by norm_num)
  have hcoeff' : ‖coefficient base (c:ℂ) j‖≤11*10^84 :=
    hcoeff.trans (div_le_self (by positivity) hR)
  have hp : ‖(3/16:ℂ)‖^j≤1 := pow_le_one₀ (norm_nonneg _) (by norm_num)
  unfold baseJet scaledCoefficient RHDirect132Rule.center
  change ‖coefficient base (c:ℂ) j * (3/16:ℂ)^j‖≤_
  rw [norm_mul,norm_pow]
  calc
    _ ≤ (11*10^84)*1 := mul_le_mul hcoeff' hp (pow_nonneg (norm_nonneg _) j) (by positivity)
    _ = 11*10^84 := by ring

lemma baseJet_error (i j : ℕ) (hi : i<16) (hj : j<184) :
    ‖baseJet i j-RHDirect132Rule.baseJet i j‖≤1/10^234 := by
  simpa [baseJet,base,scaledCoefficient,coefficient,RHDirect132Rule.center,
    RHDirect132Rule.baseJet,Complex.ofReal_div] using
      TaoFivePrimes.rh_direct_base_theta_jets i hi j hj

lemma stored_base_bound (i j : ℕ) (hi : i<16) (hj : j<184) :
    ‖RHDirect132Rule.baseJet i j‖≤2*10^85 := by
  have hb := baseJet_bound i j hi
  have he := baseJet_error i j hi hj
  have h := norm_add_le (RHDirect132Rule.baseJet i j-baseJet i j) (baseJet i j)
  rw [sub_add_cancel,norm_sub_rev] at h
  linarith

lemma phase_error (i : ℕ) (hi : i<16) :
    ‖phase (RHDirect132Rule.center i) -
      RHDirectPhase132.asComplex (RHDirectPhase132.panels i)‖≤1/10^194 := by
  simpa [phase,RHDirect132Rule.center,Complex.ofReal_mul,mul_assoc] using
    TaoFivePrimes.rh_direct_phase_132_panels i hi

lemma phase_unit (i : ℕ) : ‖phase (RHDirect132Rule.center i)‖=1 := by
  have hid : phase (RHDirect132Rule.center i) =
      Complex.exp (Complex.I*((66*(3*(2*(i:ℝ)+1)/16):ℝ):ℂ)) := by
    unfold phase RHDirect132Rule.center
    congr 1
    push_cast
    ring
  rw [hid]
  rw [Complex.norm_exp]
  simp only [Complex.mul_re,Complex.I_re,Complex.I_im,Complex.ofReal_im,zero_mul,
    one_mul,zero_sub,neg_zero,Real.exp_zero]

lemma factor_error (i j : ℕ) (hi : i<16) (hj : j<184) :
    ‖phase (RHDirect132Rule.center i)*baseJet i j -
      RHDirectPhase132.asComplex (RHDirectPhase132.panels i) *
        RHDirect132Rule.baseJet i j‖ ≤ 3/10^109 := by
  have hb := baseJet_error i j hi hj
  have hq := stored_base_bound i j hi hj
  have hp := phase_error i hi
  have hid : phase (RHDirect132Rule.center i)*baseJet i j -
      RHDirectPhase132.asComplex (RHDirectPhase132.panels i) * RHDirect132Rule.baseJet i j =
      phase (RHDirect132Rule.center i)*(baseJet i j-RHDirect132Rule.baseJet i j)+
      (phase (RHDirect132Rule.center i) -
        RHDirectPhase132.asComplex (RHDirectPhase132.panels i))*RHDirect132Rule.baseJet i j := by ring
  rw [hid]
  calc
    _ ≤ ‖phase (RHDirect132Rule.center i)*(baseJet i j-RHDirect132Rule.baseJet i j)‖ +
        ‖(phase (RHDirect132Rule.center i) -
          RHDirectPhase132.asComplex (RHDirectPhase132.panels i))*RHDirect132Rule.baseJet i j‖ :=
      norm_add_le _ _
    _ ≤ 1/10^234+(1/10^194)*(2*10^85) := by
      have h1 : ‖phase (RHDirect132Rule.center i)*(baseJet i j-RHDirect132Rule.baseJet i j)‖≤1/10^234 := by
        rw [norm_mul,phase_unit,one_mul]; exact hb
      have h2 : ‖(phase (RHDirect132Rule.center i) -
          RHDirectPhase132.asComplex (RHDirectPhase132.panels i))*RHDirect132Rule.baseJet i j‖ ≤
          (1/10^194)*(2*10^85) := by
        rw [norm_mul]
        exact mul_le_mul hp hq (norm_nonneg _) (by positivity)
      exact add_le_add h1 h2
    _ ≤ 3/10^109 := by norm_num

lemma exp_integer_bound (n : ℕ) : Real.exp n ≤ (3:ℝ)^n := by
  rw [show Real.exp n=(Real.exp 1)^n by
    simpa only [mul_one] using Real.exp_nat_mul (1:ℝ) n]
  exact pow_le_pow_left₀ (Real.exp_pos 1).le (le_of_lt (by linarith [Real.exp_one_lt_d9])) n

lemma phaseJet_bound (m : ℕ) : ‖RHDirect132Rule.phaseJet m‖≤2000000 := by
  have hn : ‖Complex.I*(66:ℂ)*(3/16:ℂ)‖=(99/8:ℝ) := by norm_num [norm_mul]
  unfold RHDirect132Rule.phaseJet
  rw [norm_div,norm_pow,Complex.norm_natCast,hn]
  calc
    _ ≤ Real.exp (99/8) := Real.pow_div_factorial_le_exp _ (by norm_num) _
    _ ≤ Real.exp 13 := Real.exp_le_exp.mpr (by norm_num)
    _ ≤ (3:ℝ)^13 := exp_integer_bound 13
    _ ≤ _ := by norm_num

lemma powerJet_bound (i k m : ℕ) (hi : i<16) :
    ‖RHDirect132Rule.powerJet i k m‖≤3000 := by
  unfold RHDirect132Rule.powerJet
  by_cases hmk : m≤k
  · rw [if_pos hmk,norm_div,norm_mul,norm_pow,norm_pow,norm_mul,
      Complex.norm_natCast,Complex.norm_natCast]
    have hc : ‖RHDirect132Rule.center i‖≤6 := by
      unfold RHDirect132Rule.center
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (center_bounds i hi).1]
      exact (center_bounds i hi).2
    have hh : ‖(3/16:ℂ)‖=(3/16:ℝ) := by norm_num
    rw [hh]
    have h1 := Real.pow_div_factorial_le_exp ‖RHDirect132Rule.center i‖
      (norm_nonneg _) (k-m)
    have h2 := Real.pow_div_factorial_le_exp (3/16:ℝ) (by norm_num) m
    calc
      _ = (‖RHDirect132Rule.center i‖^(k-m)/((k-m).factorial:ℝ))*
          ((3/16:ℝ)^m/(m.factorial:ℝ)) := by ring
      _ ≤ Real.exp ‖RHDirect132Rule.center i‖*Real.exp (3/16) := by
        exact mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le
      _ = Real.exp (‖RHDirect132Rule.center i‖+3/16) := by rw [Real.exp_add]
      _ ≤ Real.exp 7 := Real.exp_le_exp.mpr (by linarith)
      _ ≤ (3:ℝ)^7 := exp_integer_bound 7
      _ ≤ _ := by norm_num
  · simp [hmk]

lemma weight_bound (j : ℕ) : ‖RHDirect132Rule.weight j‖≤2 := by
  have hn : ‖(1:ℂ)-(-1:ℂ)^(j+1)‖≤2 := by
    have h := norm_sub_le (1:ℂ) ((-1:ℂ)^(j+1))
    simpa [norm_pow, show (1:ℝ)+1=2 by norm_num] using h
  have hd : (1:ℝ)≤‖((j:ℂ)+1)‖ := by
    rw [show (j:ℂ)+1=((j+1:ℕ):ℂ) by push_cast; rfl,Complex.norm_natCast]
    exact_mod_cast Nat.succ_pos j
  unfold RHDirect132Rule.weight
  rw [norm_div]
  exact (div_le_div_of_nonneg_right hn (norm_nonneg _)).trans (div_le_self (by norm_num) hd)

lemma sum_bound (N : ℕ) (hN : N≤184) (a : ℝ) (ha : 0≤a)
    (f : ℕ → ℂ) (hf : ∀ n<N, ‖f n‖≤a) :
    ‖∑ n ∈ range N, f n‖ ≤ 184*a := by
  calc
    _ ≤ ∑ n ∈ range N, ‖f n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ range N, a := sum_le_sum (fun n hn => hf n (mem_range.mp hn))
    _ = (N:ℝ)*a := by simp
    _ ≤ 184*a := by
      gcongr
      exact_mod_cast hN

lemma panel_difference (i k : ℕ) :
    exactPanel i k-RHDirect132Rule.panel i k =
      (3/16:ℂ) * ∑ j ∈ range 184, RHDirect132Rule.weight j *
        ∑ m ∈ range (j+1), RHDirect132Rule.powerJet i k m *
          ∑ l ∈ range (j-m+1), RHDirect132Rule.phaseJet l *
            (phase (RHDirect132Rule.center i)*baseJet i (j-m-l) -
              RHDirectPhase132.asComplex (RHDirectPhase132.panels i) *
                RHDirect132Rule.baseJet i (j-m-l)) := by
  unfold exactPanel RHDirect132Rule.panel
  rw [←mul_sub,←sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro j hj
  rw [←mul_sub,←sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro m hm
  rw [←mul_sub,←sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro l hl
  rw [←mul_sub]

lemma inner_difference_bound (i k j m : ℕ) (hi : i<16) (hj : j<184) (hm : m<j+1) :
    ‖RHDirect132Rule.powerJet i k m *
      ∑ l ∈ range (j-m+1), RHDirect132Rule.phaseJet l *
        (phase (RHDirect132Rule.center i)*baseJet i (j-m-l) -
          RHDirectPhase132.asComplex (RHDirectPhase132.panels i) *
            RHDirect132Rule.baseJet i (j-m-l))‖ ≤ 184/10^97 := by
  rw [mul_sum]
  have hN : j-m+1≤184 := by omega
  have hh := sum_bound (j-m+1) hN (1/10^97) (by positivity) (fun l =>
    RHDirect132Rule.powerJet i k m * (RHDirect132Rule.phaseJet l *
      (phase (RHDirect132Rule.center i)*baseJet i (j-m-l) -
        RHDirectPhase132.asComplex (RHDirectPhase132.panels i) *
          RHDirect132Rule.baseJet i (j-m-l)))) (by
    intro l hl
    have hindex : j-m-l<184 := by omega
    have hp := powerJet_bound i k m hi
    have hphase := phaseJet_bound l
    have he := factor_error i (j-m-l) hi hindex
    simp only [norm_mul]
    have he' := mul_le_mul hphase he (norm_nonneg _) (by norm_num : (0:ℝ)≤2000000)
    have he'' := mul_le_mul hp he'
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num : (0:ℝ)≤3000)
    exact he''.trans (by norm_num))
  exact hh.trans_eq (by ring)

lemma middle_difference_bound (i k j : ℕ) (hi : i<16) (hj : j<184) :
    ‖∑ m ∈ range (j+1), RHDirect132Rule.powerJet i k m *
      ∑ l ∈ range (j-m+1), RHDirect132Rule.phaseJet l *
        (phase (RHDirect132Rule.center i)*baseJet i (j-m-l) -
          RHDirectPhase132.asComplex (RHDirectPhase132.panels i) *
            RHDirect132Rule.baseJet i (j-m-l))‖ ≤ (184*184)/10^97 := by
  have hN : j+1≤184 := by omega
  have hh := sum_bound (j+1) hN (184/10^97) (by positivity) (fun m =>
    RHDirect132Rule.powerJet i k m *
      ∑ l ∈ range (j-m+1), RHDirect132Rule.phaseJet l *
        (phase (RHDirect132Rule.center i)*baseJet i (j-m-l) -
          RHDirectPhase132.asComplex (RHDirectPhase132.panels i) *
            RHDirect132Rule.baseJet i (j-m-l)))
    (fun m hm => inner_difference_bound i k j m hi hj hm)
  exact hh.trans_eq (by ring)

lemma panel_error (i k : ℕ) (hi : i<16) :
    ‖exactPanel i k-RHDirect132Rule.panel i k‖≤1/10^88 := by
  rw [panel_difference,norm_mul]
  have hsum := sum_bound 184 (by norm_num) (2*(184*184)/10^97) (by positivity)
    (fun j => RHDirect132Rule.weight j *
      ∑ m ∈ range (j+1), RHDirect132Rule.powerJet i k m *
        ∑ l ∈ range (j-m+1), RHDirect132Rule.phaseJet l *
          (phase (RHDirect132Rule.center i)*baseJet i (j-m-l) -
            RHDirectPhase132.asComplex (RHDirectPhase132.panels i) *
              RHDirect132Rule.baseJet i (j-m-l))) (by
      intro j hj
      rw [norm_mul]
      have hw := weight_bound j
      have hm := middle_difference_bound i k j hi hj
      calc
        _ ≤ 2*((184*184)/10^97) :=
          mul_le_mul hw hm (norm_nonneg _) (by norm_num)
        _ = _ := by ring)
  have hh : ‖(3/16:ℂ)‖≤1 := by norm_num
  calc
    _ ≤ 1*(184*(2*(184*184)/10^97)) :=
      mul_le_mul hh hsum (norm_nonneg _) (by norm_num)
    _ ≤ 1/10^88 := by norm_num

lemma rule_error (k : ℕ) :
    ‖RHDirectOscillatory.panelSum 66 k-RHDirect132Rule.rule k‖≤1/10^85 := by
  have he : RHDirectOscillatory.panelSum 66 k = ∑ i ∈ range 16, exactPanel i k := by
    unfold RHDirectOscillatory.panelSum
    exact sum_congr rfl (fun i _ => exact_panel i k)
  rw [he,RHDirect132Rule.rule,←sum_sub_distrib]
  have hh := sum_bound 16 (by norm_num) (1/10^88) (by positivity)
    (fun i => exactPanel i k-RHDirect132Rule.panel i k)
    (fun i hi => panel_error i k hi)
  exact hh.trans (by norm_num)

end Direct132RuleProof

theorem solution (k : ℕ) :
    ‖RHDirectOscillatory.rawIntegral 66 k-RHDirect132Rule.rule k‖≤18/10^82 := by
  have ha := TaoFivePrimes.rh_direct_oscillatory_quadrature 66 (by norm_num) k
  have hb := Direct132RuleProof.rule_error k
  have hid : RHDirectOscillatory.rawIntegral 66 k-RHDirect132Rule.rule k =
      (RHDirectOscillatory.rawIntegral 66 k-RHDirectOscillatory.panelSum 66 k) +
      (RHDirectOscillatory.panelSum 66 k-RHDirect132Rule.rule k) := by ring
  rw [hid]
  exact (norm_add_le _ _).trans (by linarith)
