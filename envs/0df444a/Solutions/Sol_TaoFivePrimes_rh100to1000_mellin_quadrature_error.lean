-- Prove2me | solution 1 for TaoFivePrimes.rh100to1000_mellin_quadrature_error
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-14T04:38:07.530987+00:00
-- url     : https://prove2.me/submissions/1cbc41a6-6c87-4142-bc00-88a00a53d35f

import Definitions.Def_TaoFivePrimes_RH100To1000MellinModel
import Mathlib
import Definitions.Def_TaoFivePrimes_RH14To100MomentModel
import Definitions.Def_TaoFivePrimes_RH14To100CheckedMomentNCPanels0
import Definitions.Def_TaoFivePrimes_RH14To100CheckedMomentNCPanels1
import Definitions.Def_TaoFivePrimes_RH14To100CheckedMomentNCPanels2
import Definitions.Def_TaoFivePrimes_RH14To100CheckedMomentNCPanels3
import Definitions.Def_TaoFivePrimes_RH14To100CheckedMomentNCRounding
import Theorems.Thm_TaoFivePrimes_rh14to100_theta_checks
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
namespace RH1000MellinProof
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

section Height100Module4

open Complex Finset
namespace CertifiedExponentialJets
open _root_.CertifiedExponentialJets
open CertifiedTaylorQuadrature CertifiedMomentConvolution
open _root_.CertifiedTaylorQuadrature _root_.CertifiedMomentConvolution

lemma coefficient_deriv (f : ℂ → ℂ) (c : ℂ) (n : ℕ) :
    coefficient (deriv f) c n=(n+1:ℂ)*coefficient f c (n+1) := by
  unfold coefficient
  rw [← iteratedDeriv_succ',Nat.factorial_succ]
  push_cast
  have h0 : (n.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  have h1 : (n+1:ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp

lemma exp_coefficient_recurrence (g : ℂ → ℂ) (hg : Differentiable ℂ g) (c : ℂ) (n : ℕ) :
    (n+1:ℂ)*coefficient (fun z => Complex.exp (g z)) c (n+1)=
      ∑ k ∈ range (n+1), (k+1:ℂ)*coefficient g c (k+1)*
        coefficient (fun z => Complex.exp (g z)) c (n-k) := by
  have hf : Differentiable ℂ (fun z => Complex.exp (g z)) := by fun_prop
  have he : deriv (fun z => Complex.exp (g z)) =
      (fun z => deriv g z*Complex.exp (g z)) := by
    funext z
    exact ((hg z).hasDerivAt.cexp).deriv.trans (mul_comm _ _)
  rw [← coefficient_deriv,he,coefficient_mul _ _ hg.deriv hf]
  simp_rw [coefficient_deriv]

lemma scaled_exp_coefficient_recurrence (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (c h : ℂ) (n : ℕ) :
    (n+1:ℂ)*scaledCoefficient (fun z => Complex.exp (g z)) c h (n+1)=
      ∑ k ∈ range (n+1), (k+1:ℂ)*scaledCoefficient g c h (k+1)*
        scaledCoefficient (fun z => Complex.exp (g z)) c h (n-k) := by
  unfold scaledCoefficient
  rw [← mul_assoc,exp_coefficient_recurrence g hg c n,sum_mul]
  apply sum_congr rfl
  intro k hk
  have he : n+1=(k+1)+(n-k) := by have := mem_range.mp hk; omega
  conv_lhs => rw [he,pow_add]
  ring

lemma product_error (a b x y : ℂ) (r s : ℝ)
    (ha : ‖a-x‖≤ r) (hb : ‖b-y‖≤ s) :
    ‖a*b-x*y‖≤ ‖x‖*s+r*‖y‖+r*s := by
  have hr : 0≤ r := (norm_nonneg _).trans ha
  have hs : 0≤ s := (norm_nonneg _).trans hb
  have he : a*b-x*y=x*(b-y)+(a-x)*y+(a-x)*(b-y) := by ring
  rw [he]
  calc
    _ ≤  ‖x*(b-y)+(a-x)*y‖+‖(a-x)*(b-y)‖ := norm_add_le _ _
    _ ≤  (‖x*(b-y)‖+‖(a-x)*y‖)+‖(a-x)*(b-y)‖ := by gcongr; exact norm_add_le _ _
    _ = (‖x‖*‖b-y‖+‖a-x‖*‖y‖)+‖a-x‖*‖b-y‖ := by simp only [norm_mul]
    _ ≤  _ := by gcongr

noncomputable def residual (G F : ℕ → ℂ) (n : ℕ) : ℂ :=
  (n+1:ℂ)*F (n+1)-∑ k ∈ range (n+1), (k+1:ℂ)*G (k+1)*F (n-k)

noncomputable def errorSum (G F : ℕ → ℂ) (r s : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range (n+1), (k+1:ℝ)*
    (‖G (k+1)‖*s (n-k)+r (k+1)*‖F (n-k)‖+r (k+1)*s (n-k))

theorem enclosure_of_recurrence (A F G C : ℕ → ℂ) (r s : ℕ → ℝ) (N : ℕ)
    (hrec : ∀ n : ℕ, (n+1:ℂ)*F (n+1)=
      ∑ k ∈ range (n+1), (k+1:ℂ)*A (k+1)*F (n-k))
    (hG : ∀ j< N, ‖A j-G j‖≤ r j)
    (h0 : ‖F 0-C 0‖≤ s 0)
    (hcheck : ∀ n, n+1< N → ‖residual G C n‖+errorSum G C r s n≤ (n+1:ℝ)*s (n+1)) :
    ∀ n< N, ‖F n-C n‖≤ s n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    cases n with
    | zero => exact h0
    | succ n =>
      have hp (k : ℕ) (hk : k∈range (n+1)) :
          ‖A (k+1)*F (n-k)-G (k+1)*C (n-k)‖ ≤ 
            ‖G (k+1)‖*s (n-k)+r (k+1)*‖C (n-k)‖+r (k+1)*s (n-k) := by
        have hk' := mem_range.mp hk
        exact product_error _ _ _ _ _ _ (hG (k+1) (by omega))
          (ih (n-k) (by omega) (by omega))
      have he : (n+1:ℂ)*(F (n+1)-C (n+1)) =
          (∑ k ∈ range (n+1), (k+1:ℂ)*(A (k+1)*F (n-k)-G (k+1)*C (n-k))) - residual G C n := by
        unfold residual
        simp_rw [mul_sub,sum_sub_distrib]
        rw [hrec n]
        simp only [mul_assoc]
        ring
      have hm : (n+1:ℝ)*‖F (n+1)-C (n+1)‖≤ (n+1:ℝ)*s (n+1) := by
        calc
          _ = ‖(n+1:ℂ)*(F (n+1)-C (n+1))‖ := by rw [norm_mul]; norm_cast
          _ ≤  ‖∑ k ∈ range (n+1), (k+1:ℂ)*(A (k+1)*F (n-k)-G (k+1)*C (n-k))‖+
              ‖residual G C n‖ := by rw [he]; exact norm_sub_le _ _
          _ ≤  (∑ k ∈ range (n+1), ‖(k+1:ℂ)*(A (k+1)*F (n-k)-G (k+1)*C (n-k))‖)+
              ‖residual G C n‖ := by gcongr; exact norm_sum_le _ _
          _ ≤  errorSum G C r s n+‖residual G C n‖ := by
            gcongr
            unfold errorSum
            apply sum_le_sum
            intro k hk
            rw [norm_mul]
            have hc : ‖(k+1:ℂ)‖=(k+1:ℝ) := by norm_cast
            rw [hc]
            exact mul_le_mul_of_nonneg_left (hp k hk) (by positivity)
          _ ≤  _ := by linarith [hcheck n hn]
      have hpos : (0:ℝ)< n+1 := by positivity
      nlinarith

end CertifiedExponentialJets

end Height100Module4

section Height100Module5

open Complex Finset
namespace CertifiedIntegerExponentialJets
open _root_.CertifiedIntegerExponentialJets
open CertifiedMomentConvolution CertifiedExponentialJets
open _root_.CertifiedMomentConvolution _root_.CertifiedExponentialJets

noncomputable def integerResidual (D : ℕ) (G C : ℕ → ℤ) (n : ℕ) : ℤ :=
  (n+1:ℤ)*C (n+1)*D-∑ k ∈ range (n+1), (k+1:ℤ)*G (k+1)*C (n-k)

noncomputable def integerErrorSum (G C : ℕ → ℤ) (r s : ℕ → ℕ) (n : ℕ) : ℤ :=
  ∑ k ∈ range (n+1), (k+1:ℤ)*
    (|G (k+1)| *(s (n-k):ℤ)+(r (k+1):ℤ) * |C (n-k)|+(r (k+1):ℤ)*s (n-k))

noncomputable def fixedCenter (D : ℕ) (G : ℕ → ℤ) (n : ℕ) : ℂ := (G n:ℂ)/D
noncomputable def fixedRadius (D : ℕ) (r : ℕ → ℕ) (n : ℕ) : ℝ := (r n:ℝ)/D

lemma residual_scale (D : ℕ) (hD : 0< D) (G C : ℕ → ℤ) (n : ℕ) :
    CertifiedExponentialJets.residual (fixedCenter D G) (fixedCenter D C) n =
      (integerResidual D G C n:ℂ)/(D:ℂ)^2 := by
  have hd : (D:ℂ)≠0 := by exact_mod_cast Nat.ne_of_gt hD
  have hs : (∑ k ∈ range (n+1), (k+1:ℂ)*((G (k+1):ℂ)/D)*((C (n-k):ℂ)/D)) =
      (∑ k ∈ range (n+1), (k+1:ℂ)*(G (k+1):ℂ)*(C (n-k):ℂ))/(D:ℂ)^2 := by
    rw [sum_div]
    apply sum_congr rfl
    intro k _
    field_simp
  unfold CertifiedExponentialJets.residual fixedCenter integerResidual
  push_cast
  rw [hs]
  field_simp

lemma errorSum_scale (D : ℕ) (hD : 0< D) (G C : ℕ → ℤ) (r s : ℕ → ℕ) (n : ℕ) :
    errorSum (fixedCenter D G) (fixedCenter D C) (fixedRadius D r) (fixedRadius D s) n =
      (integerErrorSum G C r s n:ℝ)/(D:ℝ)^2 := by
  have hd : (D:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hD
  unfold errorSum fixedCenter fixedRadius integerErrorSum
  simp only [norm_div,Complex.norm_intCast,Complex.norm_natCast,
    Int.cast_sum,Int.cast_mul,Int.cast_add,Int.cast_natCast,Int.cast_one,Int.cast_abs]
  rw [sum_div]
  apply sum_congr rfl
  intro k _
  field_simp

lemma integer_check_sound (D : ℕ) (hD : 0< D) (G C : ℕ → ℤ) (r s : ℕ → ℕ) (n : ℕ)
    (hc : |integerResidual D G C n|+integerErrorSum G C r s n≤ (n+1:ℤ)*s (n+1)*D) :
    ‖CertifiedExponentialJets.residual (fixedCenter D G) (fixedCenter D C) n‖+
      errorSum (fixedCenter D G) (fixedCenter D C) (fixedRadius D r) (fixedRadius D s) n ≤ 
      (n+1:ℝ)*fixedRadius D s (n+1) := by
  have hd : (D:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hD
  have hnum : |(integerResidual D G C n:ℝ)|+(integerErrorSum G C r s n:ℝ) ≤ 
      (n+1:ℝ)*(s (n+1):ℝ)*D := by exact_mod_cast hc
  rw [residual_scale D hD,errorSum_scale D hD,norm_div,norm_pow,
    Complex.norm_intCast,Complex.norm_natCast]
  calc
    _ = (|(integerResidual D G C n:ℝ)|+(integerErrorSum G C r s n:ℝ))/(D:ℝ)^2 := by ring
    _ ≤  ((n+1:ℝ)*(s (n+1):ℝ)*D)/(D:ℝ)^2 :=
      div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _ = _ := by unfold fixedRadius; field_simp

theorem fixed_enclosure_of_recurrence (A F : ℕ → ℂ)
    (D : ℕ) (hD : 0< D) (G C : ℕ → ℤ) (r s : ℕ → ℕ) (N : ℕ)
    (hrec : ∀ n : ℕ, (n+1:ℂ)*F (n+1)=
      ∑ k ∈ range (n+1), (k+1:ℂ)*A (k+1)*F (n-k))
    (hG : ∀ j< N, ‖A j-fixedCenter D G j‖≤ fixedRadius D r j)
    (h0 : ‖F 0-fixedCenter D C 0‖≤ fixedRadius D s 0)
    (hcheck : ∀ n : ℕ, n+1< N →
      |integerResidual D G C n|+integerErrorSum G C r s n≤ (n+1:ℤ)*s (n+1)*D) :
    ∀ n< N, ‖F n-fixedCenter D C n‖≤ fixedRadius D s n := by
  apply enclosure_of_recurrence A F (fixedCenter D G) (fixedCenter D C)
    (fixedRadius D r) (fixedRadius D s) N hrec hG h0
  intro n hn
  exact integer_check_sound D hD G C r s n (hcheck n hn)

end CertifiedIntegerExponentialJets

end Height100Module5

section Height100Module6

set_option autoImplicit false
open Finset
open scoped BigOperators
namespace CertifiedSignedODEConvolution
open _root_.CertifiedSignedODEConvolution
open CertifiedIntegerExponentialJets
open _root_.CertifiedIntegerExponentialJets

noncomputable def conv (a b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ range (n+1), a k*b (n-k)

noncomputable def absDerivative (G : ℕ → ℤ) (k : ℕ) : ℕ := (k+1)*(G (k+1)).natAbs
noncomputable def radiusDerivative (r : ℕ → ℕ) (k : ℕ) : ℕ := (k+1)*r (k+1)

noncomputable def positive (C : ℕ → ℤ) (k : ℕ) : ℕ := (C k).toNat
noncomputable def negative (C : ℕ → ℤ) (k : ℕ) : ℕ := (-C k).toNat

lemma signed_product (G C : ℕ → ℤ) (n : ℕ)
    (hG : ∀ k, k≤ n → G (k+1)≤ 0) :
    (∑ k ∈ range (n+1), (k+1:ℤ)*G (k+1)*C (n-k)) =
      -(conv (absDerivative G) (positive C) n:ℤ) +
        (conv (absDerivative G) (negative C) n:ℤ) := by
  unfold conv absDerivative positive negative
  push_cast
  rw [←sum_neg_distrib,←sum_add_distrib]
  apply sum_congr rfl
  intro k hk
  have hkg := hG k (by simpa using mem_range.mp hk)
  calc
    _ = (k+1:ℤ)*G (k+1)*((C (n-k)).toNat-((-C (n-k)).toNat:ℤ)) := by
      rw [Int.toNat_sub_toNat_neg]
    _ = _ := by rw [abs_of_nonpos hkg]; ring

lemma error_product (G C : ℕ → ℤ) (r s : ℕ → ℕ) (n : ℕ) :
    integerErrorSum G C r s n =
      (conv (absDerivative G) s n:ℤ) +
        (conv (radiusDerivative r) (fun j => (C j).natAbs+s j) n:ℤ) := by
  unfold integerErrorSum conv absDerivative radiusDerivative
  push_cast
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro k hk
  ring

lemma residual_product (D : ℕ) (G C : ℕ → ℤ) (n : ℕ)
    (hG : ∀ k, k≤ n → G (k+1)≤ 0) :
    integerResidual D G C n = (n+1:ℤ)*C (n+1)*D +
      (conv (absDerivative G) (positive C) n:ℤ) -
        (conv (absDerivative G) (negative C) n:ℤ) := by
  rw [integerResidual,signed_product G C n hG]
  ring

theorem residual_check_of_convolutions (D : ℕ) (G C : ℕ → ℤ) (r s : ℕ → ℕ)
    (n cp cm es er : ℕ) (hG : ∀ k, k≤ n → G (k+1)≤ 0)
    (hp : cp=conv (absDerivative G) (positive C) n)
    (hm : cm=conv (absDerivative G) (negative C) n)
    (hes : es=conv (absDerivative G) s n)
    (her : er=conv (radiusDerivative r) (fun j => (C j).natAbs+s j) n)
    (hc : (((n+1:ℤ)*C (n+1)*D+(cp:ℤ)-(cm:ℤ)).natAbs+es+er)≤ (n+1)*s (n+1)*D) :
    |integerResidual D G C n|+integerErrorSum G C r s n≤ (n+1:ℤ)*s (n+1)*D := by
  rw [residual_product D G C n hG,error_product,←hp,←hm,←hes,←her]
  have hh : (((((n+1:ℤ)*C (n+1)*D+(cp:ℤ)-(cm:ℤ)).natAbs+es+er):ℕ):ℤ) ≤ 
      (((n+1)*s (n+1)*D:ℕ):ℤ) := by exact_mod_cast hc
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Int.natCast_natAbs,add_assoc] using hh

noncomputable def digit (bits p k : ℕ) : ℕ := (p >>> (bits*k)) % (2^bits)

end CertifiedSignedODEConvolution

end Height100Module6

section Height100Module7

set_option autoImplicit false
namespace CertifiedListODEVectors
open _root_.CertifiedListODEVectors
open CertifiedSignedODEConvolution
open _root_.CertifiedSignedODEConvolution
open Finset
open scoped BigOperators

lemma getD_mapIdx_zero {α β : Type*} [Zero α] [Zero β]
    (l : List α) (f : ℕ → α → β) (hf : ∀ j,f j 0=0) (j : ℕ) :
    (l.mapIdx f).getD j 0=f j (l.getD j 0) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_mapIdx]
  cases l[j]? <;> simp [hf]

lemma getD_tail {α : Type*} (l : List α) (j : ℕ) (d : α) :
    l.tail.getD j d=l.getD (j+1) d := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_tail]

lemma absDerivativeList_getD (g : List ℤ) (j : ℕ) :
    (absDerivativeList g).getD j 0=(j+1)*(g.getD (j+1) 0).natAbs := by
  rw [absDerivativeList,←List.mapIdx_eq_zipIdx_map (l := g.tail)
    (f := fun k (x : ℤ) => (k+1)*x.natAbs),
    getD_mapIdx_zero _ _ (by intro k; simp),getD_tail]

lemma radiusDerivativeList_getD (r : List ℕ) (j : ℕ) :
    (radiusDerivativeList r).getD j 0=(j+1)*r.getD (j+1) 0 := by
  rw [radiusDerivativeList,←List.mapIdx_eq_zipIdx_map (l := r.tail)
    (f := fun k (x : ℕ) => (k+1)*x),
    getD_mapIdx_zero _ _ (by intro k; simp),getD_tail]

lemma positiveList_getD (f : List ℤ) (j : ℕ) :
    (positiveList f).getD j 0=(f.getD j 0).toNat := by
  exact List.getD_map f 0 Int.toNat

lemma negativeList_getD (f : List ℤ) (j : ℕ) :
    (negativeList f).getD j 0=(-f.getD j 0).toNat := by
  exact List.getD_map f 0 (fun x : ℤ => (-x).toNat)

lemma radiusFactorList_getD (f : List ℤ) (s : List ℕ) (h : f.length=s.length) (j : ℕ) :
    (radiusFactorList f s).getD j 0=(f.getD j 0).natAbs+s.getD j 0 := by
  induction f generalizing s j with
  | nil => cases s <;> simp_all [radiusFactorList]
  | cons x xs ih =>
    cases s with
    | nil => simp at h
    | cons y ys =>
      cases j with
      | zero => rfl
      | succ j => exact ih ys (by simpa using h) j

lemma list_all_nonpos (g : List ℤ) (h : g.all (fun x => decide (x≤ 0))=true) (j : ℕ) :
    g.getD j 0≤ 0 := by
  induction g generalizing j with
  | nil => simp
  | cons x xs ih =>
    simp only [List.all_cons,Bool.and_eq_true,decide_eq_true_eq] at h
    cases j with
    | zero => exact h.1
    | succ j => exact ih h.2 j

lemma digit_lists (bits : ℕ) (xs ys : List ℕ) (a b : ℕ → ℕ) (n : ℕ)
    (hx : ∀ k≤ n,xs.getD k 0=a k) (hy : ∀ k≤ n,ys.getD k 0=b k)
    (hc : xs.sum*ys.sum<2^bits) :
    digit bits (CertifiedPackedConvolution.encode bits xs*CertifiedPackedConvolution.encode bits ys) n=
      conv a b n := by
  rw [digit,CertifiedPackedConvolution.shiftRight_product_digit bits xs ys hc]
  apply sum_congr rfl
  intro k hk
  have hk' := mem_range.mp hk
  rw [hx k (by omega),hy (n-k) (by omega)]

lemma digit_truncate (bits p N k : ℕ) (hk : k< N) :
    digit bits (p % 2^(bits*N)) k = digit bits p k := by
  unfold digit
  rw [Nat.shiftRight_eq_div_pow,Nat.shiftRight_eq_div_pow,
    show bits*N=bits*k+bits*(N-k) by
      rw [←Nat.mul_add]; congr 1; omega,pow_add,
    Nat.mod_mul_right_div_self]
  apply Nat.mod_mod_of_dvd
  have he : bits*(N-k)=bits+bits*(N-k-1) := by
    calc
      _ = bits*(1+(N-k-1)) := by congr 1; omega
      _ = _ := by ring
  rw [he,pow_add]
  exact Nat.dvd_mul_right _ _

end CertifiedListODEVectors

end Height100Module7

section Height100Module8

set_option autoImplicit false
open Finset
namespace CertifiedPackedHorner
open _root_.CertifiedPackedHorner
open CertifiedPackedConvolution
open _root_.CertifiedPackedConvolution

end CertifiedPackedHorner

namespace CertifiedPackedHorner
open _root_.CertifiedPackedHorner

end CertifiedPackedHorner

end Height100Module8

section Height100Module9

open Complex MeasureTheory Set HurwitzZeta Real
open scoped Real

namespace ZetaSix
open _root_.ZetaSix

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
open _root_.TaoZetaBounds

lemma F_nat_zero_shift (a : ℝ) {t : ℝ} (ht : 0 < t) :
    F_nat 0 a t = exp (-π * a ^ 2 * t) + F_nat 0 (a + 1) t := by
  rw [F_nat, (summable_f_nat 0 a ht).tsum_eq_zero_add]
  simp only [f_nat, Nat.cast_zero, zero_add, pow_zero, one_mul]
  congr 1
  unfold F_nat
  apply tsum_congr
  intro n
  simp only [f_nat, pow_zero, one_mul, Nat.cast_add, Nat.cast_one]
  congr 2
  ring

end TaoZetaBounds

end Height100Module10

section Height100Module11

open Real MeasureTheory Set Filter
open scoped Topology

namespace TaoZetaBounds
open _root_.TaoZetaBounds

lemma exp_neg_nat_pi_le (n : ℕ) : exp (-(n : ℝ) * π) ≤  (1 / 23 : ℝ)^n := by
  have he : -(n : ℝ) * π = n * (-π) := by ring
  rw [he, exp_nat_mul]
  exact pow_le_pow_left₀ (exp_nonneg _) ZetaSix.exp_neg_pi_le_23 n

end TaoZetaBounds

end Height100Module11

section Height100Module12

open Real MeasureTheory Set Filter Finset HurwitzZeta HurwitzKernelBounds

namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature
open TaoZetaBounds
open _root_.TaoZetaBounds

lemma polynomial_exp_majorant_general (m : ℕ) (A c t : ℝ) (hA : 0 < A) (ht : 0 < t) :
    t ^ m * exp (-c * t) ≤ 
      (A ^ m * exp (-m)) * exp (-(c - m / A) * t) := by
  have hl := log_le_sub_one_of_pos (div_pos ht hA)
  rw [log_div ht.ne' hA.ne'] at hl
  have hm := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg m : (0:ℝ)≤ m)
  have hle : (m:ℝ) * log t - c * t ≤  m * log A - m - (c - m / A) * t := by
    simp only [div_eq_mul_inv] at hm ⊢
    nlinarith
  have et : exp ((m:ℝ) * log t) = t ^ m := by
    rw [exp_nat_mul, exp_log ht]
  have ea : exp ((m:ℝ) * log A) = A ^ m := by
    rw [exp_nat_mul, exp_log hA]
  calc
    t ^ m * exp (-c * t) = exp ((m:ℝ) * log t - c * t) := by
      rw [sub_eq_add_neg, exp_add, et]; congr 1; ring
    _ ≤  exp (m * log A - m - (c - m / A) * t) := exp_le_exp.mpr hle
    _ = (A ^ m * exp (-m)) * exp (-(c - m / A) * t) := by
      rw [sub_eq_add_neg, exp_add, sub_eq_add_neg, exp_add, ea]
      congr 1
      ring

lemma polynomial_exp_tail_general (m : ℕ) (A c : ℝ) (hA : 0 < A) (hd : 0 < c - m / A) :
    IntegrableOn (fun t : ℝ => t ^ m * exp (-c * t)) (Ioi A) ∧
    (∫ t in Ioi A, t ^ m * exp (-c * t)) ≤ 
      A ^ m * exp (-c * A) / (c - m / A) := by
  let d := c - m / A
  have hd0 : 0 < d := hd
  have hg : IntegrableOn
      (fun t : ℝ => (A ^ m * exp (-m)) * exp (-d * t)) (Ioi A) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hd0) A).const_mul _
  have hi : IntegrableOn (fun t : ℝ => t ^ m * exp (-c * t)) (Ioi A) := by
    apply hg.mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0< t := hA.trans ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact polynomial_exp_majorant_general m A c t hA (hA.trans ht)
  refine ⟨hi, ?_⟩
  have hb := integral_mono_ae hi hg (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact polynomial_exp_majorant_general m A c t hA (hA.trans ht))
  refine hb.trans_eq ?_
  rw [integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr hd0)]
  have he : -(m:ℝ) + -d * A = -c * A := by dsimp [d]; field_simp; ring
  calc
    A ^ m * exp (-(m:ℝ)) * (-exp (-d * A) / -d) =
        A ^ m * (exp (-m) * exp (-d * A)) / d := by ring
    _ = A ^ m * exp (-c * A) / d := by rw [← exp_add, he]

lemma kernel_finite_remainder_eq (N : ℕ) {t : ℝ} (ht : 0< t) :
    evenKernel 0 t-1-2*(∑ n ∈ range N, exp (-π*(n+1:ℝ)^2*t)) =
      2*F_nat 0 (N+1) t := by
  induction N with
  | zero =>
    have hF : F_int 0 0 t = F_nat 0 0 t + F_nat 0 1 t := by
      simpa only [QuotientAddGroup.mk_zero, sub_zero] using
        F_int_eq_of_mem_Icc 0 (by simp : (0:ℝ) ∈ Set.Icc 0 1) ht
    rw [ZetaSix.evenKernel_zero_eq_F_int ht,hF,F_nat_zero_shift 0 ht]
    simp
    ring
  | succ N ih =>
    rw [sum_range_succ]
    calc
      _ = (evenKernel 0 t-1-2*(∑ n ∈ range N, exp (-π*(n+1:ℝ)^2*t))) -
          2*exp (-π*(N+1:ℝ)^2*t) := by ring
      _ = 2*F_nat 0 (N+1) t - 2*exp (-π*(N+1:ℝ)^2*t) := by rw [ih]
      _ = _ := by rw [F_nat_zero_shift (N+1) ht]; push_cast; ring

lemma kernel_finite_remainder_bound (N : ℕ) {t : ℝ} (ht : 1≤ t) :
    |evenKernel 0 t-1-2*(∑ n ∈ range N, exp (-π*(n+1:ℝ)^2*t))| ≤ 
      (21/10:ℝ)*exp (-π*(N+1:ℝ)^2*t) := by
  rw [kernel_finite_remainder_eq N (by linarith), abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
  have hb := F_nat_zero_le (a := (N+1:ℝ)) (by positivity) (by linarith : 0< t)
  rw [Real.norm_eq_abs] at hb
  have he : exp (-π*t)≤ 1/23 :=
    (exp_le_exp.mpr (by nlinarith [pi_pos])).trans ZetaSix.exp_neg_pi_le_23
  have hd : 0<1-exp (-π*t) := by linarith
  calc
    2*|F_nat 0 (N+1) t| ≤  2*(exp (-π*(N+1:ℝ)^2*t)/(1-exp (-π*t))) := by gcongr
    _ ≤  _ := by
      rw [← mul_div_assoc, div_le_iff₀ hd]
      nlinarith [exp_pos (-π*(N+1:ℝ)^2*t)]

lemma theta_twenty_moment_tail :
    (21/10:ℝ)*(∫ t in Ioi (1:ℝ), t^64*exp (-441*π*t)) ≤  1/10^370 := by
  have hb := (polynomial_exp_tail_general 64 1 (441*π) (by norm_num)
    (by nlinarith [pi_gt_three])).2
  have hn : exp (-441*π)≤ (1/23:ℝ)^441 := by simpa using exp_neg_nat_pi_le 441
  calc
    _ ≤  (21/10:ℝ)*(exp (-441*π)/(441*π-64)) := by simpa using mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤ 21/10)
    _ ≤  (21/10:ℝ)*((1/23:ℝ)^441/1259) := by gcongr; nlinarith [pi_gt_three]
    _ ≤  1/10^370 := by norm_num

lemma large_moment_tail :
    (21/10:ℝ)*(∫ t in Ioi (400:ℝ), t^64*exp (-π*t)) ≤  1/10^370 := by
  have hb := (polynomial_exp_tail_general 64 400 π (by norm_num)
    (by nlinarith [pi_gt_three])).2
  norm_num only [Nat.cast_ofNat] at hb
  have hn : exp (-π*400)≤ (1/23:ℝ)^(400:ℕ) := by
    rw [show -π*400=-(400:ℝ)*π by ring]
    exact exp_neg_nat_pi_le 400
  calc
    _ ≤  (21/10:ℝ)*((400:ℝ)^(64:ℕ)*exp (-π*400)/(π-64/400)) := by
      have hh := mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤ 21/10)
      convert! hh using 1
      norm_num
    _ ≤  (21/10:ℝ)*((400:ℝ)^(64:ℕ)*(1/23:ℝ)^(400:ℕ)/(71/25)) := by gcongr; nlinarith [pi_gt_three]
    _ ≤  1/10^370 := by
      rw [show (400:ℕ)=200+200 by rfl, pow_add]
      norm_num

end CertifiedZetaQuadrature

end Height100Module12

section Height100Module13

open Complex Finset Metric

namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature

noncomputable def thetaTruncation (z : ℂ) : ℂ :=
  ∑ n ∈ range 20, Complex.exp (-(Real.pi:ℂ)*(n+1)^2*Complex.exp z)

end CertifiedZetaQuadrature

end Height100Module13

section Height100Module14

open Real MeasureTheory Set Filter HurwitzZeta
namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature

noncomputable def phase (τ t : ℝ) : ℂ := Complex.exp (Complex.I*(τ:ℂ)*(log t:ℂ))
noncomputable def twistedRaw (a : ℕ) (τ : ℝ) (k : ℕ) (t : ℝ) : ℂ :=
  (momentWeight a k t*(evenKernel 0 t-1):ℝ)*phase τ t
noncomputable def twistedFinite (a : ℕ) (τ : ℝ) (k : ℕ) (t : ℝ) : ℂ :=
  (2*momentWeight a k t*(∑ n ∈ Finset.range 20, exp (-π*(n+1:ℝ)^2*t)):ℝ)*phase τ t

lemma norm_phase (τ t : ℝ) : ‖phase τ t‖=1 := by
  simp [phase,Complex.norm_exp,Complex.mul_re,Complex.mul_im]

lemma momentWeight_nonneg (a k : ℕ) {t : ℝ} (ht : 1≤ t) : 0≤ momentWeight a k t := by
  have hl := log_nonneg ht
  unfold momentWeight
  positivity

lemma momentWeight_bound (a k : ℕ) (ha : a≤ 64) {t : ℝ} (ht : 1≤ t) :
    momentWeight a k t≤ t^64 := by
  have ht0 : 0< t := by linarith
  have hl := log_nonneg ht
  have hp := pow_div_factorial_le_exp (a*log t) (by positivity) k
  rw [exp_nat_mul,exp_log ht0] at hp
  have hr : t^(-3/4:ℝ)≤ 1 := rpow_le_one_of_one_le_of_nonpos ht (by norm_num)
  have hta : t^a≤ t^64 := pow_le_pow_right₀ ht ha
  unfold momentWeight
  rw [mul_div_assoc]
  calc
    _ ≤  t^(-3/4:ℝ)*t^a := by gcongr
    _ ≤  t^a := by nlinarith [pow_nonneg ht0.le a]
    _ ≤  _ := hta

lemma momentWeight_continuousOn (a k : ℕ) : ContinuousOn (momentWeight a k) (Ici 1) := by
  intro t ht
  have ht0 : t≠0 := by linarith [show 1≤ t from ht]
  apply ContinuousAt.continuousWithinAt
  unfold momentWeight
  exact (((continuousAt_id.rpow_const (Or.inl ht0)).mul
    ((continuousAt_const.mul (Real.continuousAt_log ht0)).pow k)).div_const _)

lemma phase_continuousOn (τ : ℝ) : ContinuousOn (phase τ) (Ici 1) := by
  intro t ht
  have ht0 : t≠0 := by linarith [show 1≤ t from ht]
  have hl := Real.continuousAt_log ht0
  apply ContinuousAt.continuousWithinAt
  unfold phase
  fun_prop

lemma twistedRaw_continuousOn (a : ℕ) (τ : ℝ) (k : ℕ) :
    ContinuousOn (twistedRaw a τ k) (Ici 1) := by
  apply ContinuousOn.mul _ (phase_continuousOn τ)
  apply Complex.continuous_ofReal.comp_continuousOn
  apply (momentWeight_continuousOn a k).mul
  exact ((continuousOn_evenKernel 0).mono (fun t ht => by
    change 0< t; linarith [show 1≤ t from ht])).sub continuousOn_const

lemma twistedFinite_continuousOn (a : ℕ) (τ : ℝ) (k : ℕ) :
    ContinuousOn (twistedFinite a τ k) (Ici 1) := by
  apply ContinuousOn.mul _ (phase_continuousOn τ)
  apply Complex.continuous_ofReal.comp_continuousOn
  exact (continuousOn_const.mul (momentWeight_continuousOn a k)).mul (by fun_prop)

lemma norm_twistedRaw_bound (a : ℕ) (τ : ℝ) (k : ℕ) (ha : a≤ 64) {t : ℝ} (ht : 1≤ t) :
    ‖twistedRaw a τ k t‖≤ (21/10:ℝ)*(t^64*exp (-π*t)) := by
  rw [twistedRaw,norm_mul,norm_phase,mul_one,Complex.norm_real,Real.norm_eq_abs,
    abs_mul,abs_of_nonneg (momentWeight_nonneg a k ht)]
  calc
    _ ≤  t^64*((21/10:ℝ)*exp (-π*t)) := mul_le_mul (momentWeight_bound a k ha ht)
      (ZetaSix.abs_evenKernel_sub_one_le_of_one_le ht) (abs_nonneg _) (by positivity)
    _ = _ := by ring

lemma norm_twisted_difference_bound (a : ℕ) (τ : ℝ) (k : ℕ) (ha : a≤ 64)
    {t : ℝ} (ht : 1≤ t) :
    ‖twistedRaw a τ k t-twistedFinite a τ k t‖≤ (21/10:ℝ)*(t^64*exp (-441*π*t)) := by
  have he : twistedRaw a τ k t-twistedFinite a τ k t =
      ((momentWeight a k t*(evenKernel 0 t-1-2*(∑ n ∈ Finset.range 20,
        exp (-π*(n+1:ℝ)^2*t))):ℝ):ℂ)*phase τ t := by
    unfold twistedRaw twistedFinite
    push_cast
    ring
  rw [he,norm_mul,norm_phase,mul_one,Complex.norm_real,Real.norm_eq_abs,
    abs_mul,abs_of_nonneg (momentWeight_nonneg a k ht)]
  have hb := kernel_finite_remainder_bound 20 ht
  norm_num only [Nat.cast_ofNat] at hb
  have hexp : -π*441*t=-441*π*t := by ring
  rw [hexp] at hb
  calc
    _ ≤  t^64*((21/10:ℝ)*exp (-441*π*t)) := mul_le_mul (momentWeight_bound a k ha ht)
      hb (abs_nonneg _) (by positivity)
    _ = _ := by ring

lemma twistedRaw_integrable (a : ℕ) (τ : ℝ) (k : ℕ) (ha : a≤ 64) :
    IntegrableOn (twistedRaw a τ k) (Ioi 1) := by
  have hg := ((ZetaSix.integrableOn_pow_mul_exp 64).mono_set
    (Ioi_subset_Ioi (show (0:ℝ)≤ 1 by norm_num))).const_mul (21/10:ℝ)
  apply hg.mono' (((twistedRaw_continuousOn a τ k).mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_twistedRaw_bound a τ k ha ht.le

lemma integral_twisted_difference_bound (a : ℕ) (τ : ℝ) (k : ℕ) (ha : a≤ 64) (B : ℝ) :
    ‖∫ t in Ioc (1:ℝ) B, twistedRaw a τ k t-twistedFinite a τ k t‖ ≤  1/10^370 := by
  have hg : IntegrableOn (fun t : ℝ => (21/10:ℝ)*(t^64*exp (-441*π*t))) (Ioi 1) :=
    by
      simpa only [neg_mul,IntegrableOn] using ((polynomial_exp_tail_general 64 1 (441*π) (by norm_num)
        (by nlinarith [pi_gt_three])).1).const_mul (21/10:ℝ)
  have hb := norm_integral_le_of_norm_le
    (hg.mono_set (Ioc_subset_Ioi_self : Ioc (1:ℝ) B ⊆ Ioi 1)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact norm_twisted_difference_bound a τ k ha ht.1.le)
  have hm := setIntegral_mono_set hg
    (Filter.Eventually.of_forall (fun t => by positivity : ∀t:ℝ,0≤ (21/10:ℝ)*(t^64*exp (-441*π*t))))
    (Filter.Eventually.of_forall (Ioc_subset_Ioi_self : Ioc (1:ℝ) B ⊆ Ioi 1))
  apply hb.trans (hm.trans _)
  rw [integral_const_mul]
  exact theta_twenty_moment_tail

lemma integral_twisted_tail_bound (a : ℕ) (τ : ℝ) (k : ℕ) (ha : a≤ 64)
    (B : ℝ) (hB : 400≤ B) :
    ‖∫ t in Ioi B, twistedRaw a τ k t‖≤ 1/10^370 := by
  have hg : IntegrableOn (fun t : ℝ => (21/10:ℝ)*(t^64*exp (-π*t))) (Ioi 400) :=
    ((polynomial_exp_tail_general 64 400 π (by norm_num)
      (by nlinarith [pi_gt_three])).1).const_mul _
  have hb := norm_integral_le_of_norm_le (hg.mono_set (Ioi_subset_Ioi hB)) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_twistedRaw_bound a τ k ha (by linarith [show B< t from ht]))
  have hm := setIntegral_mono_set hg
    (Filter.Eventually.of_forall (fun t => by positivity : ∀t:ℝ,0≤ (21/10:ℝ)*(t^64*exp (-π*t))))
    (Filter.Eventually.of_forall (Ioi_subset_Ioi hB))
  apply hb.trans (hm.trans _)
  rw [integral_const_mul]
  exact large_moment_tail

lemma twisted_cutoff (a : ℕ) (τ : ℝ) (k : ℕ) (ha : a≤ 64) (B : ℝ) (hB : 400≤ B) :
    ‖(∫ t in Ioi (1:ℝ), twistedRaw a τ k t) -
      ∫ t in Ioc (1:ℝ) B, twistedFinite a τ k t‖≤ 2/10^370 := by
  have h1B : (1:ℝ)≤ B := by linarith
  have hr := twistedRaw_integrable a τ k ha
  have hf : IntegrableOn (twistedFinite a τ k) (Ioc (1:ℝ) B) :=
    (((twistedFinite_continuousOn a τ k).mono
      (Icc_subset_Ici_self : Icc (1:ℝ) B ⊆ Ici 1)).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hs := setIntegral_union
    (show Disjoint (Ioc (1:ℝ) B) (Ioi B) from by simp [Set.disjoint_left]) measurableSet_Ioi
    (hr.mono_set Ioc_subset_Ioi_self) (hr.mono_set (Ioi_subset_Ioi h1B))
  rw [Ioc_union_Ioi_eq_Ioi h1B] at hs
  have he : (∫ t in Ioi (1:ℝ), twistedRaw a τ k t) - ∫ t in Ioc (1:ℝ) B, twistedFinite a τ k t =
      (∫ t in Ioc (1:ℝ) B, twistedRaw a τ k t-twistedFinite a τ k t)+
        ∫ t in Ioi B, twistedRaw a τ k t := by
    rw [integral_sub (hr.mono_set Ioc_subset_Ioi_self) hf]
    rw [hs]
    ring
  rw [he]
  have hdiff := integral_twisted_difference_bound a τ k ha B
  have htail := integral_twisted_tail_bound a τ k ha B hB
  exact (norm_add_le _ _).trans (by linarith)

end CertifiedZetaQuadrature

end Height100Module14

section Height100Module15

open Complex MeasureTheory Metric Set Finset
namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature

noncomputable def globalKernelMoment (k : ℕ) (z : ℂ) : ℂ :=
  2*Complex.exp (z/4) * ((64*z)^k/(k.factorial:ℂ)) * thetaTruncation z

lemma globalKernelMoment_entire (k : ℕ) : Differentiable ℂ (globalKernelMoment k) := by
  unfold globalKernelMoment thetaTruncation
  fun_prop

end CertifiedZetaQuadrature

end Height100Module15

section Height100Module16

open Real MeasureTheory Set Filter Finset
namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature

noncomputable def transformedMoment (a : ℕ) (τ : ℝ) (k : ℕ) (z : ℂ) : ℂ :=
  2*Complex.exp (z/4) * (((a:ℂ)*z)^k/(k.factorial:ℂ)) *
    Complex.exp (Complex.I*(τ:ℂ)*z) * thetaTruncation z

lemma exp_six_ge_four_hundred : (400:ℝ)≤ exp 6 := by
  have h1 : (2718/1000:ℝ)≤ exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤ 2718/1000) h1 6
  norm_num at hp
  linarith

lemma finite_theta_cast (u : ℝ) :
    ((∑ n ∈ range 20, exp (-π*(n+1:ℝ)^2*exp u):ℝ):ℂ)=thetaTruncation (u:ℂ) := by
  unfold thetaTruncation
  push_cast
  rfl

lemma weight_exp_identity (a k : ℕ) (u : ℝ) :
    exp u*momentWeight a k (exp u)=exp (u/4)*(a*u)^k/(k.factorial:ℝ) := by
  unfold momentWeight
  rw [log_exp,← Real.exp_mul]
  have he : u+u*(-3/4:ℝ)=u/4 := by ring
  calc
    _ = (exp u*exp (u*(-3/4)))*(a*u)^k/(k.factorial:ℝ) := by ring
    _ = _ := by rw [← exp_add,he]

lemma transformedMoment_point (a : ℕ) (τ : ℝ) (k : ℕ) (u : ℝ) :
    exp u • twistedFinite a τ k (exp u)=transformedMoment a τ k (u:ℂ) := by
  have hw := congrArg (fun x : ℝ => (x:ℂ)) (weight_exp_identity a k u)
  push_cast at hw
  rw [Complex.real_smul]
  unfold twistedFinite transformedMoment phase
  rw [log_exp]
  push_cast
  rw [← finite_theta_cast u]
  calc
    _ = 2*((exp u:ℂ)*(momentWeight a k (exp u):ℂ))*
        Complex.exp (Complex.I*(τ:ℂ)*(u:ℂ))*
        ((∑ n ∈ range 20, exp (-π*(n+1:ℝ)^2*exp u):ℝ):ℂ) := by push_cast; ring
    _ = _ := by rw [Complex.ofReal_exp,hw]; push_cast; ring

lemma transformedMoment_integral (a : ℕ) (τ : ℝ) (k : ℕ) :
    (∫ u in (0:ℝ)..6, transformedMoment a τ k (u:ℂ)) =
      ∫ t in Ioc (1:ℝ) (exp 6), twistedFinite a τ k t := by
  have he := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (a:=0) (b:=6) (f:=exp) (f':=exp) (g:=twistedFinite a τ k)
    Real.continuous_exp.continuousOn (fun x _ => Real.hasDerivAt_exp x)
    (fun x _ => (Real.exp_pos x).le)
  simp only [Function.comp_apply,exp_zero] at he
  rw [intervalIntegral.integral_of_le (by linarith [exp_six_ge_four_hundred] : (1:ℝ)≤ exp 6)] at he
  rw [← he]
  apply intervalIntegral.integral_congr
  intro u _
  exact (transformedMoment_point a τ k u).symm

lemma twisted_cutoff_transformed (a : ℕ) (τ : ℝ) (k : ℕ) (ha : a≤ 64) :
    ‖(∫ t in Ioi (1:ℝ), twistedRaw a τ k t) -
      ∫ u in (0:ℝ)..6, transformedMoment a τ k (u:ℂ)‖ ≤  2/10^370 := by
  rw [transformedMoment_integral]
  exact twisted_cutoff a τ k ha (exp 6) exp_six_ge_four_hundred

lemma transformedMoment_sixtyfour (k : ℕ) (z : ℂ) :
    transformedMoment 64 0 k z=globalKernelMoment k z := by
  simp [transformedMoment,globalKernelMoment]

end CertifiedZetaQuadrature

end Height100Module16
section Height100Module56

open Complex Metric Finset MeasureTheory
namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature

lemma theta_term_unit_bound (n : ℕ) (z : ℂ) (hi : |z.im|≤ 1) :
    ‖Complex.exp (-(Real.pi:ℂ)*(n+1)^2*Complex.exp z)‖ ≤ 
      Real.exp (-(3/2)*Real.exp z.re) := by
  have hc : (1/2:ℝ)≤ Real.cos z.im := by
    have h := Real.one_sub_sq_div_two_le_cos (x:=z.im)
    have hs : z.im^2≤ 1 := by
      have ha := abs_le.mp hi
      nlinarith [mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr ha.1)]
    linarith
  have hn : (1:ℝ)≤ (n+1:ℝ)^2 := by have : (0:ℝ)≤ n := Nat.cast_nonneg n; nlinarith
  have hp : (3/2:ℝ)≤ Real.pi*(n+1:ℝ)^2*Real.cos z.im := by
    have h1 : (3:ℝ)≤ Real.pi*(n+1:ℝ)^2 :=
      Real.pi_gt_three.le.trans (le_mul_of_one_le_right Real.pi_pos.le hn)
    have hm := mul_le_mul h1 hc (by norm_num : (0:ℝ)≤ 1/2)
      (by positivity : (0:ℝ)≤ Real.pi*(n+1:ℝ)^2)
    linarith
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [mul_re,neg_re,ofReal_re,neg_im,ofReal_im,neg_zero,mul_im,
    natCast_re,natCast_im,add_re,one_re,add_im,one_im,pow_two,Complex.exp_re,Complex.exp_im]
  nlinarith [mul_nonneg (sub_nonneg.mpr hp) (Real.exp_pos z.re).le]

end CertifiedZetaQuadrature

end Height100Module56

section Height100Module57

open Complex Metric Finset MeasureTheory
namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature

lemma exp_three_ge_twenty : (20:ℝ)≤ Real.exp 3 := by
  have hbase : (2718/1000:ℝ)≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤ 2718/1000) hbase 3
  have he : Real.exp 3=(Real.exp 1)^3 := by
    simpa only [Nat.cast_ofNat,mul_one] using Real.exp_nat_mul (1:ℝ) 3
  rw [he]
  norm_num at h ⊢
  linarith

lemma log_fortythree_le_377 : Real.log 43≤ 377/100 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0:ℝ)<43)).mpr
  have hsmall := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤ 77/100) 5
  norm_num [Finset.sum_range_succ] at hsmall
  have hmul := mul_le_mul exp_three_ge_twenty hsmall
    (by norm_num) (Real.exp_pos 3).le
  have he : Real.exp (377/100)=Real.exp 3*Real.exp (77/100) := by
    rw [←Real.exp_add]
    congr 1
    ring
  rw [he]
  nlinarith

lemma exp_tangent_fortythree_fine (r : ℝ) : 43*r-11911/100≤ Real.exp r := by
  have he := Real.add_one_le_exp (r-Real.log 43)
  rw [Real.exp_sub,Real.exp_log (by norm_num : (0:ℝ)<43)] at he
  nlinarith [log_fortythree_le_377]

lemma exp_tangent_twenty (r : ℝ) (hr : 2≤ r) : 20*r-40≤ Real.exp r := by
  have he := Real.add_one_le_exp (r-3)
  have hmul := mul_le_mul exp_three_ge_twenty he (by linarith) (Real.exp_pos 3).le
  have hx : Real.exp 3*Real.exp (r-3)=Real.exp r := by
    rw [←Real.exp_add]
    congr 1
    ring
  rw [hx] at hmul
  linarith

set_option exponentiation.threshold 512 in
lemma globalKernelMoment_unit_disk_84 (k : ℕ) (c : ℝ) (hc : 0≤ c) (z : ℂ)
    (hz : ‖z-(c:ℂ)‖≤ 1) : ‖globalKernelMoment k z‖≤ 10^84 := by
  have hre : |z.re-c|≤ 1 := by
    simpa only [sub_re,ofReal_re] using (Complex.abs_re_le_norm (z-(c:ℂ))).trans hz
  have him : |z.im|≤ 1 := by
    simpa only [sub_im,ofReal_im,sub_zero] using (Complex.abs_im_le_norm (z-(c:ℂ))).trans hz
  have hr : -(1:ℝ)≤ z.re := by linarith [(abs_le.mp hre).1]
  have himsq : z.im^2≤ 1 := by
    have hi := abs_le.mp him
    nlinarith [mul_nonneg (sub_nonneg.mpr hi.2) (sub_nonneg.mpr hi.1)]
  have hp : ‖(64*z)^k/(k.factorial:ℂ)‖ ≤  Real.exp (64*‖z‖) := by
    simpa [norm_div,norm_pow,norm_mul] using
      Real.pow_div_factorial_le_exp (64*‖z‖) (by positivity) k
  have ht : ‖thetaTruncation z‖≤ 20*Real.exp (-(3/2)*Real.exp z.re) := by
    calc
      _ ≤  ∑ n ∈ range 20, ‖Complex.exp (-(Real.pi:ℂ)*(n+1)^2*Complex.exp z)‖ := norm_sum_le _ _
      _ ≤  ∑ _n ∈ range 20, Real.exp (-(3/2)*Real.exp z.re) :=
        sum_le_sum (fun n _ => theta_term_unit_bound n z him)
      _ = _ := by simp
  have he : z.re/4+64*‖z‖-(3/2)*Real.exp z.re≤ 189 := by
    by_cases hr3 : 3≤ z.re
    · have hnorm : ‖z‖≤ z.re+1/6 := by
        have hs := Complex.sq_norm_sub_sq_re z
        apply (sq_le_sq₀ (norm_nonneg z) (by linarith : 0≤ z.re+1/6)).mp
        nlinarith
      have ht := exp_tangent_fortythree_fine z.re
      linarith
    · by_cases hr2 : 2≤ z.re
      · have hnorm : ‖z‖≤ z.re+1/4 := by
          have hs := Complex.sq_norm_sub_sq_re z
          apply (sq_le_sq₀ (norm_nonneg z) (by linarith : 0≤ z.re+1/4)).mp
          nlinarith
        have ht := exp_tangent_twenty z.re hr2
        linarith
      · have hrsq : z.re^2≤ 4 := by
          nlinarith [mul_nonneg (by linarith : 0≤ 2-z.re) (by linarith : 0≤ 2+z.re)]
        have hnorm : ‖z‖≤ 5/2 := by
          have hs := Complex.sq_norm_sub_sq_re z
          apply (sq_le_sq₀ (norm_nonneg z) (by norm_num : (0:ℝ)≤ 5/2)).mp
          nlinarith
        have hx := Real.exp_pos z.re
        linarith
  unfold globalKernelMoment
  simp only [norm_mul]
  rw [show ‖(2:ℂ)‖=2 by norm_num]
  calc
    _ ≤  2*Real.exp (z.re/4)*Real.exp (64*‖z‖)*(20*Real.exp (-(3/2)*Real.exp z.re)) := by
      gcongr
      rw [Complex.norm_exp]
      simp
    _ = 40*Real.exp (z.re/4+64*‖z‖-(3/2)*Real.exp z.re) := by
      rw [show z.re/4+64*‖z‖-(3/2)*Real.exp z.re =
        z.re/4+64*‖z‖+(-(3/2)*Real.exp z.re) by ring,Real.exp_add,Real.exp_add]
      ring
    _ ≤  40*Real.exp 189 := by gcongr
    _ ≤  40*(27183/10000:ℝ)^189 := by
      rw [show Real.exp 189=(Real.exp 1)^189 by
        simpa only [Nat.cast_ofNat,mul_one] using Real.exp_nat_mul (1:ℝ) 189]
      gcongr
      linarith [Real.exp_one_lt_d9]
    _ ≤  10^84 := by norm_num
end CertifiedZetaQuadrature

end Height100Module57
end RH1000MellinProof

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
namespace RH1000MellinProof.CertifiedZetaQuadrature
open Complex Metric Finset MeasureTheory
lemma transformed_entire (a : ℕ) (τ : ℝ) (k : ℕ) :
    Differentiable ℂ (transformedMoment a τ k) := by
  unfold transformedMoment thetaTruncation
  fun_prop
lemma complex_phase_bound (τ : ℝ) (ht : |τ| ≤ 500) (c : ℝ) (z : ℂ)
    (hz : ‖z-(c:ℂ)‖ ≤ 1) : ‖Complex.exp (Complex.I*(τ:ℂ)*z)‖ ≤ Real.exp 500 := by
  have hi : |z.im| ≤ 1 := by
    simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero] using
      (Complex.abs_im_le_norm (z-(c:ℂ))).trans hz
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  calc
    _ = -τ*z.im := by simp [Complex.mul_re,Complex.mul_im]
    _ ≤ |-τ*z.im| := le_abs_self _
    _ = |τ| * |z.im| := by rw [abs_mul,abs_neg]
    _ ≤ 500*1 := mul_le_mul ht hi (abs_nonneg _) (by norm_num)
    _ = _ := by ring
lemma exp_five_hundred_bound : Real.exp 500 ≤ (10:ℝ)^218 := by
  rw [show Real.exp 500=(Real.exp 1)^500 by
    simpa only [Nat.cast_ofNat,mul_one] using Real.exp_nat_mul (1:ℝ) 500]
  calc
    _ ≤ (27183/10000:ℝ)^500 := by
      gcongr
      linarith [Real.exp_one_lt_d9]
    _ ≤ _ := by norm_num
lemma transformed_unit_disk (a : ℕ) (ha : a ≤ 64) (τ : ℝ) (ht : |τ| ≤ 500)
    (k : ℕ) (c : ℝ) (hc : 0 ≤ c) (z : ℂ) (hz : ‖z-(c:ℂ)‖ ≤ 1) :
    ‖transformedMoment a τ k z‖ ≤ (10:ℝ)^302 := by
  have hp : ‖((a:ℂ)*z)^k/(k.factorial:ℂ)‖ ≤ ‖(64*z)^k/(k.factorial:ℂ)‖ := by
    norm_num only [norm_div,norm_pow,norm_mul,Complex.norm_natCast,norm_ofNat]
    gcongr
    exact_mod_cast ha
  have hf := complex_phase_bound τ ht c z hz
  have hg := globalKernelMoment_unit_disk_84 k c hc z hz
  calc
    _ = ‖2*Complex.exp (z/4)‖*‖((a:ℂ)*z)^k/(k.factorial:ℂ)‖*
      ‖Complex.exp (Complex.I*(τ:ℂ)*z)‖*‖thetaTruncation z‖ := by
        simp only [transformedMoment,norm_mul]
    _ ≤ ‖2*Complex.exp (z/4)‖*‖(64*z)^k/(k.factorial:ℂ)‖*
      Real.exp 500*‖thetaTruncation z‖ := by gcongr
    _ = ‖globalKernelMoment k z‖*Real.exp 500 := by
      simp only [globalKernelMoment,norm_mul]
      ring
    _ ≤ (10:ℝ)^84*Real.exp 500 := by gcongr
    _ ≤ (10:ℝ)^84*(10:ℝ)^218 := by gcongr; exact exp_five_hundred_bound
    _ = _ := by norm_num
end RH1000MellinProof.CertifiedZetaQuadrature

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
namespace RH1000MellinProof.CertifiedZetaQuadrature
open Complex Metric MeasureTheory
lemma transformed_panel_1024 (a : ℕ) (ha : a ≤ 64) (τ : ℝ) (ht : |τ| ≤ 500)
    (k : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    ‖(∫ x in -(3/16:ℝ)..(3/16:ℝ), transformedMoment a τ k ((c:ℂ)+x))-
      RH1000MellinProof.CertifiedTaylorQuadrature.panel
        (transformedMoment a τ k) c (3/16) 1024‖ ≤ 1/10^430 := by
  have hb : ∀ z ∈ sphere (c:ℂ) (1:ℝ), ‖transformedMoment a τ k z‖ ≤ (10:ℝ)^302 := by
    intro z hz
    exact transformed_unit_disk a ha τ ht k c hc z (mem_sphere_iff_norm.mp hz).le
  have he := RH1000MellinProof.CertifiedTaylorQuadrature.panel_error
    (transformedMoment a τ k) (transformed_entire a τ k) c 1 (10^302) (3/16)
    (by norm_num) (by positivity) (by norm_num) (by norm_num) hb 1024
  apply he.trans
  norm_num
end RH1000MellinProof.CertifiedZetaQuadrature
namespace RH1000MellinProof.DirectMellinQuadrature
open Complex MeasureTheory Set Finset
open RH1000MellinProof.CertifiedZetaQuadrature RH1000MellinProof.CertifiedTaylorQuadrature
noncomputable def grid (i : ℕ) : ℝ := 3*(i:ℝ)/8
noncomputable def center (i : ℕ) : ℝ := 3*(2*(i:ℝ)+1)/16
noncomputable def rule (a : ℕ) (τ : ℝ) (k : ℕ) : ℂ :=
  ∑ i ∈ range 16, panel (transformedMoment a τ k) (center i) (3/16) 1024
lemma shifted_integral (a : ℕ) (τ : ℝ) (k i : ℕ) :
    (∫ u in -(3/16:ℝ)..(3/16:ℝ), transformedMoment a τ k ((center i:ℂ)+u))=
      ∫ t in grid i..grid (i+1), transformedMoment a τ k (t:ℂ) := by
  have h := intervalIntegral.integral_comp_add_left
    (fun t : ℝ => transformedMoment a τ k (t:ℂ)) (a:=-(3/16:ℝ)) (b:=3/16) (center i)
  have hL : center i+(-(3/16:ℝ))=grid i := by unfold center grid; ring
  have hR : center i+(3/16:ℝ)=grid (i+1) := by unfold center grid; push_cast; ring
  simpa only [Complex.ofReal_add,hL,hR] using h
lemma integral_sum (a : ℕ) (τ : ℝ) (k : ℕ) :
    (∑ i ∈ range 16, ∫ t in grid i..grid (i+1), transformedMoment a τ k (t:ℂ))=
      ∫ u in (0:ℝ)..6, transformedMoment a τ k (u:ℂ) := by
  have hc : Continuous (fun t : ℝ => transformedMoment a τ k (t:ℂ)) :=
    (transformed_entire a τ k).continuous.comp Complex.continuous_ofReal
  have h := intervalIntegral.sum_integral_adjacent_intervals (μ:=volume) (a:=grid) (n:=16)
    (fun i _ => hc.intervalIntegrable (grid i) (grid (i+1)))
  have h0 : grid 0=0 := by norm_num [grid]
  have h16 : grid 16=6 := by norm_num [grid]
  rwa [h0,h16] at h
lemma integral_error (a : ℕ) (ha : a ≤ 64) (τ : ℝ) (ht : |τ| ≤ 500) (k : ℕ) :
    ‖(∫ u in (0:ℝ)..6, transformedMoment a τ k (u:ℂ))-rule a τ k‖ ≤ 16/10^430 := by
  rw [←integral_sum,rule,←sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ range 16, ‖(∫ t in grid i..grid (i+1), transformedMoment a τ k (t:ℂ))-
      panel (transformedMoment a τ k) (center i) (3/16) 1024‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ range 16, (1/10^430:ℝ) := by
      apply sum_le_sum
      intro i _
      rw [←shifted_integral]
      exact transformed_panel_1024 a ha τ ht k (center i) (by unfold center; positivity)
    _ = _ := by simp; ring
lemma mellin_error (a : ℕ) (ha : a ≤ 64) (τ : ℝ) (ht : |τ| ≤ 500) (k : ℕ) :
    ‖(∫ t in Ioi (1:ℝ), twistedRaw a τ k t)-rule a τ k‖ ≤ 1/10^365 := by
  have hc := twisted_cutoff_transformed a τ k ha
  have hq := integral_error a ha τ ht k
  have he : (∫ t in Ioi (1:ℝ), twistedRaw a τ k t)-rule a τ k=
      ((∫ t in Ioi (1:ℝ), twistedRaw a τ k t)-
        (∫ u in (0:ℝ)..6, transformedMoment a τ k (u:ℂ)))+
      ((∫ u in (0:ℝ)..6, transformedMoment a τ k (u:ℂ))-rule a τ k) := by ring
  rw [he]
  exact (norm_add_le _ _).trans (by linarith)
end RH1000MellinProof.DirectMellinQuadrature

theorem solution (a : ℕ) (ha : a ≤ 64) (τ : ℝ) (ht : |τ| ≤ 500) (k : ℕ) :
    ‖(∫ t in Set.Ioi (1:ℝ), RH1000Mellin.raw a τ k t)-
      TaoFivePrimes_RH100To1000MellinModel a τ k‖ ≤ 1/10^365 := by
  exact RH1000MellinProof.DirectMellinQuadrature.mellin_error a ha τ ht k
