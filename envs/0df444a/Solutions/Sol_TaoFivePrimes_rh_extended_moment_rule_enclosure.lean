-- Prove2me | solution 1 for TaoFivePrimes.rh_extended_moment_rule_enclosure
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T18:55:38.615614+00:00
-- url     : https://prove2.me/submissions/83dc2b45-38ad-4aeb-96a2-a41f1708213e

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

lemma theta_eight_moment_tail :
    (21/10:ℝ)*(∫ t in Ioi (1:ℝ), t^64*exp (-81*π*t)) ≤  1/10^100 := by
  have hb := (polynomial_exp_tail_general 64 1 (81*π) (by norm_num)
    (by nlinarith [pi_gt_three])).2
  have hn : exp (-81*π)≤ (1/23:ℝ)^81 := by simpa using exp_neg_nat_pi_le 81
  calc
    _ ≤  (21/10:ℝ)*(exp (-81*π)/(81*π-64)) := by simpa using mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤ 21/10)
    _ ≤  (21/10:ℝ)*((1/23:ℝ)^81/179) := by gcongr; nlinarith [pi_gt_three]
    _ ≤  1/10^100 := by norm_num

lemma large_moment_tail :
    (21/10:ℝ)*(∫ t in Ioi (400:ℝ), t^64*exp (-π*t)) ≤  1/10^100 := by
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
    _ ≤  1/10^100 := by
      rw [show (400:ℕ)=200+200 by rfl, pow_add]
      norm_num

end CertifiedZetaQuadrature

end Height100Module12

section Height100Module13

open Complex Finset Metric

namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature

noncomputable def thetaTruncation (z : ℂ) : ℂ :=
  ∑ n ∈ range 8, Complex.exp (-(Real.pi:ℂ)*(n+1)^2*Complex.exp z)

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
  (2*momentWeight a k t*(∑ n ∈ Finset.range 8, exp (-π*(n+1:ℝ)^2*t)):ℝ)*phase τ t

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
    ‖twistedRaw a τ k t-twistedFinite a τ k t‖≤ (21/10:ℝ)*(t^64*exp (-81*π*t)) := by
  have he : twistedRaw a τ k t-twistedFinite a τ k t =
      ((momentWeight a k t*(evenKernel 0 t-1-2*(∑ n ∈ Finset.range 8,
        exp (-π*(n+1:ℝ)^2*t))):ℝ):ℂ)*phase τ t := by
    unfold twistedRaw twistedFinite
    push_cast
    ring
  rw [he,norm_mul,norm_phase,mul_one,Complex.norm_real,Real.norm_eq_abs,
    abs_mul,abs_of_nonneg (momentWeight_nonneg a k ht)]
  have hb := kernel_finite_remainder_bound 8 ht
  norm_num only [Nat.cast_ofNat] at hb
  have hexp : -π*81*t=-81*π*t := by ring
  rw [hexp] at hb
  calc
    _ ≤  t^64*((21/10:ℝ)*exp (-81*π*t)) := mul_le_mul (momentWeight_bound a k ha ht)
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
    ‖∫ t in Ioc (1:ℝ) B, twistedRaw a τ k t-twistedFinite a τ k t‖ ≤  1/10^100 := by
  have hg : IntegrableOn (fun t : ℝ => (21/10:ℝ)*(t^64*exp (-81*π*t))) (Ioi 1) :=
    by
      simpa only [neg_mul,IntegrableOn] using ((polynomial_exp_tail_general 64 1 (81*π) (by norm_num)
        (by nlinarith [pi_gt_three])).1).const_mul (21/10:ℝ)
  have hb := norm_integral_le_of_norm_le
    (hg.mono_set (Ioc_subset_Ioi_self : Ioc (1:ℝ) B ⊆ Ioi 1)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact norm_twisted_difference_bound a τ k ha ht.1.le)
  have hm := setIntegral_mono_set hg
    (Filter.Eventually.of_forall (fun t => by positivity : ∀t:ℝ,0≤ (21/10:ℝ)*(t^64*exp (-81*π*t))))
    (Filter.Eventually.of_forall (Ioc_subset_Ioi_self : Ioc (1:ℝ) B ⊆ Ioi 1))
  apply hb.trans (hm.trans _)
  rw [integral_const_mul]
  exact theta_eight_moment_tail

lemma integral_twisted_tail_bound (a : ℕ) (τ : ℝ) (k : ℕ) (ha : a≤ 64)
    (B : ℝ) (hB : 400≤ B) :
    ‖∫ t in Ioi B, twistedRaw a τ k t‖≤ 1/10^100 := by
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
      ∫ t in Ioc (1:ℝ) B, twistedFinite a τ k t‖≤ 2/10^100 := by
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
    ((∑ n ∈ range 8, exp (-π*(n+1:ℝ)^2*exp u):ℝ):ℂ)=thetaTruncation (u:ℂ) := by
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
        ((∑ n ∈ range 8, exp (-π*(n+1:ℝ)^2*exp u):ℝ):ℂ) := by push_cast; ring
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
      ∫ u in (0:ℝ)..6, transformedMoment a τ k (u:ℂ)‖ ≤  2/10^100 := by
  rw [transformedMoment_integral]
  exact twisted_cutoff a τ k ha (exp 6) exp_six_ge_four_hundred

lemma transformedMoment_sixtyfour (k : ℕ) (z : ℂ) :
    transformedMoment 64 0 k z=globalKernelMoment k z := by
  simp [transformedMoment,globalKernelMoment]

end CertifiedZetaQuadrature

end Height100Module16

section Height100Module17

open Complex MeasureTheory Set HurwitzZeta Real
open scoped Real
set_option autoImplicit false
set_option exponentiation.threshold 1024
set_option maxRecDepth 10000

namespace TaoZetaWide256
open _root_.TaoZetaWide256
open ZetaSix
open _root_.ZetaSix

end TaoZetaWide256

end Height100Module17

section Height100Module18

open Complex Finset Metric
open scoped BigOperators
set_option autoImplicit false
set_option exponentiation.threshold 1024

namespace TaoZetaGlobal
open _root_.TaoZetaGlobal

end TaoZetaGlobal

end Height100Module18

section Height100Module19

open Complex MeasureTheory Set Filter Asymptotics
open scoped Topology
set_option autoImplicit false

namespace TaoZetaCertificate
open _root_.TaoZetaCertificate

end TaoZetaCertificate

end Height100Module19

section Height100Module20

open Complex MeasureTheory Set HurwitzZeta
set_option autoImplicit false

namespace TaoZetaCertificate
open _root_.TaoZetaCertificate

end TaoZetaCertificate

end Height100Module20

section Height100Module21

open Complex MeasureTheory Set
open scoped ComplexConjugate
set_option autoImplicit false

namespace TaoZetaCertificate
open _root_.TaoZetaCertificate

end TaoZetaCertificate

end Height100Module21

section Height100Module22

open Complex Finset Metric Filter
namespace CertifiedComplexTaylor
open _root_.CertifiedComplexTaylor
open CertifiedTaylorQuadrature
open _root_.CertifiedTaylorQuadrature

lemma coefficient_sub (f g : ℂ → ℂ) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (c : ℂ) (n : ℕ) :
    coefficient (fun z => f z-g z) c n = coefficient f c n-coefficient g c n := by
  unfold coefficient
  change iteratedDeriv n (f-g) c/(n.factorial:ℂ)=_
  rw [iteratedDeriv_sub hf.contDiff.contDiffAt hg.contDiff.contDiffAt,sub_div]

end CertifiedComplexTaylor

end Height100Module22

section Height100Module23

open Complex MeasureTheory Set HurwitzZeta Real
open scoped Real
set_option autoImplicit false

namespace TaoZetaWide
open _root_.TaoZetaWide
open ZetaSix
open _root_.ZetaSix

end TaoZetaWide

end Height100Module23

section Height100Module24

open Complex Metric TaoZetaCertificate
open _root_.TaoZetaCertificate
namespace CertifiedLocalXi
open _root_.CertifiedLocalXi

end CertifiedLocalXi

end Height100Module24

section Height100Module25

open Complex MeasureTheory Set Finset
namespace CertifiedGlobalMoments
open _root_.CertifiedGlobalMoments
open CertifiedZetaQuadrature TaoZetaCertificate
open _root_.CertifiedZetaQuadrature _root_.TaoZetaCertificate

lemma moment_complex (j : ℕ) :
    (moment j:ℂ)=∫ t in Ioi (1:ℝ), twistedRaw 64 0 (2*j) t := by
  unfold moment twistedRaw
  simp only [phase,ofReal_zero,mul_zero,zero_mul,Complex.exp_zero,mul_one]
  exact (integral_complex_ofReal).symm

end CertifiedGlobalMoments

end Height100Module25

section Height100Module26

open Complex Finset
namespace CertifiedEvenPolynomial
open _root_.CertifiedEvenPolynomial

end CertifiedEvenPolynomial

end Height100Module26

section Height100Module27

open Complex Metric Set
namespace CertifiedLocalXi
open _root_.CertifiedLocalXi

end CertifiedLocalXi

end Height100Module27

section Height100Module28

open Complex Metric
open scoped ComplexConjugate
namespace CertifiedLocalXi
open _root_.CertifiedLocalXi

end CertifiedLocalXi

end Height100Module28

section Height100Module29

open Complex Finset
namespace CertifiedLocalXi
open _root_.CertifiedLocalXi

end CertifiedLocalXi

end Height100Module29

section Height100Module30

open Complex Finset
namespace CertifiedLocalXi
open _root_.CertifiedLocalXi

end CertifiedLocalXi

end Height100Module30

section Height100Module31

open Complex Finset
namespace CertifiedPolynomialTranslation
open _root_.CertifiedPolynomialTranslation
open CertifiedTaylorQuadrature
open _root_.CertifiedTaylorQuadrature

end CertifiedPolynomialTranslation

end Height100Module31

section Height100Module32

open Complex Finset
namespace CertifiedPolynomialTranslation
open _root_.CertifiedPolynomialTranslation
open CertifiedTaylorQuadrature CertifiedGlobalMoments
open _root_.CertifiedTaylorQuadrature _root_.CertifiedGlobalMoments

end CertifiedPolynomialTranslation

end Height100Module32

section Height100Module33

set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

namespace CertifiedDenseGlobalPolynomial
open _root_.CertifiedDenseGlobalPolynomial
open Complex Finset CertifiedPolynomialTranslation
open _root_.CertifiedPolynomialTranslation

end CertifiedDenseGlobalPolynomial

end Height100Module33

section Height100Module34

set_option autoImplicit false
open Finset
open scoped BigOperators

namespace CertifiedFixedPoint
open _root_.CertifiedFixedPoint

noncomputable def Contains (S : ℕ) (b : Box) (x : ℝ) : Prop :=
  (b.lo:ℝ)/S ≤  x ∧ x ≤  (b.hi:ℝ)/S

noncomputable def oneBox (S : ℕ) : Box := ⟨S,S⟩
noncomputable def addBox (a b : Box) : Box := ⟨a.lo+b.lo,a.hi+b.hi⟩

lemma contains_nonneg {S : ℕ} {b : Box} {x : ℝ} (h : Contains S b x) : 0≤ x :=
  (by positivity : (0:ℝ)≤ b.lo/S).trans h.1

lemma quotient_bounds (m n : ℕ) (hn : 0< n) :
    ((m/n:ℕ):ℝ) ≤  (m:ℝ)/n ∧ (m:ℝ)/n ≤  ((m/n+1:ℕ):ℝ) := by
  refine ⟨Nat.cast_div_le, ?_⟩
  apply (div_le_iff₀ (by exact_mod_cast hn : (0:ℝ)< n)).mpr
  have h := (Nat.lt_mul_div_succ m hn).le
  exact_mod_cast (by simpa [Nat.mul_comm] using h)

lemma oneBox_sound {S : ℕ} (hS : 0< S) : Contains S (oneBox S) 1 := by
  have h : (S:ℝ)≠0 := by exact_mod_cast hS.ne'
  simp [Contains,oneBox,h]

lemma addBox_sound {S : ℕ} {a b : Box} {x y : ℝ}
    (ha : Contains S a x) (hb : Contains S b y) : Contains S (addBox a b) (x+y) := by
  constructor <;> dsimp [Contains,addBox] at *
  · push_cast
    rw [add_div]
    linarith [ha.1,hb.1]
  · push_cast
    rw [add_div]
    linarith [ha.2,hb.2]

lemma mulDivBox_sound {S d : ℕ} (hS : 0< S) (hd : 0< d)
    {a b : Box} {x y : ℝ} (ha : Contains S a x) (hb : Contains S b y) :
    Contains S (mulDivBox S d a b) (x*y/d) := by
  have hSr : (0:ℝ)< S := by exact_mod_cast hS
  have hdr : (0:ℝ)< d := by exact_mod_cast hd
  have hx := contains_nonneg ha
  have hy := contains_nonneg hb
  have hlo := (quotient_bounds (a.lo*b.lo) (S*d) (Nat.mul_pos hS hd)).1
  have hhi := (quotient_bounds (a.hi*b.hi) (S*d) (Nat.mul_pos hS hd)).2
  simp only [Nat.cast_mul] at hlo hhi
  constructor
  · calc
      _ ≤  (((a.lo:ℝ)*b.lo)/(S*d))/S := div_le_div_of_nonneg_right hlo hSr.le
      _ = ((a.lo:ℝ)/S*((b.lo:ℝ)/S))/d := by ring
      _ ≤  _ := by gcongr; exact ha.1; exact hb.1
  · calc
      _ ≤  ((a.hi:ℝ)/S*((b.hi:ℝ)/S))/d := by gcongr; exact ha.2; exact hb.2
      _ = (((a.hi:ℝ)*b.hi)/(S*d))/S := by ring
      _ ≤  _ := div_le_div_of_nonneg_right hhi hSr.le

/-- Fixed-point term recurrence, retaining both the current Taylor term and sum. -/
noncomputable def expTaylorRun (S : ℕ) (a : Box) : ℕ → Box × Box
  | 0 => (oneBox S,oneBox S)
  | n+1 =>
    let prev := expTaylorRun S a n
    let next := mulDivBox S (n+1) prev.1 a
    (next, addBox prev.2 next)

lemma expTaylorRun_sound {S : ℕ} (hS : 0< S) {a : Box} {x : ℝ}
    (ha : Contains S a x) (n : ℕ) :
    Contains S (expTaylorRun S a n).1 (x^n/(n.factorial:ℝ)) ∧
    Contains S (expTaylorRun S a n).2 (∑ k ∈ range (n+1),x^k/(k.factorial:ℝ)) := by
  induction n with
  | zero => simpa [expTaylorRun] using And.intro (oneBox_sound hS) (oneBox_sound hS)
  | succ n ih =>
    have ht := mulDivBox_sound hS (Nat.succ_pos n) ih.1 ha
    have he : (x^n/(n.factorial:ℝ))*x/((n+1:ℕ):ℝ) = x^(n+1)/((n+1).factorial:ℝ) := by
      rw [Nat.factorial_succ,pow_succ]
      push_cast
      field_simp
    rw [he] at ht
    refine ⟨ht, ?_⟩
    have hs := addBox_sound ih.2 ht
    simpa only [expTaylorRun,sum_range_succ] using hs

noncomputable def expBox (S : ℕ) (a : Box) (N : ℕ) : Box :=
  let b := (expTaylorRun S a N).2
  ⟨b.lo,b.hi+1⟩

lemma expBox_sound {S : ℕ} (hS : 0< S) {a : Box} {x : ℝ}
    (ha : Contains S a x) (hx1 : x≤ 1) (N : ℕ)
    (htail : ((N+2:ℕ):ℝ)/((N+1).factorial*(N+1)) ≤  1/(S:ℝ)) :
    Contains S (expBox S a N) (Real.exp x) := by
  have hx0 := contains_nonneg ha
  have hx : |x|≤ 1 := by rwa [abs_of_nonneg hx0]
  have hsum := (expTaylorRun_sound hS ha N).2
  have hl := Real.sum_le_exp_of_nonneg hx0 (N+1)
  have he := Real.exp_bound hx (Nat.succ_pos N)
  have hp : |x|^(N+1)≤ 1 := pow_le_one₀ (abs_nonneg x) hx
  have hr : Real.exp x-(∑ k ∈ range (N+1),x^k/(k.factorial:ℝ))≤ 1/(S:ℝ) := by
    calc
      _ ≤  |Real.exp x-(∑ k ∈ range (N+1),x^k/(k.factorial:ℝ))| := le_abs_self _
      _ ≤  _ := he
      _ ≤  ((N+2:ℕ):ℝ)/((N+1).factorial*(N+1)) := by
        have hh := mul_le_of_le_one_left
          (by positivity : (0:ℝ)≤ ((N+2:ℕ):ℝ)/((N+1).factorial*(N+1))) hp
        simpa only [Nat.cast_succ,Nat.cast_add,Nat.cast_ofNat] using hh
      _ ≤  _ := htail
  constructor
  · exact hsum.1.trans hl
  · dsimp [expBox]
    push_cast
    rw [add_div]
    linarith [hsum.2]

noncomputable def inverseBox (S : ℕ) (a : Box) : Box :=
  ⟨S*S/a.hi,S*S/a.lo+1⟩

lemma inverseBox_sound {S : ℕ} (hS : 0< S) {a : Box} {x : ℝ}
    (ha : Contains S a x) (hl : 0< a.lo) : Contains S (inverseBox S a) (1/x) := by
  have hSr : (0:ℝ)< S := by exact_mod_cast hS
  have hlr : (0:ℝ)< a.lo := by exact_mod_cast hl
  have hx : 0< x := (div_pos hlr hSr).trans_le ha.1
  have hh : 0< a.hi := by
    by_contra hh
    have hz : a.hi=0 := by omega
    have hhx := ha.2
    simp only [hz,Nat.cast_zero,zero_div] at hhx
    linarith
  have hhr : (0:ℝ)< a.hi := by exact_mod_cast hh
  have hlo := (quotient_bounds (S*S) a.hi hh).1
  have hhi := (quotient_bounds (S*S) a.lo hl).2
  simp only [Nat.cast_mul] at hlo hhi
  constructor
  · calc
      _ ≤  ((S:ℝ)*S/a.hi)/S := div_le_div_of_nonneg_right hlo hSr.le
      _ = 1/((a.hi:ℝ)/S) := by field_simp
      _ ≤  _ := one_div_le_one_div_of_le hx ha.2
  · calc
      _ ≤  1/((a.lo:ℝ)/S) := one_div_le_one_div_of_le (div_pos hlr hSr) ha.1
      _ = ((S:ℝ)*S/a.lo)/S := by field_simp
      _ ≤  _ := div_le_div_of_nonneg_right hhi hSr.le

lemma repeatedSquare_sound {S : ℕ} (hS : 0< S) (n : ℕ) {a : Box} {x : ℝ}
    (ha : Contains S a x) : Contains S (repeatedSquare S n a) (x^(2^n)) := by
  induction n generalizing a x with
  | zero => simpa [repeatedSquare] using ha
  | succ n ih =>
    have hs : Contains S (mulDivBox S 1 a a) (x^2) := by
      simpa [pow_two] using mulDivBox_sound hS (by decide : 0<1) ha ha
    have h := ih hs
    simpa [repeatedSquare,pow_succ,pow_mul,Nat.mul_comm] using h

noncomputable def rationalBox (S m d : ℕ) : Box := ⟨S*m/d,S*m/d+1⟩

lemma rationalBox_sound {S d : ℕ} (hS : 0< S) (hd : 0< d) (m : ℕ) :
    Contains S (rationalBox S m d) ((m:ℝ)/d) := by
  have hSr : (0:ℝ)< S := by exact_mod_cast hS
  have hdr : (0:ℝ)< d := by exact_mod_cast hd
  have h := quotient_bounds (S*m) d hd
  constructor
  · calc
      _ ≤  ((S*m:ℕ):ℝ)/d/S := div_le_div_of_nonneg_right h.1 hSr.le
      _ = (m:ℝ)/d := by push_cast; field_simp
  · calc
      (m:ℝ)/d = ((S*m:ℕ):ℝ)/d/S := by push_cast; field_simp
      _ ≤  _ := div_le_div_of_nonneg_right h.2 hSr.le

end CertifiedFixedPoint

end Height100Module34

section Height100Module35

set_option autoImplicit false
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024
namespace CertifiedFixedPoint
open _root_.CertifiedFixedPoint

noncomputable def expUnit310 (a : Box) : Box := expBox scale310 a 200

lemma expUnit310_sound {a : Box} {x : ℝ} (ha : Contains scale310 a x) (hx : x≤ 1) :
    Contains scale310 (expUnit310 a) (Real.exp x) := by
  apply expBox_sound (by norm_num [scale310]) ha hx 200
  norm_num [scale310,Nat.factorial]

end CertifiedFixedPoint

end Height100Module35

section Height100Module36

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CertifiedThetaPoints
open _root_.CertifiedThetaPoints
open CertifiedFixedPoint
open _root_.CertifiedFixedPoint

noncomputable def center (i : Fin 16) : ℝ := (6*i.val+3)/16

noncomputable def pointInput (i : Fin 16) : Box := rationalBox scale310 (6*i.val+3) 128
noncomputable def pointExp (i : Fin 16) : Box := expUnit310 (pointInput i)
noncomputable def pointExpValues : List Box := List.ofFn pointExp

theorem _root_.RH14MomentEnclosureProof.CertifiedThetaPoints.pointExpCache_correct : CertifiedThetaPoints.pointExpValues = CertifiedThetaPoints.pointExpCache :=
  Eq.refl CertifiedThetaPoints.pointExpCache

lemma cachedPointExp_eq (i : Fin 16) : cachedPointExp i = pointExp i := by
  rw [cachedPointExp,←pointExpCache_correct]
  simp only [pointExpValues,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    dif_pos i.isLt,Option.getD_some]

lemma pointExp_sound (i : Fin 16) :
    Contains scale310 (cachedPointExp i) (Real.exp (center i/8)) := by
  rw [cachedPointExp_eq]
  have ha := rationalBox_sound (by norm_num [scale310] : 0< scale310)
    (by decide : 0<128) (6*i.val+3)
  have he : (((6*i.val+3:ℕ):ℝ)/128) = center i/8 := by
    simp [center]
    ring
  norm_num only [Nat.cast_ofNat] at ha
  rw [he] at ha
  apply expUnit310_sound ha
  have hi : (i.val:ℝ)<16 := by exact_mod_cast i.isLt
  unfold center
  linarith

end CertifiedThetaPoints

end Height100Module36

section Height100Module37

set_option autoImplicit false
set_option maxHeartbeats 0
open Finset
open scoped BigOperators

namespace CertifiedHighPrecisionPi
open _root_.CertifiedHighPrecisionPi

noncomputable def atanSum (x : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ range N, (-1)^n*x^(2*n+1)/(2*n+1)

lemma atan_remainder (x : ℝ) (hx0 : 0≤ x) (hx1 : x<1) (N : ℕ) :
    |Real.arctan x - atanSum x N| ≤  x^(2*N+1)/(1-x^2) := by
  have hx : ‖x‖<1 := by simpa [Real.norm_eq_abs,abs_of_nonneg hx0]
  have hs := Real.hasSum_arctan hx
  have htail : Real.arctan x - atanSum x N =
      ∑' n : ℕ, (-1)^(n+N)*x^(2*(n+N)+1)/(2*(n+N)+1) := by
    have h := hs.summable.sum_add_tsum_nat_add N
    rw [hs.tsum_eq] at h
    exact sub_eq_iff_eq_add.mpr (by simpa [atanSum,add_comm] using h.symm)
  rw [htail, ← Real.norm_eq_abs]
  have hq0 : 0≤ x^2 := sq_nonneg x
  have hq1 : x^2<1 := by nlinarith
  have hgeo := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (x^(2*N+1))
  have he := tsum_of_norm_bounded hgeo (fun n : ℕ => by
    have hd : (1:ℝ)≤ 2*(n+N)+1 := by
      have hn : (0:ℝ)≤ n := Nat.cast_nonneg n
      have hN : (0:ℝ)≤ N := Nat.cast_nonneg N
      linarith
    calc
      ‖(-1:ℝ)^(n+N)*x^(2*(n+N)+1)/(2*(n+N)+1)‖ =
          x^(2*(n+N)+1)/(2*(n+N)+1) := by
        simp [norm_div,norm_mul,norm_pow,Real.norm_eq_abs,abs_of_nonneg hx0,
          abs_of_nonneg (by positivity : (0:ℝ)≤ 2*(n+N)+1)]
      _ ≤  x^(2*(n+N)+1) := div_le_self (by positivity) hd
      _ = x^(2*N+1)*(x^2)^n := by
        rw [show 2*(n+N)+1=(2*N+1)+2*n by ring,pow_add,pow_mul])
  simpa only [div_eq_mul_inv] using he

noncomputable def rationalAtanSum (x : ℚ) (N : ℕ) : ℚ :=
  ∑ n ∈ range N, (-1)^n*x^(2*n+1)/(2*n+1)

lemma rationalAtanSum_cast (x : ℚ) (N : ℕ) :
    (rationalAtanSum x N : ℝ) = atanSum x N := by
  simp [rationalAtanSum,atanSum]

noncomputable def machinApprox (N M : ℕ) : ℚ :=
  16*rationalAtanSum (1/5) N - 4*rationalAtanSum (1/239) M

lemma machin_error (N M : ℕ) :
    |Real.pi-(machinApprox N M:ℝ)| ≤ 
      16*((1/5:ℝ)^(2*N+1)/(1-(1/5:ℝ)^2)) +
        4*((1/239:ℝ)^(2*M+1)/(1-(1/239:ℝ)^2)) := by
  have h5 := atan_remainder (1/5) (by norm_num) (by norm_num) N
  have h239 := atan_remainder (1/239) (by norm_num) (by norm_num) M
  have hm : Real.pi = 16*Real.arctan (1/5)-4*Real.arctan (1/239) := by
    have h := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
    norm_num at h
    linarith
  rw [hm,machinApprox]
  push_cast
  rw [rationalAtanSum_cast,rationalAtanSum_cast]
  calc
    _ = |16*(Real.arctan (1/5)-atanSum (1/5) N) -
        4*(Real.arctan (1/239)-atanSum (1/239) M)| := by congr 1; ring
    _ ≤  |16*(Real.arctan (1/5)-atanSum (1/5) N)| +
        |4*(Real.arctan (1/239)-atanSum (1/239) M)| := abs_sub _ _
    _ ≤  _ := by
      rw [abs_mul,abs_mul]
      norm_num at h5 h239 ⊢
      linarith

end CertifiedHighPrecisionPi

end Height100Module37

section Height100Module38

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 1024
set_option Elab.async false

namespace CertifiedHighPrecisionPi
open _root_.CertifiedHighPrecisionPi

lemma machin_error_320 : |Real.pi-(machinApprox 230 70:ℝ)|≤ 1/10^320 := by
  apply (machin_error 230 70).trans
  norm_num

lemma machin_lower_check : (piFloor310:ℚ)/10^310 + 1/10^320 ≤  machinApprox 230 70 := by
  decide +kernel

lemma machin_upper_check : machinApprox 230 70 + 1/10^320 ≤  (piFloor310+1:ℚ)/10^310 := by
  decide +kernel

theorem pi_enclosure_310 :
    (piFloor310:ℝ)/10^310 ≤  Real.pi ∧ Real.pi ≤  (piFloor310+1:ℝ)/10^310 := by
  have hl : (piFloor310:ℝ)/10^310 + 1/10^320 ≤  (machinApprox 230 70:ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr machin_lower_check
    push_cast at h
    exact h
  have hu : (machinApprox 230 70:ℝ) + 1/10^320 ≤  (piFloor310+1:ℝ)/10^310 := by
    have h := (Rat.cast_le (K := ℝ)).mpr machin_upper_check
    push_cast at h
    exact h
  have he := abs_le.mp machin_error_320
  constructor <;> linarith

end CertifiedHighPrecisionPi

end Height100Module38

section Height100Module39

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CertifiedFixedPoint
open _root_.CertifiedFixedPoint

noncomputable def divideBox (d : ℕ) (a : Box) : Box := ⟨a.lo/d,a.hi/d+1⟩

lemma scaleBox_sound {S : ℕ} (m : ℕ) {a : Box} {x : ℝ}
    (ha : Contains S a x) : Contains S (scaleBox m a) ((m:ℝ)*x) := by
  constructor <;> dsimp [scaleBox]
  · push_cast
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left ha.1 (Nat.cast_nonneg m)
  · push_cast
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left ha.2 (Nat.cast_nonneg m)

lemma divideBox_sound {S d : ℕ} (hS : 0< S) (hd : 0< d)
    {a : Box} {x : ℝ} (ha : Contains S a x) :
    Contains S (divideBox d a) (x/d) := by
  have hSr : (0:ℝ)< S := by exact_mod_cast hS
  have hdr : (0:ℝ)< d := by exact_mod_cast hd
  constructor
  · calc
      _ ≤  ((a.lo:ℝ)/d)/S := div_le_div_of_nonneg_right (quotient_bounds a.lo d hd).1 hSr.le
      _ = ((a.lo:ℝ)/S)/d := by ring
      _ ≤  _ := div_le_div_of_nonneg_right ha.1 hdr.le
  · calc
      _ ≤  ((a.hi:ℝ)/S)/d := div_le_div_of_nonneg_right ha.2 hdr.le
      _ = ((a.hi:ℝ)/d)/S := by ring
      _ ≤  _ := div_le_div_of_nonneg_right (quotient_bounds a.hi d hd).2 hSr.le

lemma expTaylorRun_sum_lower (S : ℕ) (a : Box) (n : ℕ) :
    S≤ (expTaylorRun S a n).2.lo := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact ih.trans (Nat.le_add_right _ _)

lemma expUnit310_lo_pos (a : Box) : 0<(expUnit310 a).lo := by
  have h := expTaylorRun_sum_lower scale310 a 200
  exact (by norm_num [scale310] : 0< scale310).trans_le h

noncomputable def expNegative310 (a : Box) : Box :=
  repeatedSquare scale310 10 (inverseBox scale310 (expUnit310 (divideBox 1024 a)))

lemma expNegative310_sound {a : Box} {x : ℝ}
    (ha : Contains scale310 a x) (hx : x≤ 1024) :
    Contains scale310 (expNegative310 a) (Real.exp (-x)) := by
  have hS : 0< scale310 := by norm_num [scale310]
  have hq := divideBox_sound hS (by decide : 0<1024) ha
  have he := expUnit310_sound hq (by norm_num; linarith)
  have hi := inverseBox_sound hS he (expUnit310_lo_pos _)
  have hp := repeatedSquare_sound hS 10 hi
  have hv : (1/Real.exp (x/1024))^(1024:ℕ) = Real.exp (-x) := by
    rw [one_div,←Real.exp_neg,←Real.exp_nat_mul]
    norm_num
    ring
  norm_num only [Nat.cast_ofNat] at hp
  simpa only [expNegative310,hv] using hp

end CertifiedFixedPoint

end Height100Module39

section Height100Module40

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option exponentiation.threshold 1024

namespace CertifiedThetaPoints
open _root_.CertifiedThetaPoints
open CertifiedFixedPoint CertifiedHighPrecisionPi
open _root_.CertifiedFixedPoint _root_.CertifiedHighPrecisionPi

noncomputable def quarterExpBox (i : Fin 16) : Box := repeatedSquare scale310 1 (cachedPointExp i)
noncomputable def lambda (i : Fin 16) (n : Fin 8) : ℝ :=
  Real.pi*(n.val+1:ℝ)^2*Real.exp (center i)

noncomputable instance (i : Fin 16) (n : Fin 8) : Decidable (active i n) := inferInstanceAs
  (Decidable ((lambdaBox i n).lo < 800*scale310))

lemma piBox_sound : Contains scale310 piBox Real.pi := by
  simpa only [Contains,piBox,scale310,Nat.cast_add,Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat] using pi_enclosure_310

lemma centerExpBox_sound (i : Fin 16) :
    Contains scale310 (centerExpBox i) (Real.exp (center i)) := by
  have h := repeatedSquare_sound (by norm_num [scale310] : 0< scale310) 3 (pointExp_sound i)
  have he : (Real.exp (center i/8))^(2^3)=Real.exp (center i) := by
    rw [←Real.exp_nat_mul]
    norm_num
    ring
  simpa only [centerExpBox,he] using h

lemma quarterExpBox_sound (i : Fin 16) :
    Contains scale310 (quarterExpBox i) (Real.exp (center i/4)) := by
  have h := repeatedSquare_sound (by norm_num [scale310] : 0< scale310) 1 (pointExp_sound i)
  have he : (Real.exp (center i/8))^(2^1)=Real.exp (center i/4) := by
    rw [←Real.exp_nat_mul]
    norm_num
    ring
  simpa only [quarterExpBox,he] using h

lemma lambdaBox_sound (i : Fin 16) (n : Fin 8) :
    Contains scale310 (lambdaBox i n) (lambda i n) := by
  have h := scaleBox_sound ((n.val+1)^2)
    (mulDivBox_sound (by norm_num [scale310] : 0< scale310) (by decide : 0<1)
      piBox_sound (centerExpBox_sound i))
  simpa [lambdaBox,lambda,mul_comm,mul_left_comm,mul_assoc] using h

lemma active_bound_check : ∀ i : Fin 16, ∀ n : Fin 8,
    active i n → (lambdaBox i n).hi ≤  1024*scale310 := by decide +kernel

lemma active_lambda_le (i : Fin 16) (n : Fin 8) (h : active i n) : lambda i n≤ 1024 := by
  have hb := (lambdaBox_sound i n).2
  have hc := active_bound_check i n h
  have hSr : (0:ℝ)< scale310 := by norm_num [scale310]
  have he : ((lambdaBox i n).hi:ℝ)/scale310 ≤  1024 := by
    apply (div_le_iff₀ hSr).mpr
    exact_mod_cast hc
  exact hb.trans he

lemma inactive_lambda_ge (i : Fin 16) (n : Fin 8) (h : ¬active i n) : 800≤ lambda i n := by
  have hb := (lambdaBox_sound i n).1
  have hc : 800*scale310 ≤  (lambdaBox i n).lo := Nat.le_of_not_gt h
  have hSr : (0:ℝ)< scale310 := by norm_num [scale310]
  have he : (800:ℝ) ≤  ((lambdaBox i n).lo:ℝ)/scale310 := by
    apply (le_div_iff₀ hSr).mpr
    exact_mod_cast hc
  exact he.trans hb

noncomputable def thetaInitialBox (i : Fin 16) (n : Fin 8) : Box :=
  if active i n then expNegative310 (lambdaBox i n) else ⟨0,0⟩

noncomputable def fullInitialBox (i : Fin 16) (n : Fin 8) : Box :=
  scaleBox 2 (mulDivBox scale310 1 (quarterExpBox i) (thetaInitialBox i n))

lemma thetaInitialBox_sound (i : Fin 16) (n : Fin 8) (h : active i n) :
    Contains scale310 (thetaInitialBox i n) (Real.exp (-lambda i n)) := by
  rw [thetaInitialBox,if_pos h]
  exact expNegative310_sound (lambdaBox_sound i n) (active_lambda_le i n h)

lemma fullInitialBox_sound (i : Fin 16) (n : Fin 8) (h : active i n) :
    Contains scale310 (fullInitialBox i n) (2*Real.exp (center i/4-lambda i n)) := by
  have he := mulDivBox_sound (by norm_num [scale310] : 0< scale310) (by decide : 0<1)
    (quarterExpBox_sound i) (thetaInitialBox_sound i n h)
  have hs := scaleBox_sound 2 he
  simpa [fullInitialBox,←Real.exp_add,sub_eq_add_neg] using hs

end CertifiedThetaPoints

end Height100Module40

section Height100Module41

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CertifiedThetaPoints
open _root_.CertifiedThetaPoints
open CertifiedFixedPoint
open _root_.CertifiedFixedPoint

noncomputable def initialValues : List (List Box) := List.ofFn (fun i : Fin 16 => List.ofFn (fullInitialBox i))

theorem _root_.RH14MomentEnclosureProof.CertifiedThetaPoints.initialCache_correct : CertifiedThetaPoints.initialValues = CertifiedThetaPoints.initialCache :=
  Eq.refl CertifiedThetaPoints.initialCache

lemma cachedInitial_eq (i : Fin 16) (n : Fin 8) : cachedInitial i n=fullInitialBox i n := by
  rw [cachedInitial,←initialCache_correct]
  simp only [initialValues,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    dif_pos i.isLt,dif_pos n.isLt,Option.getD_some]

lemma cachedInitial_sound (i : Fin 16) (n : Fin 8) (h : active i n) :
    Contains scale310 (cachedInitial i n) (2*Real.exp (center i/4-lambda i n)) := by
  rw [cachedInitial_eq]
  exact fullInitialBox_sound i n h

end CertifiedThetaPoints

end Height100Module41

section Height100Module42

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CertifiedThetaCandidates
open _root_.CertifiedThetaCandidates
open CertifiedThetaPoints CertifiedFixedPoint
open _root_.CertifiedThetaPoints _root_.CertifiedFixedPoint

end CertifiedThetaCandidates

end Height100Module42

section Height100Module43

namespace CertifiedStreamingODE
open _root_.CertifiedStreamingODE
open CertifiedSignedODEConvolution
open _root_.CertifiedSignedODEConvolution

lemma digit_shift (bits p j : ℕ) : digit bits (p>>>bits) j=digit bits p (j+1) := by
  unfold digit
  rw [←Nat.shiftRight_add]
  congr 2
  simp [Nat.mul_add,add_comm]

lemma tail_getD {α : Type*} (xs : List α) (j : ℕ) (d : α) :
    xs.tail.getD j d=xs.getD (j+1) d := by
  cases xs <;> simp

/-- The streaming checker verifies each coefficient inequality while consuming
each list and each packed integer exactly once. -/
theorem checkSteps_sound (bits D i n : ℕ) (fs : List ℤ) (ss : List ℕ)
    (pp pm pe pr : ℕ) (hc : checkSteps bits D i n fs ss pp pm pe pr=true) :
    ∀ j< n,
      (((i+j+1:ℕ):ℤ)*fs.getD j 0*D+(digit bits pp j:ℤ)-(digit bits pm j:ℤ)).natAbs+
        digit bits pe j+digit bits pr j≤ (i+j+1)*ss.getD j 0*D := by
  induction n generalizing i fs ss pp pm pe pr with
  | zero => intro j hj; omega
  | succ n ih =>
    simp only [checkSteps,Bool.and_eq_true,decide_eq_true_eq] at hc
    obtain ⟨hhead,htail⟩ := hc
    intro j hj
    cases j with
    | zero =>
      simpa only [digit,Nat.mul_zero,Nat.shiftRight_zero,Nat.add_zero,Nat.cast_add,
        Nat.cast_one,Int.natCast_emod,Nat.cast_pow,Nat.cast_ofNat,List.headD_eq_getD] using hhead
    | succ j =>
      have h := ih (i+1) fs.tail ss.tail (pp>>>bits) (pm>>>bits) (pe>>>bits) (pr>>>bits)
        htail j (by omega)
      simpa only [digit_shift,tail_getD,Nat.succ_eq_add_one,add_assoc,add_left_comm] using h

end CertifiedStreamingODE

end Height100Module43

section Height100Module44

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CertifiedJetRecords
open _root_.CertifiedJetRecords
open CertifiedThetaCandidates CertifiedThetaPoints CertifiedFixedPoint
open _root_.CertifiedThetaCandidates _root_.CertifiedThetaPoints _root_.CertifiedFixedPoint
open CertifiedListODEVectors CertifiedPackedConvolution CertifiedStreamingODE
open _root_.CertifiedListODEVectors _root_.CertifiedPackedConvolution _root_.CertifiedStreamingODE

end CertifiedJetRecords

end Height100Module44

section Height100Module45
namespace CertifiedJetRecords
open _root_.CertifiedJetRecords
open _root_.CertifiedJetRecords
theorem records_checked (i : Fin 16) (n : Fin 8)
    (ha : _root_.CertifiedThetaPoints.active i n) : checkRecord i n (recordAt i n)=true :=
  TaoFivePrimes.rh14to100_theta_checks i n ha
end CertifiedJetRecords
end Height100Module45

section Height100Module46

end Height100Module46

section Height100Module47

namespace CertifiedJetRecords
open _root_.CertifiedJetRecords

lemma checkInputs_head (D p limit j : ℕ) (e : Entry) (es : List Entry)
    (hc : checkInputs D p limit j (e::es)=true) : entryCondition D p limit j e := by
  have h := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).1
  exact of_decide_eq_true h

lemma checkInputs_tail (D p limit j : ℕ) (e : Entry) (es : List Entry)
    (hc : checkInputs D p limit j (e::es)=true) : checkInputs D p limit (j+1) es=true :=
  (Bool.and_eq_true_iff.mp hc).2

lemma checkInputs_next (D p limit j : ℕ) (e f : Entry) (es : List Entry)
    (hc : checkInputs D p limit j (e::f::es)=true) : nextCondition j e f := by
  have h := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).2
  exact of_decide_eq_true h

theorem checkInputs_entry (D p limit j : ℕ) (es : List Entry)
    (hc : checkInputs D p limit j es=true) :
    ∀ k< es.length, entryCondition D p limit (j+k) (es.getD k zeroEntry) := by
  induction es generalizing j with
  | nil => intro k hk; simp at hk
  | cons e es ih =>
    intro k hk
    cases k with
    | zero => simpa using checkInputs_head D p limit j e es hc
    | succ k =>
      have h := ih (j+1) (checkInputs_tail D p limit j e es hc) k (by simpa using hk)
      change entryCondition D p limit (j+(k+1)) (es.getD k zeroEntry)
      simpa only [add_assoc,add_comm,add_left_comm] using h

theorem checkInputs_adjacent (D p limit j : ℕ) (es : List Entry)
    (hc : checkInputs D p limit j es=true) :
    ∀ k, k+1< es.length → nextCondition (j+k) (es.getD k zeroEntry) (es.getD (k+1) zeroEntry) := by
  induction es generalizing j with
  | nil => intro k hk; simp at hk
  | cons e es ih =>
    intro k hk
    cases k with
    | zero =>
      cases es with
      | nil => simp at hk
      | cons f es => simpa using checkInputs_next D p limit j e f es hc
    | succ k =>
      have h := ih (j+1) (checkInputs_tail D p limit j e es hc) k (by simpa using hk)
      change nextCondition (j+(k+1)) (es.getD k zeroEntry) (es.getD (k+1) zeroEntry)
      simpa only [add_assoc,add_comm,add_left_comm] using h

end CertifiedJetRecords

end Height100Module47

section Height100Module48

set_option autoImplicit false
namespace CertifiedJetRecords
open _root_.CertifiedJetRecords
open CertifiedFixedPoint CertifiedThetaPoints CertifiedSignedODEConvolution
open _root_.CertifiedFixedPoint _root_.CertifiedThetaPoints _root_.CertifiedSignedODEConvolution
open CertifiedListODEVectors CertifiedStreamingODE CertifiedIntegerExponentialJets
open _root_.CertifiedListODEVectors _root_.CertifiedStreamingODE _root_.CertifiedIntegerExponentialJets

noncomputable def Record.G (d : Record) (j : ℕ) : ℤ := d.gs.getD j 0
open _root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record
noncomputable def Record.F (d : Record) (j : ℕ) : ℤ := d.fs.getD j 0
noncomputable def Record.R (d : Record) (j : ℕ) : ℕ := d.rs.getD j 0
noncomputable def Record.S (d : Record) (j : ℕ) : ℕ := d.ss.getD j 0

theorem checkRecord_conditions (i : Fin 16) (n : Fin 8) (d : Record)
    (hc : checkRecord i n d=true) :
    initialCondition i n d ∧ checkInputs scale310 i.val (10^75) 0 d.entries=true ∧
    d.gs.tail.all (fun g => decide (g≤ 0))=true ∧ carryCondition d ∧ productCondition d ∧
    checkSteps bits scale310 0 (precision-1) d.fs.tail d.ss.tail d.pp d.pm d.pe d.pr=true := by
  simpa only [checkRecord,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using hc

theorem checked_record_ode (i : Fin 16) (n : Fin 8) (d : Record)
    (hc : checkRecord i n d=true) (j : ℕ) (hj : j+1<184) :
    |integerResidual scale310 (_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.G d) (_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.F d) j|+integerErrorSum (_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.G d) (_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.F d) (_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.R d) (_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.S d) j ≤ 
      (j+1:ℤ)*(_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.S d) (j+1)*scale310 := by
  obtain ⟨_hi,_hin,hsign,hcarry,hprod,hstream⟩ := checkRecord_conditions i n d hc
  obtain ⟨hcp,hcm,hce,hcr⟩ := hcarry
  obtain ⟨hpp,hpm,hpe,hpr⟩ := hprod
  have hj' : j< precision-1 := by dsimp [precision]; omega
  have hlen : d.fs.length=d.ss.length := by simp [Record.fs,Record.ss]
  have hp : digit bits d.pp j=conv (absDerivative (_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.G d)) (positive (_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.F d)) j := by
    rw [hpp,lowProduct,Nat.shiftLeft_eq',Nat.shiftLeft_eq,one_mul,digit_truncate bits _ _ j hj']
    apply digit_lists _ _ _ _ _ _ _ _ hcp
    · intro k hk
      simp only [Record.ad,absDerivativeList_getD,absDerivative,Record.G]
    · intro k hk
      simp only [Record.fp,positiveList_getD,positive,Record.F]
  have hm : digit bits d.pm j=conv (absDerivative (_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.G d)) (negative (_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.F d)) j := by
    rw [hpm,lowProduct,Nat.shiftLeft_eq',Nat.shiftLeft_eq,one_mul,digit_truncate bits _ _ j hj']
    apply digit_lists _ _ _ _ _ _ _ _ hcm
    · intro k hk
      simp only [Record.ad,absDerivativeList_getD,absDerivative,Record.G]
    · intro k hk
      simp only [Record.fm,negativeList_getD,negative,Record.F]
  have he : digit bits d.pe j=conv (absDerivative (_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.G d)) (_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.S d) j := by
    rw [hpe,lowProduct,Nat.shiftLeft_eq',Nat.shiftLeft_eq,one_mul,digit_truncate bits _ _ j hj']
    apply digit_lists _ _ _ _ _ _ _ _ hce
    · intro k hk
      simp only [Record.ad,absDerivativeList_getD,absDerivative,Record.G]
    · intro k hk
      rfl
  have hr : digit bits d.pr j=conv (radiusDerivative (_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.R d)) (fun k => ((_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.F d) k).natAbs+(_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.S d) k) j := by
    rw [hpr,lowProduct,Nat.shiftLeft_eq',Nat.shiftLeft_eq,one_mul,digit_truncate bits _ _ j hj']
    apply digit_lists _ _ _ _ _ _ _ _ hcr
    · intro k hk
      simp only [Record.rd,radiusDerivativeList_getD,radiusDerivative,Record.R]
    · intro k hk
      simp only [Record.fr,radiusFactorList_getD _ _ hlen,Record.F,Record.S]
  have hneg : ∀ k, k≤ j → (_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.G d) (k+1)≤ 0 := by
    intro k hk
    have hh := list_all_nonpos d.gs.tail hsign k
    simpa only [CertifiedListODEVectors.getD_tail,Record.G] using hh
  apply residual_check_of_convolutions scale310 (_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.G d) (_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.F d) (_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.R d) (_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.S d) j
    (digit bits d.pp j) (digit bits d.pm j) (digit bits d.pe j) (digit bits d.pr j)
    hneg hp hm he hr
  have hh := checkSteps_sound bits scale310 0 (precision-1) d.fs.tail d.ss.tail
    d.pp d.pm d.pe d.pr hstream j hj'
  simpa only [zero_add,Nat.cast_add,Nat.cast_one,CertifiedStreamingODE.tail_getD,Record.F,Record.S] using hh

end CertifiedJetRecords

end Height100Module48

section Height100Module49

set_option autoImplicit false
namespace CertifiedFixedPoint
open _root_.CertifiedFixedPoint

lemma rationalStep_sound {S d : ℕ} (hS : 0< S) (hd : 0< d) (p : ℕ)
    {a b : Box} {x : ℝ} (ha : Contains S a x)
    (hl : b.lo*d≤ p*a.lo) (hh : p*a.hi≤ b.hi*d) :
    Contains S b ((p:ℝ)*x/d) := by
  have hSr : (0:ℝ)< S := by exact_mod_cast hS
  have hdr : (0:ℝ)< d := by exact_mod_cast hd
  have hlr : (b.lo:ℝ)≤ (p:ℝ)*a.lo/d := by
    apply (le_div_iff₀ hdr).mpr
    exact_mod_cast hl
  have hhr : (p:ℝ)*a.hi/d≤ (b.hi:ℝ) := by
    apply (div_le_iff₀ hdr).mpr
    exact_mod_cast hh
  constructor
  · calc
      _ ≤  ((p:ℝ)*a.lo/d)/S := div_le_div_of_nonneg_right hlr hSr.le
      _ = (p:ℝ)*((a.lo:ℝ)/S)/d := by ring
      _ ≤  _ := by gcongr; exact ha.1
  · calc
      _ ≤  (p:ℝ)*((a.hi:ℝ)/S)/d := by gcongr; exact ha.2
      _ = ((p:ℝ)*a.hi/d)/S := by ring
      _ ≤  _ := div_le_div_of_nonneg_right hhr hSr.le

/-- Linear integer inequalities certify a whole normalized power jet. The
proposed boxes may be generated by any method; their construction is not trusted. -/
theorem powerJet_enclosure {S d : ℕ} (hS : 0< S) (hd : 0< d) (p N : ℕ)
    (b : ℕ → Box) (x : ℝ) (h0 : Contains S (b 0) x)
    (hstep : ∀ j, j+1< N →
      (b (j+1)).lo*(d*(j+1))≤ p*(b j).lo ∧
      p*(b j).hi≤ (b (j+1)).hi*(d*(j+1))) :
    ∀ j< N, Contains S (b j) (x*((p:ℝ)/d)^j/(j.factorial:ℝ)) := by
  intro j
  induction j with
  | zero => intro hj; simpa using h0
  | succ j ih =>
    intro hj
    have hc := hstep j hj
    have hs := rationalStep_sound hS (Nat.mul_pos hd (Nat.succ_pos j)) p
      (ih (by omega)) hc.1 hc.2
    convert hs using 1
    push_cast
    rw [Nat.factorial_succ,pow_succ]
    push_cast
    field_simp

end CertifiedFixedPoint

end Height100Module49

section Height100Module50

open Complex Metric Real
namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature

noncomputable def thetaTerm (n : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (-(Real.pi:ℂ)*(n+1)^2*Complex.exp z)

end CertifiedZetaQuadrature

end Height100Module50

section Height100Module51

open Complex Metric Finset
namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature
set_option exponentiation.threshold 512
open CertifiedTaylorQuadrature CertifiedMomentConvolution
open _root_.CertifiedTaylorQuadrature _root_.CertifiedMomentConvolution

noncomputable def fullThetaTerm (n : ℕ) (z : ℂ) : ℂ :=
  2*Complex.exp (z/4-(Real.pi:ℂ)*(n+1)^2*Complex.exp z)

lemma fullThetaTerm_factor (n : ℕ) (z : ℂ) :
    fullThetaTerm n z=2*Complex.exp (z/4)*thetaTerm n z := by
  unfold fullThetaTerm thetaTerm
  rw [show z/4-(Real.pi:ℂ)*(n+1)^2*Complex.exp z =
    z/4+(-(Real.pi:ℂ)*(n+1)^2*Complex.exp z) by ring,Complex.exp_add]
  ring

lemma fullThetaTerm_entire (n : ℕ) : Differentiable ℂ (fullThetaTerm n) := by
  unfold fullThetaTerm
  fun_prop

noncomputable def baseKernel (z : ℂ) : ℂ := ∑ n ∈ range 8, fullThetaTerm n z

lemma baseKernel_entire : Differentiable ℂ baseKernel := by
  unfold baseKernel fullThetaTerm
  fun_prop

lemma baseKernel_eq (z : ℂ) : baseKernel z=2*Complex.exp (z/4)*thetaTruncation z := by
  unfold baseKernel
  simp_rw [fullThetaTerm_factor]
  rw [← mul_sum]
  rfl

lemma globalKernelMoment_base (k : ℕ) (z : ℂ) :
    globalKernelMoment k z=((64*z)^k/(k.factorial:ℂ))*baseKernel z := by
  rw [baseKernel_eq]
  unfold globalKernelMoment
  ring

end CertifiedZetaQuadrature

end Height100Module51

section Height100Module52

open Complex Finset
namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature
open CertifiedTaylorQuadrature CertifiedMomentConvolution CertifiedExponentialJets
open _root_.CertifiedTaylorQuadrature _root_.CertifiedMomentConvolution _root_.CertifiedExponentialJets

noncomputable def thetaExponent (m : ℕ) (z : ℂ) : ℂ :=
  z/4-(Real.pi:ℂ)*(m+1)^2*Complex.exp z

lemma thetaExponent_entire (m : ℕ) : Differentiable ℂ (thetaExponent m) := by
  unfold thetaExponent
  fun_prop

lemma scaled_linear_quarter (c h : ℂ) (j : ℕ) :
    scaledCoefficient (fun z : ℂ => z/4) c h j =
      if j=0 then c/4 else if j=1 then h/4 else 0 := by
  unfold scaledCoefficient coefficient
  rw [iteratedDeriv_div_const,iteratedDeriv_fun_id]
  rcases j with _|j
  · simp
  rcases j with _|j
  · simp; ring
  · simp

lemma scaled_const_exp (a c h : ℂ) (j : ℕ) :
    scaledCoefficient (fun z => a*Complex.exp z) c h j =
      a*Complex.exp c*h^j/(j.factorial:ℂ) := by
  unfold scaledCoefficient coefficient
  rw [iteratedDeriv_const_mul_field]
  simp only [iteratedDeriv_eq_iterate,Complex.iter_deriv_exp]
  ring

lemma thetaExponent_scaled (m j : ℕ) (c h : ℝ) :
    scaledCoefficient (thetaExponent m) c h j =
      (if j=0 then (c:ℂ)/4 else if j=1 then (h:ℂ)/4 else 0) -
        ((Real.pi*(m+1:ℝ)^2*Real.exp c:ℝ):ℂ)*(h:ℂ)^j/(j.factorial:ℂ) := by
  have hlin : Differentiable ℂ (fun z : ℂ => z/4) := by fun_prop
  have hexp : Differentiable ℂ (fun z : ℂ => (Real.pi:ℂ)*(m+1)^2*Complex.exp z) := by fun_prop
  have hsplit : scaledCoefficient (thetaExponent m) c h j =
      scaledCoefficient (fun z : ℂ => z/4) c h j-
      scaledCoefficient (fun z : ℂ => (Real.pi:ℂ)*(m+1)^2*Complex.exp z) c h j := by
    unfold scaledCoefficient thetaExponent
    rw [CertifiedComplexTaylor.coefficient_sub _ _ hlin hexp]
    ring
  rw [hsplit,scaled_linear_quarter,scaled_const_exp]
  push_cast
  ring

lemma fullThetaTerm_scaled (m : ℕ) (c h : ℂ) (j : ℕ) :
    scaledCoefficient (fullThetaTerm m) c h j =
      2*scaledCoefficient (fun z => Complex.exp (thetaExponent m z)) c h j := by
  unfold scaledCoefficient coefficient fullThetaTerm thetaExponent
  rw [iteratedDeriv_const_mul_field]
  ring

lemma fullThetaTerm_ode (m : ℕ) (c h : ℂ) (n : ℕ) :
    (n+1:ℂ)*scaledCoefficient (fullThetaTerm m) c h (n+1)=
      ∑ k ∈ range (n+1), (k+1:ℂ)*scaledCoefficient (thetaExponent m) c h (k+1)*
        scaledCoefficient (fullThetaTerm m) c h (n-k) := by
  simp_rw [fullThetaTerm_scaled]
  have hr := scaled_exp_coefficient_recurrence (thetaExponent m) (thetaExponent_entire m) c h n
  have h2 := congrArg (fun z : ℂ => 2*z) hr
  rw [mul_sum] at h2
  convert! h2 using 1
  · ring
  · apply sum_congr rfl
    intro k _
    ring

end CertifiedZetaQuadrature

end Height100Module52

section Height100Module53

open Complex Finset
namespace CertifiedJetRecords
open _root_.CertifiedJetRecords
open CertifiedFixedPoint CertifiedThetaPoints CertifiedIntegerExponentialJets
open _root_.CertifiedFixedPoint _root_.CertifiedThetaPoints _root_.CertifiedIntegerExponentialJets
open CertifiedZetaQuadrature CertifiedMomentConvolution CertifiedTaylorQuadrature
open _root_.CertifiedZetaQuadrature _root_.CertifiedMomentConvolution _root_.CertifiedTaylorQuadrature

noncomputable def Record.E (d : Record) (j : ℕ) : Entry := d.entries.getD j zeroEntry
noncomputable def Record.lambdaJet (d : Record) (j : ℕ) : Box := ⟨((_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.E d) j).lo,((_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.E d) j).hi⟩

lemma Record.E_g (d : Record) (j : ℕ) : ((_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.E d) j).g=(_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.G d) j :=
  (List.getD_map d.entries zeroEntry Entry.g).symm
lemma Record.E_r (d : Record) (j : ℕ) : ((_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.E d) j).r=(_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.R d) j :=
  (List.getD_map d.entries zeroEntry Entry.r).symm
lemma Record.E_f (d : Record) (j : ℕ) : ((_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.E d) j).f=(_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.F d) j :=
  (List.getD_map d.entries zeroEntry Entry.f).symm
lemma Record.E_s (d : Record) (j : ℕ) : ((_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.E d) j).s=(_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.S d) j :=
  (List.getD_map d.entries zeroEntry Entry.s).symm

lemma checked_record_entry (i : Fin 16) (n : Fin 8) (d : Record)
    (hc : checkRecord i n d=true) (j : ℕ) (hj : j<184) :
    entryCondition scale310 i.val (10^75) j ((_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.E d) j) := by
  obtain ⟨hinit,hinputs,_⟩ := checkRecord_conditions i n d hc
  have hlen := hinit.1
  have h := checkInputs_entry scale310 i.val (10^75) 0 d.entries hinputs j (by omega)
  simpa only [zero_add,Record.E] using h

lemma checked_record_lambda (i : Fin 16) (n : Fin 8) (d : Record)
    (hc : checkRecord i n d=true) (j : ℕ) (hj : j<184) :
    Contains scale310 ((_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.lambdaJet d) j) (lambda i n*(3/16:ℝ)^j/(j.factorial:ℝ)) := by
  obtain ⟨hinit,hinputs,_⟩ := checkRecord_conditions i n d hc
  obtain ⟨hlen,hlo,hhi,_⟩ := hinit
  have hD : 0< scale310 := by norm_num [scale310]
  have hDr : (0:ℝ)< scale310 := by exact_mod_cast hD
  have hstart : Contains scale310 ((_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.lambdaJet d) 0) (lambda i n) := by
    have hl := (lambdaBox_sound i n).1
    have hh := (lambdaBox_sound i n).2
    have hel : ((_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.E d) 0).lo≤ (lambdaBox i n).lo := by
      simpa only [Record.E,←List.headD_eq_getD] using hlo
    have heh : (lambdaBox i n).hi≤ ((_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.E d) 0).hi := by
      simpa only [Record.E,←List.headD_eq_getD] using hhi
    constructor
    · exact (div_le_div_of_nonneg_right (by exact_mod_cast hel) hDr.le).trans hl
    · exact hh.trans (div_le_div_of_nonneg_right (by exact_mod_cast heh) hDr.le)
  apply powerJet_enclosure hD (by decide : 0<16) 3 184 (_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.lambdaJet d) (lambda i n) hstart _ j hj
  intro k hk
  have h := checkInputs_adjacent scale310 i.val (10^75) 0 d.entries hinputs k (by omega)
  simpa only [zero_add,Record.lambdaJet,Record.E,nextCondition] using h

noncomputable def quarterCoefficient (p j : ℕ) : ℝ :=
  if j=0 then (6*p+3)/64 else if j=1 then 3/64 else 0

lemma quotient_scaled_bounds (D m : ℕ) (hD : 0< D) :
    ((D*m/64:ℕ):ℝ)/D≤ (m:ℝ)/64 ∧
      (m:ℝ)/64≤ ((D*m/64+1:ℕ):ℝ)/D := by
  have h := quotient_bounds (D*m) 64 (by decide)
  have hDr : (0:ℝ)< D := by exact_mod_cast hD
  constructor
  · apply (div_le_iff₀ hDr).mpr
    calc
      _ ≤  ((D*m:ℕ):ℝ)/64 := h.1
      _ = _ := by push_cast; ring
  · apply (le_div_iff₀ hDr).mpr
    calc
      _ = ((D*m:ℕ):ℝ)/64 := by push_cast; ring
      _ ≤  _ := h.2

lemma offset_scaled_bounds (D p j : ℕ) (hD : 0< D) :
    (offset D p j:ℝ)/D≤ quarterCoefficient p j ∧
      quarterCoefficient p j≤ ((offset D p j:ℝ)+1)/D := by
  unfold offset quarterCoefficient
  by_cases hj0 : j=0
  · simp only [if_pos hj0]
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using
      quotient_scaled_bounds D (6*p+3) hD
  · simp only [if_neg hj0]
    by_cases hj1 : j=1
    · simp only [if_pos hj1]
      simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] using quotient_scaled_bounds D 3 hD
    · simp only [if_neg hj1,Nat.cast_zero,zero_div,zero_add]
      constructor
      · rfl
      · positivity

lemma entry_exponent_error (D p j : ℕ) (hD : 0< D) (e : Entry) (x : ℝ)
    (he : entryCondition D p (10^75) j e)
    (hx : Contains D ⟨e.lo,e.hi⟩ x) :
    |quarterCoefficient p j-x-(e.g:ℝ)/D|≤ (e.r:ℝ)/D := by
  obtain ⟨hlh,hg,hr,_⟩ := he
  have hDr : (0:ℝ)< D := by exact_mod_cast hD
  have ho := offset_scaled_bounds D p j hD
  have hwidth : (e.hi:ℝ)-(e.lo:ℝ)+1≤ e.r := by
    have h' : e.hi+1≤ e.r+e.lo := by omega
    have h'' : (e.hi:ℝ)+1≤ (e.r:ℝ)+(e.lo:ℝ) := by exact_mod_cast h'
    linarith
  have hrad : ((e.hi:ℝ)-(e.lo:ℝ)+1)/D≤ (e.r:ℝ)/D :=
    div_le_div_of_nonneg_right hwidth hDr.le
  rw [hg]
  push_cast
  rw [abs_le]
  have hpos : (0:ℝ)≤ 1/D := by positivity
  dsimp [Contains] at hx
  constructor
  · have heq : ((offset D p j:ℝ)-(e.lo:ℝ))/D=(offset D p j:ℝ)/D-(e.lo:ℝ)/D := by ring
    rw [heq]
    have hwidthEq : ((e.hi:ℝ)-(e.lo:ℝ)+1)/D=(e.hi:ℝ)/D-(e.lo:ℝ)/D+1/D := by ring
    rw [hwidthEq] at hrad
    linarith [ho.1,hx.2]
  · have heq : ((offset D p j:ℝ)-(e.lo:ℝ))/D=(offset D p j:ℝ)/D-(e.lo:ℝ)/D := by ring
    rw [heq]
    have hoff : ((offset D p j:ℝ)+1)/D=(offset D p j:ℝ)/D+1/D := by ring
    rw [hoff] at ho
    have hR1 : 1≤ e.r := by omega
    have hR1r : (1:ℝ)/D≤ e.r/D := div_le_div_of_nonneg_right (by exact_mod_cast hR1) hDr.le
    linarith [ho.2,hx.1]

lemma thetaExponent_record_formula (i : Fin 16) (n : Fin 8) (j : ℕ) :
    scaledCoefficient (thetaExponent n.val) (center i) (3/16) j=
      ((quarterCoefficient i.val j-lambda i n*(3/16:ℝ)^j/(j.factorial:ℝ):ℝ):ℂ) := by
  have hh := thetaExponent_scaled n.val j (center i) (3/16)
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at hh
  rw [hh]
  unfold quarterCoefficient lambda
  push_cast
  by_cases hj0 : j=0
  · simp only [if_pos hj0]
    unfold center
    push_cast
    ring
  · simp only [if_neg hj0]
    by_cases hj1 : j=1
    · simp only [if_pos hj1]
      push_cast
      ring
    · simp only [if_neg hj1]
      push_cast
      ring

lemma checked_record_exponent (i : Fin 16) (n : Fin 8) (d : Record)
    (hc : checkRecord i n d=true) (j : ℕ) (hj : j<184) :
    ‖scaledCoefficient (thetaExponent n.val) (center i) (3/16) j-
      fixedCenter scale310 (_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.G d) j‖≤ fixedRadius scale310 (_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.R d) j := by
  have he := checked_record_entry i n d hc j hj
  have hl := checked_record_lambda i n d hc j hj
  have h := entry_exponent_error scale310 i.val j (by norm_num [scale310]) ((_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.E d) j)
    (lambda i n*(3/16:ℝ)^j/(j.factorial:ℝ)) he hl
  rw [Record.E_g,Record.E_r] at h
  rw [thetaExponent_record_formula]
  unfold fixedCenter fixedRadius
  have heq : ((quarterCoefficient i.val j-lambda i n*(3/16:ℝ)^j/(j.factorial:ℝ):ℝ):ℂ)-
      ((_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.G d) j:ℂ)/scale310=
      ((quarterCoefficient i.val j-lambda i n*(3/16:ℝ)^j/(j.factorial:ℝ)-
        ((_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.G d) j:ℝ)/scale310:ℝ):ℂ) := by push_cast; rfl
  rw [heq,norm_real,Real.norm_eq_abs]
  exact h

lemma contains_lower_error (D : ℕ) (hD : 0< D) (b : Box) (x : ℝ) (s : ℕ)
    (hx : Contains D b x) (hs : b.hi-b.lo≤ s) : |x-(b.lo:ℝ)/D|≤ (s:ℝ)/D := by
  have hDr : (0:ℝ)< D := by exact_mod_cast hD
  have hlh : b.lo≤ b.hi := by
    have h : (b.lo:ℝ)≤ b.hi := (div_le_div_iff_of_pos_right hDr).mp (hx.1.trans hx.2)
    exact_mod_cast h
  have hw : (b.hi:ℝ)-(b.lo:ℝ)≤ s := by
    have h' : b.hi≤ s+b.lo := by omega
    have h'' : (b.hi:ℝ)≤ (s:ℝ)+(b.lo:ℝ) := by exact_mod_cast h'
    linarith
  rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
  calc
    _ ≤  (b.hi:ℝ)/D-(b.lo:ℝ)/D := sub_le_sub_right hx.2 _
    _ = ((b.hi:ℝ)-(b.lo:ℝ))/D := by ring
    _ ≤  _ := div_le_div_of_nonneg_right hw hDr.le

lemma checked_record_initial (i : Fin 16) (n : Fin 8) (d : Record)
    (ha : active i n) (hc : checkRecord i n d=true) :
    ‖scaledCoefficient (fullThetaTerm n.val) (center i) (3/16) 0-
      fixedCenter scale310 (_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.F d) 0‖≤ fixedRadius scale310 (_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.S d) 0 := by
  obtain ⟨hinit,_⟩ := checkRecord_conditions i n d hc
  obtain ⟨_hlen,_hlo,_hhi,hf,hs⟩ := hinit
  have hf' : (_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.F d) 0=((cachedInitial i n).lo:ℤ) := by
    simpa only [←Record.E_f,Record.E,←List.headD_eq_getD] using hf
  have hs' : (cachedInitial i n).hi-(cachedInitial i n).lo≤ (_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.S d) 0 := by
    simpa only [←Record.E_s,Record.E,←List.headD_eq_getD] using hs
  have h := contains_lower_error scale310 (by norm_num [scale310]) (cachedInitial i n)
    (2*Real.exp (center i/4-lambda i n)) ((_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.S d) 0) (cachedInitial_sound i n ha) hs'
  have he : fullThetaTerm n.val (center i)=((2*Real.exp (center i/4-lambda i n):ℝ):ℂ) := by
    unfold fullThetaTerm lambda
    push_cast
    ring
  unfold scaledCoefficient coefficient
  simp only [iteratedDeriv_zero,Nat.factorial_zero,Nat.cast_one,div_one,pow_zero,mul_one]
  rw [he]
  unfold fixedCenter fixedRadius
  rw [hf']
  have heq : ((2*Real.exp (center i/4-lambda i n):ℝ):ℂ)-
      (((cachedInitial i n).lo:ℤ):ℂ)/scale310=
      ((2*Real.exp (center i/4-lambda i n)-((cachedInitial i n).lo:ℝ)/scale310:ℝ):ℂ) := by
    push_cast
    rfl
  rw [heq,norm_real,Real.norm_eq_abs]
  exact h

set_option exponentiation.threshold 512 in
theorem checked_record_enclosure (i : Fin 16) (n : Fin 8) (d : Record)
    (ha : active i n) (hc : checkRecord i n d=true) (j : ℕ) (hj : j<184) :
    ‖scaledCoefficient (fullThetaTerm n.val) (center i) (3/16) j-
      ((_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.F d) j:ℂ)/scale310‖≤ 1/10^235 := by
  have h := fixed_enclosure_of_recurrence
    (scaledCoefficient (thetaExponent n.val) (center i) (3/16))
    (scaledCoefficient (fullThetaTerm n.val) (center i) (3/16)) scale310
    (by norm_num [scale310]) (_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.G d) (_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.F d) (_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.R d) (_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.S d) 184
    (fullThetaTerm_ode n.val (center i) (3/16))
    (checked_record_exponent i n d hc) (checked_record_initial i n d ha hc)
    (checked_record_ode i n d hc) j hj
  change ‖scaledCoefficient (fullThetaTerm n.val) (center i) (3/16) j-
    ((_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.F d) j:ℂ)/scale310‖≤ ((_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.S d) j:ℝ)/scale310 at h
  apply h.trans
  have hs := (checked_record_entry i n d hc j hj).2.2.2
  rw [Record.E_s] at hs
  calc
    _ ≤  (10^75:ℝ)/scale310 := div_le_div_of_nonneg_right (by exact_mod_cast hs) (by positivity)
    _ ≤  _ := by norm_num [scale310]

end CertifiedJetRecords

end Height100Module53

section Height100Module54

open Complex Finset
namespace CertifiedMomentConvolution
open _root_.CertifiedMomentConvolution
open CertifiedTaylorQuadrature
open _root_.CertifiedTaylorQuadrature

noncomputable def scalarPanel (q : ℕ → ℂ) (a c : ℂ) (h : ℝ) (N k : ℕ) : ℂ :=
  (h:ℂ) * ∑ m ∈ range (k+1),
    (if m< N then (a*(h:ℂ))^m/(m.factorial:ℂ) *
      correlation N q integrationWeight m else 0) *
        ((a*c)^(k-m)/((k-m).factorial:ℂ))

lemma integrationWeight_norm (j : ℕ) : ‖integrationWeight j‖≤ 2 := by
  unfold integrationWeight
  rw [norm_div]
  have hn : ‖(j+1:ℂ)‖=(j+1:ℝ) := by
    rw [show (j+1:ℂ)=((j+1:ℝ):ℂ) by push_cast; rfl,Complex.norm_real,Real.norm_eq_abs]
    exact abs_of_nonneg (by positivity)
  rw [hn]
  apply (div_le_iff₀ (by positivity : (0:ℝ)< j+1)).mpr
  have hh := norm_sub_le (1:ℂ) ((-1:ℂ)^(j+1))
  norm_num only [norm_one,norm_pow,norm_neg,one_pow] at hh
  have hj : (0:ℝ)≤ j := Nat.cast_nonneg j
  linarith

lemma correlation_error (p q : ℕ → ℂ) (N : ℕ) (ε : ℝ) (hε : 0≤ ε)
    (hpq : ∀ j< N, ‖p j-q j‖≤ ε) (m : ℕ) :
    ‖correlation N p integrationWeight m-correlation N q integrationWeight m‖≤ 2*N*ε := by
  unfold correlation
  rw [←sum_sub_distrib]
  calc
    _ ≤  ∑ j ∈ range (N-m), ‖(p j-q j)*integrationWeight (m+j)‖ := by
      simpa only [sub_mul] using norm_sum_le (s:=range (N-m))
        (f:=fun j => p j*integrationWeight (m+j)-q j*integrationWeight (m+j))
    _ ≤  ∑ _j ∈ range (N-m), ε*2 := by
      apply sum_le_sum
      intro j hj
      rw [norm_mul]
      exact mul_le_mul (hpq j (by have := mem_range.mp hj; omega))
        (integrationWeight_norm (m+j)) (norm_nonneg _) hε
    _ = (N-m:ℕ)*(ε*2) := by simp
    _ ≤  (N:ℝ)*(ε*2) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le N m) (by positivity)
    _ = _ := by ring

lemma real_power_factorial_norm (x : ℝ) (hx : 0≤ x) (n : ℕ) :
    ‖(x:ℂ)^n/(n.factorial:ℂ)‖≤ Real.exp x := by
  have he : (x:ℂ)^n/(n.factorial:ℂ)=((x^n/n.factorial:ℝ):ℂ) := by push_cast; rfl
  rw [he,norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  exact Real.pow_div_factorial_le_exp x hx n

end CertifiedMomentConvolution

end Height100Module54

section Height100Module55

open Complex Finset
namespace CertifiedMomentConvolution
open _root_.CertifiedMomentConvolution
open CertifiedTaylorQuadrature
open _root_.CertifiedTaylorQuadrature

set_option exponentiation.threshold 512

lemma exp396_bound : Real.exp 396≤ 10^172 := by
  have he : Real.exp 1≤ (27183:ℝ)/10000 := Real.exp_one_lt_d9.le.trans (by norm_num)
  rw [show Real.exp 396=(Real.exp 1)^396 by
    simpa only [Nat.cast_ofNat,mul_one] using Real.exp_nat_mul (1:ℝ) 396]
  exact (pow_le_pow_left₀ (Real.exp_nonneg _) he 396).trans (by norm_num)

lemma scalarPanel_error_sharp (p q : ℕ → ℂ) (c : ℝ) (hc0 : 0≤ c) (hc1 : c≤ 6)
    (k : ℕ) (ε : ℝ) (hε : 0≤ ε) (hpq : ∀ j<184, ‖p j-q j‖≤ ε) :
    ‖scalarPanel p 64 c (3/16) 184 k-scalarPanel q 64 c (3/16) 184 k‖≤ 10^174*ε := by
  have ha (m : ℕ) : ‖((64:ℂ)*((3/16:ℝ):ℂ))^m/(m.factorial:ℂ)‖=
      (12:ℝ)^m/(m.factorial:ℝ) := by
    have he : (64:ℂ)*((3/16:ℝ):ℂ)=12 := by norm_num
    rw [he,norm_div,norm_pow]
    norm_num
  have hc (m : ℕ) : ‖((64:ℂ)*(c:ℂ))^m/(m.factorial:ℂ)‖≤ Real.exp 384 := by
    have h := real_power_factorial_norm (64*c) (by positivity) m
    have he : ((64*c:ℝ):ℂ)=(64:ℂ)*(c:ℂ) := by push_cast; rfl
    rw [he] at h
    exact h.trans (Real.exp_le_exp.mpr (by linarith))
  have hs :
      ‖∑ m ∈ range (k+1),
        (if m<184 then ((64:ℂ)*((3/16:ℝ):ℂ))^m/(m.factorial:ℂ)*
          (correlation 184 p integrationWeight m-correlation 184 q integrationWeight m)
        else 0)*(((64:ℂ)*(c:ℂ))^(k-m)/((k-m).factorial:ℂ))‖≤ 
      Real.exp 12*(2*184*ε)*Real.exp 384 := by
    calc
      _ ≤  ∑ m ∈ range (k+1),
          ‖(if m<184 then ((64:ℂ)*((3/16:ℝ):ℂ))^m/(m.factorial:ℂ)*
            (correlation 184 p integrationWeight m-correlation 184 q integrationWeight m)
          else 0)*(((64:ℂ)*(c:ℂ))^(k-m)/((k-m).factorial:ℂ))‖ := norm_sum_le _ _
      _ ≤  ∑ m ∈ range (k+1), ((12:ℝ)^m/m.factorial)*(2*184*ε)*Real.exp 384 := by
        apply sum_le_sum
        intro m _hm
        by_cases hm : m<184
        · simp only [if_pos hm,norm_mul,ha]
          exact mul_le_mul (mul_le_mul_of_nonneg_left
            (correlation_error p q 184 ε hε hpq m) (by positivity)) (hc (k-m))
              (norm_nonneg _) (by positivity)
        · simp only [if_neg hm,zero_mul,norm_zero]
          positivity
      _ = (∑ m ∈ range (k+1), (12:ℝ)^m/m.factorial)*(2*184*ε)*Real.exp 384 := by
        rw [sum_mul,sum_mul]
      _ ≤  _ := by
        gcongr
        exact Real.sum_le_exp_of_nonneg (by norm_num) (k+1)
  have hd : scalarPanel p 64 c (3/16) 184 k-scalarPanel q 64 c (3/16) 184 k=
      ((3/16:ℝ):ℂ)*∑ m ∈ range (k+1),
        (if m<184 then ((64:ℂ)*((3/16:ℝ):ℂ))^m/(m.factorial:ℂ)*
          (correlation 184 p integrationWeight m-correlation 184 q integrationWeight m)
        else 0)*(((64:ℂ)*(c:ℂ))^(k-m)/((k-m).factorial:ℂ)) := by
    unfold scalarPanel
    rw [←mul_sub,←sum_sub_distrib]
    congr 1
    apply sum_congr rfl
    intro m _hm
    by_cases hm : m<184 <;> simp only [hm,ite_true,ite_false,zero_mul]
    · ring
    · simp
  rw [hd,norm_mul,norm_real,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<3/16)]
  calc
    _ ≤  (3/16:ℝ)*(Real.exp 12*(2*184*ε)*Real.exp 384) := by gcongr
    _ = 69*ε*Real.exp 396 := by
      rw [show (396:ℝ)=12+384 by norm_num,Real.exp_add]
      ring
    _ ≤  69*ε*(10^172) := mul_le_mul_of_nonneg_left exp396_bound (by positivity)
    _ ≤  _ := by nlinarith [hε]

end CertifiedMomentConvolution

end Height100Module55

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
  have ht : ‖thetaTruncation z‖≤ 8*Real.exp (-(3/2)*Real.exp z.re) := by
    calc
      _ ≤  ∑ n ∈ range 8, ‖Complex.exp (-(Real.pi:ℂ)*(n+1)^2*Complex.exp z)‖ := norm_sum_le _ _
      _ ≤  ∑ _n ∈ range 8, Real.exp (-(3/2)*Real.exp z.re) :=
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
    _ ≤  2*Real.exp (z.re/4)*Real.exp (64*‖z‖)*(8*Real.exp (-(3/2)*Real.exp z.re)) := by
      gcongr
      rw [Complex.norm_exp]
      simp
    _ = 16*Real.exp (z.re/4+64*‖z‖-(3/2)*Real.exp z.re) := by
      rw [show z.re/4+64*‖z‖-(3/2)*Real.exp z.re =
        z.re/4+64*‖z‖+(-(3/2)*Real.exp z.re) by ring,Real.exp_add,Real.exp_add]
      ring
    _ ≤  16*Real.exp 189 := by gcongr
    _ ≤  16*(27183/10000:ℝ)^189 := by
      rw [show Real.exp 189=(Real.exp 1)^189 by
        simpa only [Nat.cast_ofNat,mul_one] using Real.exp_nat_mul (1:ℝ) 189]
      gcongr
      linarith [Real.exp_one_lt_d9]
    _ ≤  10^84 := by norm_num
end CertifiedZetaQuadrature

end Height100Module57

section Height100Module58
open Complex Metric MeasureTheory
namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature
lemma global_moment_panel_error_184 (k : ℕ) (c : ℝ) (hc : 0≤ c) :
    ‖(∫ x in -(3/16:ℝ)..(3/16:ℝ), globalKernelMoment k ((c:ℂ)+x)) -
      CertifiedTaylorQuadrature.panel (globalKernelMoment k) c (3/16) 184‖≤ 1/10^50 := by
  have hb : ∀ z ∈ sphere (c:ℂ) (1:ℝ), ‖globalKernelMoment k z‖≤ 10^84 := by
    intro z hz
    exact globalKernelMoment_unit_disk_84 k c hc z (mem_sphere_iff_norm.mp hz).le
  have he := CertifiedTaylorQuadrature.panel_error (globalKernelMoment k) (globalKernelMoment_entire k)
    c 1 (10^84) (3/16) (by norm_num) (by positivity) (by norm_num) (by norm_num) hb 184
  apply he.trans
  norm_num
end CertifiedZetaQuadrature

end Height100Module58

section Height100Module59

open Complex MeasureTheory Finset
namespace CertifiedGlobalQuadrature
open _root_.CertifiedGlobalQuadrature
open CertifiedZetaQuadrature CertifiedTaylorQuadrature
open _root_.CertifiedZetaQuadrature _root_.CertifiedTaylorQuadrature

noncomputable def grid (i : ℕ) : ℝ := 3*(i:ℝ)/8
noncomputable def panelCenter (i : ℕ) : ℝ := 3*(2*(i:ℝ)+1)/16
noncomputable def rule (k : ℕ) : ℂ :=
  ∑ i ∈ range 16, panel (globalKernelMoment k) (panelCenter i) (3/16) 184

lemma shifted_integral (k i : ℕ) :
    (∫ u in -(3/16:ℝ)..(3/16:ℝ), globalKernelMoment k ((panelCenter i:ℂ)+u)) =
      ∫ t in grid i..grid (i+1), globalKernelMoment k (t:ℂ) := by
  have h := intervalIntegral.integral_comp_add_left
    (fun t : ℝ => globalKernelMoment k (t:ℂ)) (a:=-(3/16:ℝ)) (b:=3/16) (panelCenter i)
  have hL : panelCenter i+(-(3/16:ℝ))=grid i := by unfold panelCenter grid; ring
  have hR : panelCenter i+(3/16:ℝ)=grid (i+1) := by unfold panelCenter grid; push_cast; ring
  simpa only [Complex.ofReal_add,hL,hR] using h

lemma integral_sum (k : ℕ) :
    (∑ i ∈ range 16, ∫ t in grid i..grid (i+1), globalKernelMoment k (t:ℂ)) =
      ∫ u in (0:ℝ)..6, globalKernelMoment k (u:ℂ) := by
  have hc : Continuous (fun t : ℝ => globalKernelMoment k (t:ℂ)) :=
    (globalKernelMoment_entire k).continuous.comp Complex.continuous_ofReal
  have h := intervalIntegral.sum_integral_adjacent_intervals (μ:=volume) (a:=grid) (n:=16)
    (fun i _ => hc.intervalIntegrable (grid i) (grid (i+1)))
  have h0 : grid 0=0 := by norm_num [grid]
  have h16 : grid 16=6 := by norm_num [grid]
  rwa [h0,h16] at h

lemma integral_error (k : ℕ) :
    ‖(∫ u in (0:ℝ)..6, globalKernelMoment k (u:ℂ))-rule k‖≤ 16/10^50 := by
  rw [← integral_sum,rule,← sum_sub_distrib]
  calc
    _ ≤  ∑ i ∈ range 16, ‖(∫ t in grid i..grid (i+1), globalKernelMoment k (t:ℂ))-
        panel (globalKernelMoment k) (panelCenter i) (3/16) 184‖ := norm_sum_le _ _
    _ ≤  ∑ _i ∈ range 16, (1/10^50:ℝ) := by
      apply sum_le_sum
      intro i _
      rw [← shifted_integral]
      exact global_moment_panel_error_184 k (panelCenter i) (by unfold panelCenter; positivity)
    _ = _ := by simp; ring

/-- The complete analytic reduction of each true even moment to the16-panel packed rule. -/
lemma moment_rule_error (j : ℕ) :
    ‖(CertifiedGlobalMoments.moment j:ℂ)-rule (2*j)‖≤ 4/10^47 := by
  have hc := twisted_cutoff_transformed 64 0 (2*j) (by norm_num)
  rw [← CertifiedGlobalMoments.moment_complex] at hc
  have he : (fun u : ℝ => transformedMoment 64 0 (2*j) (u:ℂ)) =
      (fun u : ℝ => globalKernelMoment (2*j) (u:ℂ)) := by
    funext u
    exact transformedMoment_sixtyfour _ _
  rw [he] at hc
  have hq := integral_error (2*j)
  have hid : (CertifiedGlobalMoments.moment j:ℂ)-rule (2*j) =
      ((CertifiedGlobalMoments.moment j:ℂ)-(∫ u in (0:ℝ)..6, globalKernelMoment (2*j) (u:ℂ)))+
      ((∫ u in (0:ℝ)..6, globalKernelMoment (2*j) (u:ℂ))-rule (2*j)) := by ring
  rw [hid]
  exact (norm_add_le _ _).trans (by linarith)

/-- A finite numerical rule enclosure at10^-47 yields the agreed10^-46 true-moment enclosure. -/
lemma coefficient_enclosure (j : ℕ) (a : ℝ)
    (hnum : ‖rule (2*j)-(a:ℂ)‖≤ 1/10^47) :
    |CertifiedGlobalMoments.moment j-a|≤ 1/10^46 := by
  have he : |CertifiedGlobalMoments.moment j-a|=‖(CertifiedGlobalMoments.moment j:ℂ)-(a:ℂ)‖ := by
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  rw [he]
  have hid : (CertifiedGlobalMoments.moment j:ℂ)-(a:ℂ)=
      ((CertifiedGlobalMoments.moment j:ℂ)-rule (2*j))+(rule (2*j)-(a:ℂ)) := by ring
  rw [hid]
  have ha := moment_rule_error j
  exact (norm_add_le _ _).trans (by linarith)

end CertifiedGlobalQuadrature

end Height100Module59

section Height100Module60

open Complex Finset
namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature
open CertifiedMomentConvolution CertifiedTaylorQuadrature
open _root_.CertifiedMomentConvolution _root_.CertifiedTaylorQuadrature

lemma baseKernel_scaled_coefficient (c h : ℂ) (j : ℕ) :
    scaledCoefficient baseKernel c h j=
      ∑ n ∈ range 8, scaledCoefficient (fullThetaTerm n) c h j := by
  unfold scaledCoefficient coefficient baseKernel
  rw [iteratedDeriv_fun_sum (fun n _ => (fullThetaTerm_entire n).contDiff.contDiffAt)]
  rw [sum_div,sum_mul]

lemma global_moment_panel_eq (c : ℝ) (k : ℕ) :
    panel (globalKernelMoment k) c (3/16) 184=
      scalarPanel (scaledCoefficient baseKernel c (3/16)) 64 c (3/16) 184 k := by
  have he : globalKernelMoment k=(fun z => ((64*z)^k/(k.factorial:ℂ))*baseKernel z) := by
    funext z
    exact globalKernelMoment_base k z
  rw [he]
  simpa only [scalarPanel,Complex.ofReal_div,Complex.ofReal_ofNat] using
    power_moment_panel baseKernel baseKernel_entire 64 c (3/16) 184 k

lemma global_moment_panel_jet_error (c : ℝ) (hc0 : 0≤ c) (hc1 : c≤ 6)
    (q : ℕ → ℂ) (hq : ∀ j<184, ‖scaledCoefficient baseKernel c (3/16) j-q j‖≤ 1/10^234)
    (k : ℕ) :
    ‖panel (globalKernelMoment k) c (3/16) 184-scalarPanel q 64 c (3/16) 184 k‖≤ 1/10^60 := by
  rw [global_moment_panel_eq]
  exact (scalarPanel_error_sharp _ _ c hc0 hc1 k (1/10^234) (by positivity) hq).trans_eq (by norm_num)

noncomputable def approximateRule (q : ℕ → ℕ → ℂ) (k : ℕ) : ℂ :=
  ∑ i ∈ range 16, scalarPanel (q i) 64 (CertifiedGlobalQuadrature.panelCenter i) (3/16) 184 k

lemma global_rule_jet_error (q : ℕ → ℕ → ℂ)
    (hq : ∀ i<16, ∀ j<184,
      ‖scaledCoefficient baseKernel (CertifiedGlobalQuadrature.panelCenter i) (3/16) j-q i j‖
        ≤ 1/10^234) (k : ℕ) :
    ‖CertifiedGlobalQuadrature.rule k-approximateRule q k‖≤ 16/10^60 := by
  unfold CertifiedGlobalQuadrature.rule approximateRule
  rw [←sum_sub_distrib]
  calc
    _ ≤  ∑ i ∈ range 16,
      ‖panel (globalKernelMoment k) (CertifiedGlobalQuadrature.panelCenter i) (3/16) 184-
        scalarPanel (q i) 64 (CertifiedGlobalQuadrature.panelCenter i) (3/16) 184 k‖ :=
      norm_sum_le _ _
    _ ≤  ∑ _i ∈ range 16, (1/10^60:ℝ) := by
      apply sum_le_sum
      intro i hi
      have hi' : i<16 := mem_range.mp hi
      apply global_moment_panel_jet_error _ _ _ (q i) (hq i hi') k
      · unfold CertifiedGlobalQuadrature.panelCenter
        positivity
      · have hiR : (i:ℝ)≤ 15 := by
          have hiN : i≤ 15 := by omega
          exact_mod_cast hiN
        unfold CertifiedGlobalQuadrature.panelCenter
        linarith
    _ = _ := by simp; ring

lemma moment_enclosure_of_jet_rule (q : ℕ → ℕ → ℂ)
    (hq : ∀ i<16, ∀ j<184,
      ‖scaledCoefficient baseKernel (CertifiedGlobalQuadrature.panelCenter i) (3/16) j-q i j‖
        ≤ 1/10^234)
    (j : ℕ) (hj : j<256) (a : ℝ)
    (hnum : ‖approximateRule q (2*j)-(a:ℂ)‖≤ 1/10^62) :
    |CertifiedGlobalMoments.moment j-a|≤ 1/10^46 := by
  apply CertifiedGlobalQuadrature.coefficient_enclosure j a
  have h := global_rule_jet_error q hq (2*j)
  have he : CertifiedGlobalQuadrature.rule (2*j)-(a:ℂ)=
      (CertifiedGlobalQuadrature.rule (2*j)-approximateRule q (2*j))+
      (approximateRule q (2*j)-(a:ℂ)) := by ring
  rw [he]
  exact (norm_add_le _ _).trans (by linarith)

end CertifiedZetaQuadrature

end Height100Module60

section Height100Module61

open Complex Metric Finset
namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature
open CertifiedTaylorQuadrature CertifiedMomentConvolution
open _root_.CertifiedTaylorQuadrature _root_.CertifiedMomentConvolution
set_option exponentiation.threshold 1024

lemma thetaTerm_quarter_disk_bound (n : ℕ) (c : ℝ) (z : ℂ)
    (hz : ‖z-(c:ℂ)‖≤ 1/4) :
    ‖thetaTerm n z‖≤ Real.exp (-(18/25)*(Real.pi*(n+1:ℝ)^2*Real.exp c)) := by
  have hre : |z.re-c|≤ 1/4 := by
    simpa only [sub_re,ofReal_re] using (Complex.abs_re_le_norm (z-(c:ℂ))).trans hz
  have him : |z.im|≤ 1/4 := by
    simpa only [sub_im,ofReal_im,sub_zero] using (Complex.abs_im_le_norm (z-(c:ℂ))).trans hz
  have hcos : (31/32:ℝ)≤ Real.cos z.im := by
    have hs : z.im^2≤ 1/16 := by
      have hi := abs_le.mp him
      nlinarith [mul_nonneg (sub_nonneg.mpr hi.2) (sub_nonneg.mpr hi.1)]
    linarith [Real.one_sub_sq_div_two_le_cos (x:=z.im)]
  have hexp : (3/4:ℝ)≤ Real.exp (z.re-c) := by
    have h := Real.add_one_le_exp (z.re-c)
    linarith [(abs_le.mp hre).1]
  have hprod : (18/25:ℝ)≤ Real.exp (z.re-c)*Real.cos z.im := by
    have h := mul_le_mul hexp hcos (by norm_num : (0:ℝ)≤ 31/32) (Real.exp_nonneg _)
    linarith
  have hscale := mul_le_mul_of_nonneg_left hprod (Real.exp_nonneg c)
  have heq : Real.exp c*Real.exp (z.re-c)=Real.exp z.re := by
    rw [←Real.exp_add]
    congr 1
    ring
  rw [←mul_assoc,heq] at hscale
  have hm := mul_le_mul_of_nonneg_left hscale
    (show (0:ℝ)≤ Real.pi*(n+1:ℝ)^2 by positivity)
  rw [thetaTerm,Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [mul_re,neg_re,ofReal_re,neg_im,ofReal_im,neg_zero,mul_im,
    natCast_re,natCast_im,add_re,one_re,add_im,one_im,pow_two,Complex.exp_re,Complex.exp_im]
  nlinarith

lemma exp_neg_five_seventy_six_bound : Real.exp (-576)≤ (1/10^250:ℝ) := by
  rw [Real.exp_neg,show Real.exp (576:ℝ)=(Real.exp 1)^576 by
    simpa only [Nat.cast_ofNat,mul_one] using Real.exp_nat_mul (1:ℝ) 576]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤ 2718/1000)
    (show (2718/1000:ℝ)≤ Real.exp 1 by linarith [Real.exp_one_gt_d9]) 576
  calc
    _ ≤  ((2718/1000:ℝ)^576)⁻¹ := inv_anti₀ (by positivity) hp
    _ ≤  _ := by norm_num

lemma fullThetaTerm_quarter_small_disk (n : ℕ) (c : ℝ) (hc : c≤ 6)
    (hrate : 800≤ Real.pi*(n+1:ℝ)^2*Real.exp c) (z : ℂ) (hz : ‖z-(c:ℂ)‖≤ 1/4) :
    ‖fullThetaTerm n z‖≤ 18/10^250 := by
  have hθ : ‖thetaTerm n z‖≤ (1/10^250:ℝ) :=
    (thetaTerm_quarter_disk_bound n c z hz).trans
      ((Real.exp_le_exp.mpr (by linarith)).trans exp_neg_five_seventy_six_bound)
  have hre : z.re≤ 25/4 := by
    have h := (Complex.abs_re_le_norm (z-(c:ℂ))).trans hz
    simp only [sub_re,ofReal_re] at h
    linarith [(abs_le.mp h).2]
  have hexp : Real.exp 2≤ 9 := by
    have h := Real.exp_one_lt_three
    have hp := Real.exp_pos 1
    rw [show Real.exp 2=(Real.exp 1)^2 by
      simpa only [Nat.cast_ofNat,mul_one] using Real.exp_nat_mul (1:ℝ) 2]
    nlinarith
  have hpref : ‖2*Complex.exp (z/4)‖≤ 18 := by
    rw [norm_mul,Complex.norm_exp]
    norm_num
    have h := Real.exp_le_exp.mpr (show z.re/4≤ 2 by linarith)
    nlinarith
  rw [fullThetaTerm_factor,norm_mul]
  exact (mul_le_mul hpref hθ (norm_nonneg _) (by norm_num)).trans_eq (by ring)

lemma fullThetaTerm_small_jet_800 (n j : ℕ) (c : ℝ) (hc : c≤ 6)
    (hrate : 800≤ Real.pi*(n+1:ℝ)^2*Real.exp c) :
    ‖scaledCoefficient (fullThetaTerm n) c (3/16) j‖≤ 1/10^248 := by
  have hcoef := coefficient_bound (fullThetaTerm n) (fullThetaTerm_entire n) c (1/4) (18/10^250)
    (by norm_num) (fun z hz => fullThetaTerm_quarter_small_disk n c hc hrate z
      (mem_sphere_iff_norm.mp hz).le) j
  unfold scaledCoefficient
  rw [norm_mul,norm_pow]
  norm_num only [norm_div,Complex.norm_ofNat]
  have he : ((18/10^250:ℝ)/(1/4)^j)*(3/16)^j=(18/10^250:ℝ)*(3/4)^j := by
    rw [div_mul_eq_mul_div,mul_div_assoc,←div_pow]
    norm_num
  calc
    _ ≤  ((18/10^250)/(1/4)^j)*(3/16)^j := mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = (18/10^250:ℝ)*(3/4)^j := he
    _ ≤  (18/10^250:ℝ)*1 := by gcongr; exact pow_le_one₀ (by norm_num) (by norm_num)
    _ ≤  _ := by norm_num

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
open _root_.CertifiedGlobalJetCenters
open CertifiedJetRecords CertifiedThetaPoints CertifiedFixedPoint
open _root_.CertifiedJetRecords _root_.CertifiedThetaPoints _root_.CertifiedFixedPoint
open CertifiedMomentConvolution CertifiedZetaQuadrature
open _root_.CertifiedMomentConvolution _root_.CertifiedZetaQuadrature

lemma addLists_getD (xs ys : List ℤ) (j : ℕ) :
    (addLists xs ys).getD j 0=xs.getD j 0+ys.getD j 0 := by
  induction xs generalizing ys j with
  | nil => simp [addLists]
  | cons x xs ih =>
    cases ys with
    | nil => simp [addLists]
    | cons y ys =>
      cases j with
      | zero => rfl
      | succ j => exact ih ys j

lemma sumLists_getD (rows : List (List ℤ)) (j : ℕ) :
    (sumLists rows).getD j 0=(rows.map (fun xs => xs.getD j 0)).sum := by
  induction rows with
  | nil => rfl
  | cons xs rows ih =>
    simp only [sumLists,List.map_cons,List.sum_cons]
    rw [addLists_getD,ih]

lemma centerNumerators_getD (i : Fin 16) (j : ℕ) :
    (centerNumerators i).getD j 0=∑ n : Fin 8, (_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.F (recordAt i n)) j := by
  unfold centerNumerators
  rw [addLists_getD]
  have hz : (List.replicate 184 (0 : ℤ)).getD j 0 = 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_getD_replicate_default_eq]
  rw [hz, zero_add]
  rw [sumLists_getD,List.map_ofFn,List.sum_ofFn]
  rfl

noncomputable def baseCenter (i : Fin 16) (j : ℕ) : ℂ :=
  ((centerNumerators i).getD j 0:ℂ)/scale310

lemma baseCenter_eq_sum (i : Fin 16) (j : ℕ) :
    baseCenter i j=∑ n : Fin 8, ((_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.F (recordAt i n)) j:ℂ)/scale310 := by
  rw [baseCenter,centerNumerators_getD,Int.cast_sum,Finset.sum_div]

theorem inactive_empty : ∀ i : Fin 16, ∀ n : Fin 8,
    ¬active i n → (recordAt i n).fs=[] := by decide +kernel

lemma center_le_six (i : Fin 16) : center i≤ 6 := by
  have hi : (i.val:ℝ)≤ 15 := by
    have hn : i.val≤ 15 := by omega
    exact_mod_cast hn
  unfold center
  linarith

lemma term_error (i : Fin 16) (n : Fin 8) (j : ℕ) (hj : j<184) :
    ‖scaledCoefficient (fullThetaTerm n.val) (center i) (3/16) j-
      ((_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.F (recordAt i n)) j:ℂ)/scale310‖≤ 1/10^235 := by
  by_cases ha : active i n
  · exact checked_record_enclosure i n (recordAt i n) ha (records_checked i n ha) j hj
  · have hzero : (_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.F (recordAt i n)) j=0 := by
      simp [Record.F,inactive_empty i n ha]
    rw [hzero,Int.cast_zero,zero_div,sub_zero]
    have hsmall := fullThetaTerm_small_jet_800 n.val j (center i) (center_le_six i)
      (by simpa [lambda] using inactive_lambda_ge i n ha)
    exact hsmall.trans (by norm_num)

lemma base_error (i : Fin 16) (j : ℕ) (hj : j<184) :
    ‖scaledCoefficient baseKernel (center i) (3/16) j-baseCenter i j‖≤ 1/10^234 := by
  rw [baseKernel_scaled_coefficient,Finset.sum_range,baseCenter_eq_sum,←sum_sub_distrib]
  calc
    _ ≤  ∑ n : Fin 8, ‖scaledCoefficient (fullThetaTerm n.val) (center i) (3/16) j-
        ((_root_.RH14MomentEnclosureProof.CertifiedJetRecords.Record.F (recordAt i n)) j:ℂ)/scale310‖ := norm_sum_le _ _
    _ ≤  ∑ _n : Fin 8, (1/10^235:ℝ) := sum_le_sum (fun n _ => term_error i n j hj)
    _ ≤  _ := by norm_num

noncomputable def centers (i : ℕ) : List ℤ := if hi : i<16 then centerNumerators ⟨i,hi⟩ else []
noncomputable def jet (i j : ℕ) : ℂ := (centers i |>.getD j 0 : ℂ)/scale310

lemma center_eq_panelCenter (i : Fin 16) : center i=CertifiedGlobalQuadrature.panelCenter i.val := by
  unfold center CertifiedGlobalQuadrature.panelCenter
  ring

lemma jet_error (i : ℕ) (hi : i<16) (j : ℕ) (hj : j<184) :
    ‖scaledCoefficient baseKernel (CertifiedGlobalQuadrature.panelCenter i) (3/16) j-jet i j‖≤ 1/10^234 := by
  have h := base_error ⟨i,hi⟩ j hj
  simpa only [center_eq_panelCenter,jet,centers,dif_pos hi,baseCenter] using h

end CertifiedGlobalJetCenters

end Height100Module62

open Complex Finset

lemma new_rule_eq (j : ℕ) :
    ((TaoFivePrimes_RHExtendedMomentRule j:ℚ):ℂ)=
      CertifiedZetaQuadrature.approximateRule CertifiedGlobalJetCenters.jet (2*j) := by
  simp only [TaoFivePrimes_RHExtendedMomentRule,
    CertifiedZetaQuadrature.approximateRule, RHNextMomentRule.scalarPanel,
    CertifiedMomentConvolution.scalarPanel, RHNextMomentRule.correlation,
    CertifiedMomentConvolution.correlation, RHNextMomentRule.weight,
    CertifiedMomentConvolution.integrationWeight, RHNextMomentRule.panelCenter,
    CertifiedGlobalQuadrature.panelCenter, RHNextMomentRule.jet,
    CertifiedGlobalJetCenters.jet, RHNextMomentRule.centers,
    CertifiedGlobalJetCenters.centers]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  congr 2
  funext m
  by_cases hm : m<184
  · simp only [if_pos hm]
    push_cast
    norm_num
  · simp [hm]

theorem moment_rule_error_any_index (j : ℕ) :
    ‖(CertifiedGlobalMoments.moment j:ℂ)-
      CertifiedZetaQuadrature.approximateRule CertifiedGlobalJetCenters.jet (2*j)‖ ≤ 1/10^46 := by
  have ha := CertifiedGlobalQuadrature.moment_rule_error j
  have hb := CertifiedZetaQuadrature.global_rule_jet_error CertifiedGlobalJetCenters.jet
    CertifiedGlobalJetCenters.jet_error (2*j)
  have he : (CertifiedGlobalMoments.moment j:ℂ)-
      CertifiedZetaQuadrature.approximateRule CertifiedGlobalJetCenters.jet (2*j) =
      ((CertifiedGlobalMoments.moment j:ℂ)-CertifiedGlobalQuadrature.rule (2*j))+
      (CertifiedGlobalQuadrature.rule (2*j)-
        CertifiedZetaQuadrature.approximateRule CertifiedGlobalJetCenters.jet (2*j)) := by ring
  rw [he]
  exact (norm_add_le _ _).trans (by linarith)

end RH14MomentEnclosureProof

theorem solution (j : ℕ) :
    ‖(CertifiedGlobalMoments.moment j:ℂ)-(TaoFivePrimes_RHExtendedMomentRule j:ℂ)‖ ≤ 1/10^46 := by
  rw [RH14MomentEnclosureProof.new_rule_eq]
  exact RH14MomentEnclosureProof.moment_rule_error_any_index j
