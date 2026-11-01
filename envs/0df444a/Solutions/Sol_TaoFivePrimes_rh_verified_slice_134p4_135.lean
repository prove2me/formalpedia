-- Prove2me | solution 1 for TaoFivePrimes.rh_verified_slice_134p4_135
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-31T22:36:26.119129+00:00
-- url     : https://prove2.me/submissions/ef827ddc-b581-4222-a812-6840e17752cd

/- Submission file for Prove2Me theorem
TaoFivePrimes.rh_verified_slice_134p4_135 (ebdfa137, Open).
Submitted with the user's explicit per-item approval (Oct 31, 2026); v1 returned CE only because the header used C-style comments, fixed here to Lean block comments.

Structure: platform imports supply the Proved derivative bound, the nine
Proved bernstein_3 theorems, and the Bernstein-matrix definition (the
rational-polynomial, coefficient, and analytic-model definitions arrive
transitively through the derivative-bound import's preamble). The generic
Bernstein lemmas, the Imag134 certificate lemmas, and the slice assembly
are proved inline, exactly as in the locally verified twin file
Solutions/Slice134Full.lean, where the derivative bound appears as a
clearly-labeled axiom stub with the same name and statement and the
bernstein_3 theorems appear as decide+kernel mirrors. That twin file
compiles exit 0 with axioms [propext, Classical.choice, Quot.sound]
plus the derivative-bound stub only; on the platform the stub is this
import, so no extra axiom remains. This file itself has NOT been compiled
in the platform environment; its import paths follow the proved-105
precedent and the certificate file's own import lines. -/
import Mathlib
import Theorems.Thm_TaoFivePrimes_rh132_xi_polynomial_derivative_bound
import Theorems.Thm_TaoFivePrimes_rh132_bernstein_3_row0
import Theorems.Thm_TaoFivePrimes_rh132_bernstein_3_row1
import Theorems.Thm_TaoFivePrimes_rh132_bernstein_3_row2
import Theorems.Thm_TaoFivePrimes_rh132_bernstein_3_row3
import Theorems.Thm_TaoFivePrimes_rh132_bernstein_3_column0
import Theorems.Thm_TaoFivePrimes_rh132_bernstein_3_column1
import Theorems.Thm_TaoFivePrimes_rh132_bernstein_3_column2
import Theorems.Thm_TaoFivePrimes_rh132_bernstein_3_column3
import Theorems.Thm_TaoFivePrimes_rh132_bernstein_3_lower
import Definitions.Def_TaoFivePrimes_RH132BernsteinImag134p4To135
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000


open Complex Finset
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

namespace CertifiedLocalPolynomial
open Complex Finset TaoZetaNumerics
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

namespace Imag134
noncomputable def powerMatrix := RH132BernsteinImag134p4To135.powerMatrix
noncomputable def rowMatrix := RH132BernsteinImag134p4To135.rowMatrix
noncomputable def bernsteinMatrix := RH132BernsteinImag134p4To135.bernsteinMatrix
noncomputable def entry := RH132BernsteinImag134p4To135.entry
noncomputable def a := RH132BernsteinImag134p4To135.a
noncomputable def r := RH132BernsteinImag134p4To135.r
noncomputable def b := RH132BernsteinImag134p4To135.b

noncomputable def c (n : ℕ) : ℝ :=
  (TaoFivePrimes_RH132RoundedCoefficients14.getD n 0:ℝ)/(10^14:ℝ)
noncomputable def realValue (x y : ℝ) : ℝ :=
    ((-1:ℝ)/100000000000000) * x^22 * y^0 +
    ((231:ℝ)/100000000000000) * x^20 * y^2 +
    ((-63:ℝ)/100000000000000) * x^20 * y^1 +
    ((-61:ℝ)/50000000000000) * x^20 * y^0 +
    ((-1463:ℝ)/20000000000000) * x^18 * y^4 +
    ((399:ℝ)/10000000000000) * x^18 * y^3 +
    ((1159:ℝ)/5000000000000) * x^18 * y^2 +
    ((-33953:ℝ)/100000000000000) * x^18 * y^1 +
    ((1143:ℝ)/100000000000000) * x^18 * y^0 +
    ((74613:ℝ)/100000000000000) * x^16 * y^6 +
    ((-61047:ℝ)/100000000000000) * x^16 * y^5 +
    ((-59109:ℝ)/10000000000000) * x^16 * y^4 +
    ((1731603:ℝ)/100000000000000) * x^16 * y^3 +
    ((-174879:ℝ)/100000000000000) * x^16 * y^2 +
    ((-3512353:ℝ)/100000000000000) * x^16 * y^1 +
    ((61283:ℝ)/3125000000000) * x^16 * y^0 +
    ((-31977:ℝ)/10000000000000) * x^14 * y^8 +
    ((8721:ℝ)/2500000000000) * x^14 * y^7 +
    ((59109:ℝ)/1250000000000) * x^14 * y^6 +
    ((-5194809:ℝ)/25000000000000) * x^14 * y^5 +
    ((174879:ℝ)/5000000000000) * x^14 * y^4 +
    ((3512353:ℝ)/2500000000000) * x^14 * y^3 +
    ((-183849:ℝ)/78125000000) * x^14 * y^2 +
    ((-652983:ℝ)/1250000000000) * x^14 * y^1 +
    ((193897521:ℝ)/100000000000000) * x^14 * y^0 +
    ((323323:ℝ)/50000000000000) * x^12 * y^10 +
    ((-88179:ℝ)/10000000000000) * x^12 * y^9 +
    ((-768417:ℝ)/5000000000000) * x^12 * y^8 +
    ((22510839:ℝ)/25000000000000) * x^12 * y^7 +
    ((-5304663:ℝ)/25000000000000) * x^12 * y^6 +
    ((-319624123:ℝ)/25000000000000) * x^12 * y^5 +
    ((5576753:ℝ)/156250000000) * x^12 * y^4 +
    ((19807151:ℝ)/1250000000000) * x^12 * y^3 +
    ((-17644674411:ℝ)/100000000000000) * x^12 * y^2 +
    ((15177976489:ℝ)/100000000000000) * x^12 * y^1 +
    ((34836331:ℝ)/781250000000) * x^12 * y^0 +
    ((-323323:ℝ)/50000000000000) * x^10 * y^12 +
    ((264537:ℝ)/25000000000000) * x^10 * y^11 +
    ((2817529:ℝ)/12500000000000) * x^10 * y^10 +
    ((-82539743:ℝ)/50000000000000) * x^10 * y^9 +
    ((25007697:ℝ)/50000000000000) * x^10 * y^8 +
    ((502266479:ℝ)/12500000000000) * x^10 * y^7 +
    ((-61344283:ℝ)/390625000000) * x^10 * y^6 +
    ((-653635983:ℝ)/6250000000000) * x^10 * y^5 +
    ((194091418521:ℝ)/100000000000000) * x^10 * y^4 +
    ((-166957741379:ℝ)/50000000000000) * x^10 * y^3 +
    ((-1149598923:ℝ)/390625000000) * x^10 * y^2 +
    ((1016611987963:ℝ)/100000000000000) * x^10 * y^1 +
    ((-332054528693:ℝ)/100000000000000) * x^10 * y^0 +
    ((31977:ℝ)/10000000000000) * x^8 * y^14 +
    ((-61047:ℝ)/10000000000000) * x^8 * y^13 +
    ((-768417:ℝ)/5000000000000) * x^8 * y^12 +
    ((67532517:ℝ)/50000000000000) * x^8 * y^11 +
    ((-25007697:ℝ)/50000000000000) * x^8 * y^10 +
    ((-502266479:ℝ)/10000000000000) * x^8 * y^9 +
    ((78871221:ℝ)/312500000000) * x^8 * y^8 +
    ((280129707:ℝ)/1250000000000) * x^8 * y^7 +
    ((-582274255563:ℝ)/100000000000000) * x^8 * y^6 +
    ((1502619672411:ℝ)/100000000000000) * x^8 * y^5 +
    ((3448796769:ℝ)/156250000000) * x^8 * y^4 +
    ((-3049835963889:ℝ)/20000000000000) * x^8 * y^3 +
    ((2988490758237:ℝ)/20000000000000) * x^8 * y^2 +
    ((16130418285879:ℝ)/100000000000000) * x^8 * y^1 +
    ((-19027315712187:ℝ)/100000000000000) * x^8 * y^0 +
    ((-74613:ℝ)/100000000000000) * x^6 * y^16 +
    ((20349:ℝ)/12500000000000) * x^6 * y^15 +
    ((59109:ℝ)/1250000000000) * x^6 * y^14 +
    ((-12121221:ℝ)/25000000000000) * x^6 * y^13 +
    ((5304663:ℝ)/25000000000000) * x^6 * y^12 +
    ((319624123:ℝ)/12500000000000) * x^6 * y^11 +
    ((-61344283:ℝ)/390625000000) * x^6 * y^10 +
    ((-217878661:ℝ)/1250000000000) * x^6 * y^9 +
    ((582274255563:ℝ)/100000000000000) * x^6 * y^8 +
    ((-500873224137:ℝ)/25000000000000) * x^6 * y^7 +
    ((-8047192461:ℝ)/195312500000) * x^6 * y^6 +
    ((21348851747223:ℝ)/50000000000000) * x^6 * y^5 +
    ((-6973145102553:ℝ)/10000000000000) * x^6 * y^4 +
    ((-37637642667051:ℝ)/25000000000000) * x^6 * y^3 +
    ((133191209985309:ℝ)/25000000000000) * x^6 * y^2 +
    ((-130444947700557:ℝ)/50000000000000) * x^6 * y^1 +
    ((-43848291506659:ℝ)/20000000000000) * x^6 * y^0 +
    ((1463:ℝ)/20000000000000) * x^4 * y^18 +
    ((-3591:ℝ)/20000000000000) * x^4 * y^17 +
    ((-59109:ℝ)/10000000000000) * x^4 * y^16 +
    ((1731603:ℝ)/25000000000000) * x^4 * y^15 +
    ((-174879:ℝ)/5000000000000) * x^4 * y^14 +
    ((-24586471:ℝ)/5000000000000) * x^4 * y^13 +
    ((5576753:ℝ)/156250000000) * x^4 * y^12 +
    ((59421453:ℝ)/1250000000000) * x^4 * y^11 +
    ((-194091418521:ℝ)/100000000000000) * x^4 * y^10 +
    ((166957741379:ℝ)/20000000000000) * x^4 * y^9 +
    ((3448796769:ℝ)/156250000000) * x^4 * y^8 +
    ((-3049835963889:ℝ)/10000000000000) * x^4 * y^7 +
    ((6973145102553:ℝ)/10000000000000) * x^4 * y^6 +
    ((112912928001153:ℝ)/50000000000000) * x^4 * y^5 +
    ((-133191209985309:ℝ)/10000000000000) * x^4 * y^4 +
    ((130444947700557:ℝ)/10000000000000) * x^4 * y^3 +
    ((131544874519977:ℝ)/4000000000000) * x^4 * y^2 +
    ((-1195999065171509:ℝ)/20000000000000) * x^4 * y^1 +
    ((450867390423853:ℝ)/50000000000000) * x^4 * y^0 +
    ((-231:ℝ)/100000000000000) * x^2 * y^20 +
    ((63:ℝ)/10000000000000) * x^2 * y^19 +
    ((1159:ℝ)/5000000000000) * x^2 * y^18 +
    ((-305577:ℝ)/100000000000000) * x^2 * y^17 +
    ((174879:ℝ)/100000000000000) * x^2 * y^16 +
    ((3512353:ℝ)/12500000000000) * x^2 * y^15 +
    ((-183849:ℝ)/78125000000) * x^2 * y^14 +
    ((-4570881:ℝ)/1250000000000) * x^2 * y^13 +
    ((17644674411:ℝ)/100000000000000) * x^2 * y^12 +
    ((-45533929467:ℝ)/50000000000000) * x^2 * y^11 +
    ((-1149598923:ℝ)/390625000000) * x^2 * y^10 +
    ((1016611987963:ℝ)/20000000000000) * x^2 * y^9 +
    ((-2988490758237:ℝ)/20000000000000) * x^2 * y^8 +
    ((-16130418285879:ℝ)/25000000000000) * x^2 * y^7 +
    ((133191209985309:ℝ)/25000000000000) * x^2 * y^6 +
    ((-391334843101671:ℝ)/50000000000000) * x^2 * y^5 +
    ((-131544874519977:ℝ)/4000000000000) * x^2 * y^4 +
    ((1195999065171509:ℝ)/10000000000000) * x^2 * y^3 +
    ((-1352602171271559:ℝ)/25000000000000) * x^2 * y^2 +
    ((-3469868827007031:ℝ)/20000000000000) * x^2 * y^1 +
    ((87835206374193:ℝ)/781250000000) * x^2 * y^0 +
    ((1:ℝ)/100000000000000) * x^0 * y^22 +
    ((-3:ℝ)/100000000000000) * x^0 * y^21 +
    ((-61:ℝ)/50000000000000) * x^0 * y^20 +
    ((1787:ℝ)/100000000000000) * x^0 * y^19 +
    ((-1143:ℝ)/100000000000000) * x^0 * y^18 +
    ((-206609:ℝ)/100000000000000) * x^0 * y^17 +
    ((61283:ℝ)/3125000000000) * x^0 * y^16 +
    ((217661:ℝ)/6250000000000) * x^0 * y^15 +
    ((-193897521:ℝ)/100000000000000) * x^0 * y^14 +
    ((1167536653:ℝ)/100000000000000) * x^0 * y^13 +
    ((34836331:ℝ)/781250000000) * x^0 * y^12 +
    ((-92419271633:ℝ)/100000000000000) * x^0 * y^11 +
    ((332054528693:ℝ)/100000000000000) * x^0 * y^10 +
    ((1792268698431:ℝ)/100000000000000) * x^0 * y^9 +
    ((-19027315712187:ℝ)/100000000000000) * x^0 * y^8 +
    ((18634992528651:ℝ)/50000000000000) * x^0 * y^7 +
    ((43848291506659:ℝ)/20000000000000) * x^0 * y^6 +
    ((-1195999065171509:ℝ)/100000000000000) * x^0 * y^5 +
    ((450867390423853:ℝ)/50000000000000) * x^0 * y^4 +
    ((1156622942335677:ℝ)/20000000000000) * x^0 * y^3 +
    ((-87835206374193:ℝ)/781250000000) * x^0 * y^2 +
    ((-244152171026127:ℝ)/12500000000000) * x^0 * y^1 +
    ((10489349699252497:ℝ)/100000000000000) * x^0 * y^0

lemma complex_identity (x y : ℝ) :
    (∑ n ∈ Finset.range 40, (c n:ℂ)*((y:ℂ)-Complex.I*x)^n)-
      (realValue x y:ℂ)=-Complex.I*((x*CertifiedLocalPolynomial.bivariatePowerValue 11 22 a
        (4*x^2) ((5/3)*(y-(12/5)))):ℂ) := by
  norm_num [c,TaoFivePrimes_RH132RoundedCoefficients14,Finset.sum_range_succ,
    CertifiedLocalPolynomial.bivariatePowerValue,
    a,entry,powerMatrix,RH132BernsteinImag134p4To135.a,RH132BernsteinImag134p4To135.entry,RH132BernsteinImag134p4To135.powerMatrix,Fin.sum_univ_succ,realValue]
  push_cast
  ring_nf
  norm_num [Complex.I_pow_eq_pow_mod]
  try simp only [Complex.I_sq,Complex.I_pow_three,pow_zero,pow_one]
  apply Complex.ext <;>
    simp [←Complex.ofReal_pow,Complex.mul_re,Complex.mul_im] <;> ring
end Imag134


namespace Imag134
theorem bernstein_checked :
    (∀ i : Fin 12, ∀ j : Fin 23, r i j=TaoZetaNumerics.bernsteinTransform 22 (a i) j) ∧
    (∀ i : Fin 12, ∀ j : Fin 23, b i j=TaoZetaNumerics.bernsteinTransform 11 (fun u => r u j) i) ∧
    (∀ i : Fin 12, ∀ j : Fin 23, (14:ℚ)≤b i j) := by
  refine ⟨?_,?_,?_⟩
  · intro i j
    fin_cases i
    · exact TaoFivePrimes.rh132_bernstein_3_row0 ⟨0,by decide⟩ j
    · exact TaoFivePrimes.rh132_bernstein_3_row0 ⟨1,by decide⟩ j
    · exact TaoFivePrimes.rh132_bernstein_3_row0 ⟨2,by decide⟩ j
    · exact TaoFivePrimes.rh132_bernstein_3_row1 ⟨0,by decide⟩ j
    · exact TaoFivePrimes.rh132_bernstein_3_row1 ⟨1,by decide⟩ j
    · exact TaoFivePrimes.rh132_bernstein_3_row1 ⟨2,by decide⟩ j
    · exact TaoFivePrimes.rh132_bernstein_3_row2 ⟨0,by decide⟩ j
    · exact TaoFivePrimes.rh132_bernstein_3_row2 ⟨1,by decide⟩ j
    · exact TaoFivePrimes.rh132_bernstein_3_row2 ⟨2,by decide⟩ j
    · exact TaoFivePrimes.rh132_bernstein_3_row3 ⟨0,by decide⟩ j
    · exact TaoFivePrimes.rh132_bernstein_3_row3 ⟨1,by decide⟩ j
    · exact TaoFivePrimes.rh132_bernstein_3_row3 ⟨2,by decide⟩ j
  · intro i j
    fin_cases i
    · exact TaoFivePrimes.rh132_bernstein_3_column0 ⟨0,by decide⟩ j
    · exact TaoFivePrimes.rh132_bernstein_3_column0 ⟨1,by decide⟩ j
    · exact TaoFivePrimes.rh132_bernstein_3_column0 ⟨2,by decide⟩ j
    · exact TaoFivePrimes.rh132_bernstein_3_column1 ⟨0,by decide⟩ j
    · exact TaoFivePrimes.rh132_bernstein_3_column1 ⟨1,by decide⟩ j
    · exact TaoFivePrimes.rh132_bernstein_3_column1 ⟨2,by decide⟩ j
    · exact TaoFivePrimes.rh132_bernstein_3_column2 ⟨0,by decide⟩ j
    · exact TaoFivePrimes.rh132_bernstein_3_column2 ⟨1,by decide⟩ j
    · exact TaoFivePrimes.rh132_bernstein_3_column2 ⟨2,by decide⟩ j
    · exact TaoFivePrimes.rh132_bernstein_3_column3 ⟨0,by decide⟩ j
    · exact TaoFivePrimes.rh132_bernstein_3_column3 ⟨1,by decide⟩ j
    · exact TaoFivePrimes.rh132_bernstein_3_column3 ⟨2,by decide⟩ j
  · exact TaoFivePrimes.rh132_bernstein_3_lower


lemma imaginary_identity (s : ℂ) :
    (TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH132RoundedCoefficients14 (10^14)
      40 (264/2) s).im = -((s.re-1/2)*
      CertifiedLocalPolynomial.bivariatePowerValue 11 22 a
        (4*(s.re-1/2)^2) ((5/3)*(s.im-(672/5)))) := by
  have h := complex_identity (s.re-1/2) (s.im-264/2)
  have hw : -Complex.I*(s-RH1000Analytic.CertifiedLocalXi.center (264/2)) =
      ((s.im-264/2:ℝ):ℂ)-Complex.I*((s.re-1/2:ℝ):ℂ) := by
    apply Complex.ext <;> simp [RH1000Analytic.CertifiedLocalXi.center] <;> ring
  unfold TaoFivePrimes_RHLocalRationalPolynomial
  simp only [hw]
  have hr := congrArg Complex.im h
  simp only [Complex.sub_im,Complex.ofReal_im,sub_zero,Complex.mul_im,
    Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,
    zero_mul,neg_zero,zero_add,neg_one_mul,one_mul] at hr
  have he : (5/3:ℝ)*(s.im-264/2-(12/5))=(5/3)*(s.im-(672/5)) := by ring
  rw [he] at hr
  simp only [c,Complex.ofReal_div,Complex.ofReal_intCast] at hr
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] at hr
  simp only [Complex.ofReal_intCast]
  norm_num only at hr ⊢
  exact hr

open scoped unitInterval
attribute [local irreducible] a r b
lemma ratio_positive (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : (672/5:ℝ) ≤ s.im) (hb : s.im ≤ (135:ℝ)) :
    14 ≤ CertifiedLocalPolynomial.bivariatePowerValue 11 22 a
      (4*(s.re-1/2)^2) ((5/3)*(s.im-(672/5))) := by
  let x : Set.Icc (0:ℝ) 1 := ⟨4*(s.re-1/2)^2,⟨by positivity,by
    nlinarith [mul_nonneg h0 (show 0≤1-s.re by linarith)]⟩⟩
  let y : Set.Icc (0:ℝ) 1 := ⟨(5/3)*(s.im-(672/5)),⟨by linarith,by linarith⟩⟩
  have hr : ∀ i, r i=TaoZetaNumerics.bernsteinTransform 22 (a i) := by
    intro i
    funext j
    exact bernstein_checked.1 i j
  have hc : ∀ j, (fun i => b i j)=TaoZetaNumerics.bernsteinTransform 11
      (fun i => r i j) := by
    intro j
    funext i
    exact bernstein_checked.2.1 i j
  have hl : ∀ i j, (14:ℝ)≤(b i j:ℝ) := by
    intro i j
    exact_mod_cast bernstein_checked.2.2 i j
  exact CertifiedLocalPolynomial.bivariate_bernstein_lower 11 22 a r b hr hc 14 hl x y
end Imag134

theorem imag_certificate (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : (672/5:ℝ) ≤ s.im) (hb : s.im ≤ (135:ℝ)) :
    (14:ℝ)*|s.re-1/2| ≤
      |(TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH132RoundedCoefficients14 (10^14)
        40 (264/2) s).im| := by
  have hp := Imag134.ratio_positive s h0 h1 ha hb
  rw [Imag134.imaginary_identity,abs_neg,abs_mul,abs_of_nonneg (by linarith :
    0 ≤ CertifiedLocalPolynomial.bivariatePowerValue 11 22 Imag134.a
      (4*(s.re-1/2)^2) ((5/3)*(s.im-(672/5))))]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hp (abs_nonneg (s.re-1/2))



section Slice134Assembly

open Complex Metric Set Finset
open HurwitzZeta MeasureTheory
open scoped ComplexConjugate

/- The derivative bound is supplied by the platform import
`Theorems.Thm_TaoFivePrimes_rh132_xi_polynomial_derivative_bound`
above (Proved theorem fdbbf536); it is cited below by its platform name.
The xi approximation is not used (see the local verification file). -/


namespace Slice134

/-- Bridge lemma: the N=60 polynomial in the derivative bound equals the
N=40 polynomial in the certificate, at the same center 132. Terms with
index ≥ 40 vanish because the coefficient list has length 40, so
`getD` returns the default 0 there. -/
lemma poly60_eq_poly40 (s : ℂ) :
    TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH132RoundedCoefficients14
        (10^14) 60 132 s =
    TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH132RoundedCoefficients14
        (10^14) 40 132 s := by
  have hzero : ∀ i : ℕ,
      ((TaoFivePrimes_RH132RoundedCoefficients14.getD (40 + i) 0:ℝ)/((10^14:ℕ):ℝ):ℂ) *
        (-Complex.I*(s - RH1000Analytic.CertifiedLocalXi.center 132))^(40 + i) = 0 := by
    intro i
    have hlen : TaoFivePrimes_RH132RoundedCoefficients14.length = 40 := rfl
    have hcoeff : TaoFivePrimes_RH132RoundedCoefficients14.getD (40 + i) 0 = 0 := by
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_none_iff.mpr
          (show TaoFivePrimes_RH132RoundedCoefficients14.length ≤ 40 + i by omega)]
      rfl
    rw [hcoeff]
    simp
  unfold TaoFivePrimes_RHLocalRationalPolynomial
  rw [show (60:ℕ) = 40 + 20 from rfl, Finset.sum_range_add,
    Finset.sum_eq_zero (s := Finset.range 20) (fun i _ => hzero i), add_zero]

/-- The local xi function is entire (Mathlib: `differentiable_completedZeta₀`). -/
lemma xi_entire : Differentiable ℂ RH1000Analytic.CertifiedLocalXi.xi := by
  unfold RH1000Analytic.CertifiedLocalXi.xi
  have hΛ := differentiable_completedZeta₀
  fun_prop

/-- The N=60 polynomial is entire. -/
lemma poly_differentiable : Differentiable ℂ
    (fun w => TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH132RoundedCoefficients14
      (10^14) 60 132 w) := by
  unfold TaoFivePrimes_RHLocalRationalPolynomial
  fun_prop

/-- The error function `E(w) = 10^43 * xi(w) - P60(w)`. -/
noncomputable def E (w : ℂ) : ℂ :=
  (10^43:ℂ)*RH1000Analytic.CertifiedLocalXi.xi w -
    TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH132RoundedCoefficients14
      (10^14) 60 132 w

lemma E_differentiable : Differentiable ℂ E :=
  (xi_entire.const_mul _).sub poly_differentiable

/-- Center arithmetic: `center y - center 132 = (y - 132) * I`. -/
lemma center_sub_center (y : ℝ) :
    RH1000Analytic.CertifiedLocalXi.center y -
      RH1000Analytic.CertifiedLocalXi.center 132 =
    ((y - 132:ℝ):ℂ) * Complex.I := by
  apply Complex.ext <;> simp [RH1000Analytic.CertifiedLocalXi.center] <;> ring

/-- Distance from a point to its critical-line projection. -/
lemma proj_dist (z : ℂ) :
    ‖z - RH1000Analytic.CertifiedLocalXi.center z.im‖ = |z.re - 1/2| := by
  have he : z - RH1000Analytic.CertifiedLocalXi.center z.im =
      ((z.re - 1/2:ℝ):ℂ) := by
    apply Complex.ext <;> simp [RH1000Analytic.CertifiedLocalXi.center]
  rw [he, Complex.norm_real, Real.norm_eq_abs]

/-- Every point of the 134.4-135 rectangle lies in the derivative ball:
its squared distance to center 132 is at most 1/4 + 9 = 37/4 < (61/20)^2. -/
lemma z_in_ball (z : ℂ) (h0 : 0 ≤ z.re) (h1 : z.re ≤ 1)
    (ha : (672/5:ℝ) ≤ z.im) (hb : z.im ≤ (135:ℝ)) :
    ‖z - RH1000Analytic.CertifiedLocalXi.center 132‖ ≤ 61/20 := by
  have hsq : ‖z - RH1000Analytic.CertifiedLocalXi.center 132‖^2 =
      (z.re - 1/2)^2 + (z.im - 132)^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [RH1000Analytic.CertifiedLocalXi.center]
    ring
  have hbound : (z.re - 1/2)^2 + (z.im - 132)^2 ≤ (61/20)^2 := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ (z.re - 1/2) + 1/2 by linarith)
      (show (0:ℝ) ≤ 1/2 - (z.re - 1/2) by linarith),
      mul_nonneg (show (0:ℝ) ≤ 3 - (z.im - 132) by linarith)
      (show (0:ℝ) ≤ (z.im - 132) + 3 by linarith)]
  have hnorm : ‖z - RH1000Analytic.CertifiedLocalXi.center 132‖ =
      Real.sqrt ((z.re - 1/2)^2 + (z.im - 132)^2) := by
    rw [← Real.sqrt_sq (norm_nonneg _), hsq]
  rw [hnorm]
  calc Real.sqrt ((z.re - 1/2)^2 + (z.im - 132)^2)
      ≤ Real.sqrt ((61/20)^2) := Real.sqrt_le_sqrt hbound
    _ = 61/20 := Real.sqrt_sq (by norm_num)

/-- The critical-line projection also lies in the derivative ball. -/
lemma proj_in_ball (z : ℂ) (ha : (672/5:ℝ) ≤ z.im) (hb : z.im ≤ (135:ℝ)) :
    ‖RH1000Analytic.CertifiedLocalXi.center z.im -
      RH1000Analytic.CertifiedLocalXi.center 132‖ ≤ 61/20 := by
  rw [center_sub_center, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-! ### Conjugation of the completed zeta function (adapted from the
accepted 105-106 proof, which proved these lemmas for the same
`hurwitzEvenFEPair 0` pair that the platform analytic model defines
as `RH1000Analytic.ZetaSix.P`). -/

end Slice134

namespace RH1000Analytic.ZetaSix

lemma f_modif_of_one_lt {t : ℝ} (ht : 1 < t) :
    P.f_modif t = ((evenKernel 0 t : ℝ) : ℂ) - 1 := by
  simp [P, WeakFEPair.f_modif, hurwitzEvenFEPair, ht, not_lt.2 ht.le,
    Set.indicator_of_notMem]

lemma f_modif_of_lt_one {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    P.f_modif t = ((evenKernel 0 t : ℝ) : ℂ) - ((t ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) := by
  simp [P, WeakFEPair.f_modif, hurwitzEvenFEPair, h0, h1, not_lt.2 h1.le]
  norm_num

lemma f_modif_one : P.f_modif 1 = 0 := by
  simp [P, WeakFEPair.f_modif]

end RH1000Analytic.ZetaSix

namespace Slice134

lemma conj_kernel {t : ℝ} (ht : 0 < t) :
    conj (RH1000Analytic.ZetaSix.P.f_modif t) =
      RH1000Analytic.ZetaSix.P.f_modif t := by
  rcases lt_trichotomy t 1 with h | rfl | h
  · rw [RH1000Analytic.ZetaSix.f_modif_of_lt_one ht h]
    simp
  · rw [RH1000Analytic.ZetaSix.f_modif_one]
    simp
  · rw [RH1000Analytic.ZetaSix.f_modif_of_one_lt h]
    simp

lemma completedZeta_conj (s : ℂ) :
    completedRiemannZeta₀ (conj s) = conj (completedRiemannZeta₀ s) := by
  change mellin RH1000Analytic.ZetaSix.P.f_modif (conj s / 2) / 2 =
    conj (mellin RH1000Analytic.ZetaSix.P.f_modif (s / 2) / 2)
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

/-- xi is real on the critical line: `conj (center y) = 1 - center y`,
conjugation of Λ₀, and the functional equation Λ₀(1 - s) = Λ₀(s). -/
lemma xi_critical_real (y : ℝ) :
    (RH1000Analytic.CertifiedLocalXi.xi
      (RH1000Analytic.CertifiedLocalXi.center y)).im = 0 := by
  have hc : conj (RH1000Analytic.CertifiedLocalXi.center y) =
      1 - RH1000Analytic.CertifiedLocalXi.center y := by
    apply Complex.ext <;> simp [RH1000Analytic.CertifiedLocalXi.center] <;> ring
  have he := completedZeta_conj (RH1000Analytic.CertifiedLocalXi.center y)
  rw [hc, completedRiemannZeta₀_one_sub] at he
  have hi := congrArg Complex.im he
  simp only [conj_im] at hi
  have hΛ : (completedRiemannZeta₀
      (RH1000Analytic.CertifiedLocalXi.center y)).im = 0 := by linarith
  have hf : (RH1000Analytic.CertifiedLocalXi.center y *
      (RH1000Analytic.CertifiedLocalXi.center y - 1) / 2).im = 0 := by
    norm_num [RH1000Analytic.CertifiedLocalXi.center, Complex.mul_im]
    ring
  unfold RH1000Analytic.CertifiedLocalXi.xi
  simp [Complex.mul_im, hf, hΛ]

/-- The polynomial is real on the critical line: the rotated variable
`-I * (center y - center 132)` equals the real number `y - 132`, so
every term is a real coefficient times a real power. -/
lemma poly60_critical_real (y : ℝ) :
    (TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH132RoundedCoefficients14
      (10^14) 60 132 (RH1000Analytic.CertifiedLocalXi.center y)).im = 0 := by
  have hrot : -Complex.I * (RH1000Analytic.CertifiedLocalXi.center y -
      RH1000Analytic.CertifiedLocalXi.center 132) = ((y - 132:ℝ):ℂ) := by
    apply Complex.ext <;> simp [RH1000Analytic.CertifiedLocalXi.center] <;> ring
  have he : TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH132RoundedCoefficients14
      (10^14) 60 132 (RH1000Analytic.CertifiedLocalXi.center y) =
      ((∑ n ∈ Finset.range 60,
        ((TaoFivePrimes_RH132RoundedCoefficients14.getD n 0:ℝ)/((10^14:ℕ):ℝ)) *
          (y - 132)^n : ℝ):ℂ) := by
    simp only [TaoFivePrimes_RHLocalRationalPolynomial, hrot, Complex.ofReal_sum,
      Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow,
      Complex.ofReal_intCast, Complex.ofReal_natCast]
  rw [he]
  exact Complex.ofReal_im _

/-- The error function is imaginary-zero on the critical line. -/
lemma E_critical_real (y : ℝ) :
    (E (RH1000Analytic.CertifiedLocalXi.center y)).im = 0 := by
  unfold E
  rw [Complex.sub_im]
  have hxi : ((10^43:ℂ) * RH1000Analytic.CertifiedLocalXi.xi
      (RH1000Analytic.CertifiedLocalXi.center y)).im = 0 := by
    rw [Complex.mul_im, xi_critical_real, mul_zero, zero_add]
    have h10 : (10^43:ℂ).im = 0 := by
      rw [show (10^43:ℂ) = ((10^43:ℝ):ℂ) by norm_num]
      exact Complex.ofReal_im _
    rw [h10, zero_mul]
  rw [hxi, poly60_critical_real, sub_zero]

/-- Lipschitz bound for the imaginary part of the error, directly from
the Proved derivative bound via the mean value theorem on the closed
ball of radius 61/20 about center 132 (no Cauchy step, no xi
approximation). The segment from `z` to its critical-line projection
stays in the ball by convexity. -/
lemma imag_error_bound (z : ℂ) (h0 : 0 ≤ z.re) (h1 : z.re ≤ 1)
    (ha : (672/5:ℝ) ≤ z.im) (hb : z.im ≤ (135:ℝ)) :
    |(E z).im| ≤ (27/50) * |z.re - 1/2| := by
  have hEp : (E (RH1000Analytic.CertifiedLocalXi.center z.im)).im = 0 :=
    E_critical_real z.im
  have hball_z : z ∈ Metric.closedBall
      (RH1000Analytic.CertifiedLocalXi.center 132) (61/20:ℝ) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact z_in_ball z h0 h1 ha hb
  have hball_p : RH1000Analytic.CertifiedLocalXi.center z.im ∈ Metric.closedBall
      (RH1000Analytic.CertifiedLocalXi.center 132) (61/20:ℝ) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact proj_in_ball z ha hb
  have hdiff : ∀ w ∈ Metric.closedBall
      (RH1000Analytic.CertifiedLocalXi.center 132) (61/20:ℝ),
      DifferentiableAt ℂ E w :=
    fun w _ => E_differentiable.differentiableAt
  have hbound : ∀ w ∈ Metric.closedBall
      (RH1000Analytic.CertifiedLocalXi.center 132) (61/20:ℝ),
      ‖deriv E w‖ ≤ 27/50 := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    show ‖deriv (fun w : ℂ => (10^43:ℂ)*RH1000Analytic.CertifiedLocalXi.xi w -
      TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH132RoundedCoefficients14
        (10^14) 60 132 w) w‖ ≤ 27/50
    exact TaoFivePrimes.rh132_xi_polynomial_derivative_bound w hw
  have hlip := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
    (convex_closedBall _ _) hball_p hball_z
  have hdist : ‖z - RH1000Analytic.CertifiedLocalXi.center z.im‖ = |z.re - 1/2| :=
    proj_dist z
  have him : (E z).im = (E z - E (RH1000Analytic.CertifiedLocalXi.center z.im)).im := by
    rw [Complex.sub_im, hEp, sub_zero]
  rw [him]
  calc |(E z - E (RH1000Analytic.CertifiedLocalXi.center z.im)).im|
      ≤ ‖E z - E (RH1000Analytic.CertifiedLocalXi.center z.im)‖ :=
        Complex.abs_im_le_norm _
    _ ≤ (27/50) * ‖z - RH1000Analytic.CertifiedLocalXi.center z.im‖ := hlip
    _ = (27/50) * |z.re - 1/2| := by rw [hdist]

/-- xi has no zero off the critical line in the rectangle: the
certificate gives `|Im P40| ≥ 14|σ - 1/2|` while the error bound gives
`|Im E| ≤ (27/50)|σ - 1/2|`, and `E = -P40` at a zero of xi. -/
lemma xi_nonzero_off_line (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : (672/5:ℝ) ≤ s.im) (hb : s.im ≤ (135:ℝ)) (hneq : s.re ≠ 1/2) :
    RH1000Analytic.CertifiedLocalXi.xi s ≠ 0 := by
  intro hzero
  have hcert := imag_certificate s h0 h1 ha hb
  rw [show (264/2:ℝ) = 132 by norm_num] at hcert
  have hEim : |(E s).im| =
      |(TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH132RoundedCoefficients14
        (10^14) 40 132 s).im| := by
    have h1 : E s = - TaoFivePrimes_RHLocalRationalPolynomial
        TaoFivePrimes_RH132RoundedCoefficients14 (10^14) 40 132 s := by
      unfold E
      rw [hzero, poly60_eq_poly40]
      simp
    rw [h1, Complex.neg_im, abs_neg]
  have herr := imag_error_bound s h0 h1 ha hb
  rw [hEim] at herr
  have hpos : 0 < |s.re - 1/2| := abs_pos.mpr (sub_ne_zero.mpr hneq)
  linarith

/-- xi-to-zeta transfer (adapted from the accepted 105-106 proof). -/
lemma xi_nonzero_implies_zeta {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (hXi : RH1000Analytic.CertifiedLocalXi.xi s ≠ 0) : riemannZeta s ≠ 0 := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at h0
  have hs1 : s ≠ 1 := fun h => by simp [h] at h1
  have h1s : (1:ℂ) - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  rw [riemannZeta_def_of_ne_zero hs0]
  intro hz
  rcases div_eq_zero_iff.mp hz with hz | hz
  · apply hXi
    have hh := completedRiemannZeta_eq s
    rw [hz] at hh
    have hsum : completedRiemannZeta₀ s = 1/s + 1/(1-s) := by
      linear_combination -hh
    unfold RH1000Analytic.CertifiedLocalXi.xi
    rw [hsum]
    field_simp
    ring
  · exact Complex.Gammaℝ_ne_zero_of_re_pos h0 hz

end Slice134

end Slice134Assembly

/-- The full 134.4-135 slice, statement character-identical to platform
theorem TaoFivePrimes.rh_verified_slice_134p4_135 (ebdfa137) modulo the
name `solution`. -/
theorem solution (s : ℂ) (hs : riemannZeta s = 0) (h0 : 0 < s.re) (h1 : s.re < 1)
    (ha : (672/5:ℝ) ≤ s.im) (hb : s.im ≤ (135:ℝ)) : s.re = 1/2 := by
  by_contra hneq
  have hxi := Slice134.xi_nonzero_off_line s h0.le h1.le ha hb hneq
  exact Slice134.xi_nonzero_implies_zeta h0 h1 hxi hs

