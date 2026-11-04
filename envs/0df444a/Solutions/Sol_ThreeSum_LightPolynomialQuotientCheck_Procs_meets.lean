-- Prove2me | solution 1 for ThreeSum.LightPolynomialQuotientCheck.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:33:38.829846+00:00
-- url     : https://prove2.me/submissions/e8341ca8-c7b9-437b-82d4-d4fc07e07012

import Definitions.Def_Submission_ThreeSum_LightPolynomialProductArray
import Definitions.Def_Submission_ThreeSum_LightPolynomialProductCheck
import Definitions.Def_Submission_ThreeSum_LightPrimeAddArray
import Definitions.Def_Submission_ThreeSum_LightPolynomialQuotientCheck
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_ThreeSum_LightCoefficientDecode_meets
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_meets
import Theorems.Thm_ThreeSum_LightPolynomialProductArray_meets
import Theorems.Thm_ThreeSum_LightPolynomialProductCheck_meets
import Theorems.Thm_ThreeSum_LightPrimeAddArray_meets
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
set_option autoImplicit false
open ThreeSum ThreeSum.LightPolynomialQuotientCheck
open Light
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program} {depth : ℕ}
namespace ThreeSum.LightPolynomialQuotientCheck
namespace Procs
theorem _root_.solution {main aBase bBase hBase fBase rBase productWork sumWork d p : ℕ} (S : Procs P main) (μ : ℕ → ℤ)
    (x y h f r : ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word) (hd : depth + 3 < lim.depth) (hp : 1 < p)
    (ha : aBase + d ≤ productWork) (hb : bBase + d ≤ productWork) (hh : hBase + d ≤ productWork)
    (hf : fBase + (d + 1) ≤ productWork) (hr : rBase + 2 * d ≤ productWork) (hprod : productWork + 2 * d ≤ sumWork)
    (hspace : sumWork + 2 * d ≤ lim.space) (hxRead : ∀ i < d, μ (aBase + i) = (x i : ℤ))
    (hyRead : ∀ i < d, μ (bBase + i) = (y i : ℤ)) (hhRead : ∀ i < d, μ (hBase + i) = (h i : ℤ))
    (hfRead : ∀ i < d + 1, μ (fBase + i) = (f i : ℤ)) (hrRead : ∀ i < 2 * d, μ (rBase + i) = (r i : ℤ))
    (hxBound : ∀ i < d, x i < p) (hyBound : ∀ i < d, y i < p) (hhBound : ∀ i < d, h i < p)
    (hfBound : ∀ i < d + 1, f i < p) (hrBound : ∀ i < 2 * d, r i < p) (hword : (word d p : ℤ) ≤ lim.word) :
    Meets lim P main depth [aBase, bBase, hBase, fBase, rBase, d, p, productWork, sumWork] μ (time d p)
      (fun z ν => z = LightPolynomialProductCheck.flag p x y (expected p d h f r) d d (2 * d) ∧ Kept μ ν productWork) :=
  by
  have hbudget (z : ℕ) (hz : z ≤ word d p) : (z : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hz).trans hword
  have hcommon : 20 * ((d + 1) * (p + 1) ^ 2 + 2 * d + (d + 1) + 10) ≤ word d p :=
    by
    unfold word
    have hpow := Nat.zero_le ((p + 1) ^ 2)
    nlinarith
  have hwprod := hbudget _ hcommon
  have hwcheck := hbudget (20 * ((d + 1) * (p + 1) ^ 2 + 2 * d + d + 10)) (by omega)
  have hwadd : (LightPrimeCoefficient.word p : ℤ) ≤ lim.word :=
    by
    apply hbudget
    unfold LightPrimeCoefficient.word word
    have hh : (p + 1) ^ 2 ≤ (d + 2) * (p + 1) ^ 2 := Nat.le_mul_of_pos_left _ (by omega)
    nlinarith
  have hdWord := hbudget d (by unfold word; omega)
  have htwoDWord := hbudget (2 * d) (by unfold word; omega)
  have hpWord := hbudget p (by unfold word; omega)
  have hsuccWord := hbudget (d + 1) (by unfold word; omega)
  have h2 : (2 : ℤ) ≤ lim.word := hbudget 2 (by unfold word; omega)
  apply Meets.of_body S.mainBody
  unfold body time
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen (2 * d : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightPolynomialProductArray.time,
            LightPrimeAddArray.time, LightPolynomialProductCheck.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightPolynomialProductArray.time, LightPrimeAddArray.time, LightPolynomialProductCheck.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightPolynomialProductArray.time,
            LightPrimeAddArray.time, LightPolynomialProductCheck.time] <;>
          omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    first
    |
      refine
        _root_.Light.Ends.callToThen
          ((LightPolynomialProductArray.meets (depth := depth + 1) S.productBody S.coefficientBody S.rawBody S.digitBody
              S.divideBody μ h f hw (by omega) hh hf (by omega) hhRead hfRead hhBound hfBound hwprod)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightPolynomialProductArray.meets (depth := depth + 1) S.productBody S.coefficientBody S.rawBody S.digitBody
            S.divideBody μ h f hw (by omega) hh hf (by omega) hhRead hfRead hhBound hfBound hwprod)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightPolynomialProductArray.time,
            LightPrimeAddArray.time, LightPolynomialProductCheck.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightPolynomialProductArray.time, LightPrimeAddArray.time, LightPolynomialProductCheck.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightPolynomialProductArray.time,
            LightPrimeAddArray.time, LightPolynomialProductCheck.time] <;>
          omega)
    on_goal -1 => (rintro v₁ μ₁ ⟨productValues, keep₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have rValues (i : ℕ) (hi : i < 2 * d) : μ₁ (rBase + i) = (r i : ℤ) :=
    (keep₁ _ (Or.inl (by omega))).trans (hrRead i hi)
  have productBound (i : ℕ) (_hi : i < 2 * d) : LightPolynomialCoefficient.coefficient p h f d (d + 1) i < p :=
    Nat.mod_lt _ (by omega)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    first
    |
      refine
        _root_.Light.Ends.callToThen
          ((LightPrimeAddArray.meets (depth := depth + 1) S.addBody S.mulAddBody S.divideBody μ₁
              (fun i => LightPolynomialCoefficient.coefficient p h f d (d + 1) i) r hw (by omega) hp hprod (by omega)
              hspace productValues rValues productBound hrBound hwadd)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightPrimeAddArray.meets (depth := depth + 1) S.addBody S.mulAddBody S.divideBody μ₁
            (fun i => LightPolynomialCoefficient.coefficient p h f d (d + 1) i) r hw (by omega) hp hprod (by omega)
            hspace productValues rValues productBound hrBound hwadd)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightPolynomialProductArray.time,
            LightPrimeAddArray.time, LightPolynomialProductCheck.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightPolynomialProductArray.time, LightPrimeAddArray.time, LightPolynomialProductCheck.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightPolynomialProductArray.time,
            LightPrimeAddArray.time, LightPolynomialProductCheck.time] <;>
          omega)
    on_goal -1 => (rintro v₂ μ₂ ⟨sumValues, keep₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have xValues (i : ℕ) (hi : i < d) : μ₂ (aBase + i) = (x i : ℤ) := by
    rw [keep₂ _ (Or.inl (by omega)), keep₁ _ (Or.inl (by omega)), hxRead i hi]
  have yValues (i : ℕ) (hi : i < d) : μ₂ (bBase + i) = (y i : ℤ) := by
    rw [keep₂ _ (Or.inl (by omega)), keep₁ _ (Or.inl (by omega)), hyRead i hi]
  have expectedValues (i : ℕ) (hi : i < 2 * d) : μ₂ (sumWork + i) = (expected p d h f r i : ℤ) := sumValues i hi
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    first
    |
      refine
        _root_.Light.Ends.callToThen
          ((LightPolynomialProductCheck.meets (depth := depth + 1) S.checkBody S.coefficientBody S.rawBody S.digitBody
              S.divideBody μ₂ x y (expected p d h f r) hw (by omega) (by omega) (by omega) hspace xValues yValues
              expectedValues hxBound hyBound hwcheck)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightPolynomialProductCheck.meets (depth := depth + 1) S.checkBody S.coefficientBody S.rawBody S.digitBody
            S.divideBody μ₂ x y (expected p d h f r) hw (by omega) (by omega) (by omega) hspace xValues yValues
            expectedValues hxBound hyBound hwcheck)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightPolynomialProductArray.time,
            LightPrimeAddArray.time, LightPolynomialProductCheck.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightPolynomialProductArray.time, LightPrimeAddArray.time, LightPolynomialProductCheck.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightPolynomialProductArray.time,
            LightPrimeAddArray.time, LightPolynomialProductCheck.time] <;>
          omega)
    on_goal -1 => (rintro z ν ⟨hz, hν⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst ν
  refine ⟨hz, ?_⟩
  intro i hi
  change μ₂ i = μ i
  rw [keep₂ _ (Or.inl (by omega)), keep₁ _ (Or.inl hi)]
end Procs
end ThreeSum.LightPolynomialQuotientCheck
