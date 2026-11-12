-- Prove2me | solution 1 for OddOrder.BG.AppC.FieldNormalizerData.relationC9_w3_word
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:31:52.501975+00:00
-- url     : https://prove2.me/submissions/eda0a80e-16f5-4c31-b303-03caaad94e6f

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/AppC_NormSetBasic.lean
--   OddOrder/BG/AppC_LemmaC3_NormalForms.lean
--   OddOrder/BG/AppC_LemmaC3_Step4Capstone.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_ScalarCalculus
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_NormalForms
import Definitions.Def_OddOrder_BG_AppC_NormSetBasic
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_Step4Capstone
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Ring.AddAut
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.ZMod
import Theorems.Thm_OddOrder_BG_AppC_FieldNormalizerData_relationC7

-- ===== OddOrder/BG/AppC_NormSetBasic.lean =====
namespace OddOrder.BG.AppC.NormSet

open scoped Pointwise

open Polynomial Finset

variable (p q : ℕ)

/-- **BG Appendix C, Lemma C.3, Step 4**: in `𝔽_{p^q}`, the `p`-power
Frobenius fixes the prime-field element `2`. -/
lemma pow_p_natCast_two [Fact p.Prime] :
    (2 : GaloisField p q) ^ p = 2 := by
  simpa [frobenius_def] using
    (map_natCast (frobenius (GaloisField p q) p) 2)

/-- **BG Appendix C, Lemma C.3, Step 4**: the BG norm is compatible with the
`p`-power Frobenius. -/
theorem normN_pow_p [Fact p.Prime] (hq : q ≠ 0) (a : GaloisField p q) :
    normN p q (a ^ p) = (normN p q a) ^ p := by
  rw [normN_eq_algebraMap_norm p q hq, normN_eq_algebraMap_norm p q hq]
  rw [← map_pow]
  rw [← (Algebra.norm (ZMod p) (S := GaloisField p q)).map_pow a p]

/-- **BG Appendix C, Lemma C.3, Step 4**: the `p`-power Frobenius carries
`2 - a` to `2 - a^p`. -/
theorem two_sub_pow_p [Fact p.Prime] (a : GaloisField p q) :
    ((2 : GaloisField p q) - a) ^ p = (2 : GaloisField p q) - a ^ p := by
  have h := map_sub (frobenius (GaloisField p q) p) (2 : GaloisField p q) a
  simpa [frobenius_def, pow_p_natCast_two p q] using h

/-- **BG Appendix C, Lemma C.3, Step 4**: the norm set `E` is stable under
the `p`-power Frobenius. -/
theorem normSetE_pow_p [Fact p.Prime] (hq : q ≠ 0) {a : GaloisField p q}
    (ha : a ∈ normSetE p q) :
    a ^ p ∈ normSetE p q := by
  constructor
  · rw [normN_pow_p p q hq, ha.1, one_pow]
  · rw [← two_sub_pow_p p q a, normN_pow_p p q hq, ha.2, one_pow]

/-- **BG Appendix C, Lemma C.3, Step 4**: if `a,b ∈ E` and `a+b=2`, then
their Frobenius images again lie in `E` and still sum to `2`. -/
theorem normSetE_frobenius_pair [Fact p.Prime] (hq : q ≠ 0)
    {a b : GaloisField p q} (ha : a ∈ normSetE p q) (hb : b ∈ normSetE p q)
    (hsum : a + b = 2) :
    a ^ p ∈ normSetE p q ∧ b ^ p ∈ normSetE p q ∧ a ^ p + b ^ p = 2 := by
  refine ⟨normSetE_pow_p p q hq ha, normSetE_pow_p p q hq hb, ?_⟩
  rw [add_pow_p p q, hsum, pow_p_natCast_two p q]

end OddOrder.BG.AppC.NormSet

-- ===== OddOrder/BG/AppC_LemmaC3_NormalForms.lean =====
namespace OddOrder.BG.AppC

open OddOrder.GroupTheory

open scoped Pointwise

open scoped BigOperators

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

section Step4

namespace Step4C5NormalForms

/-- Under `(C.8)`, the first `(C.7)` word is raised to its `p`-th power. -/
theorem frobenius_w1
    {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) :
    forms.frobenius.w1 = forms.w1 ^ p := by
  simp [frobenius, w1, map_pow, mul_pow]

/-- Under `(C.8)`, the second `(C.7)` word is raised to its `p`-th power. -/
theorem frobenius_w2
    {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) :
    forms.frobenius.w2 = forms.w2 ^ p := by
  simp [frobenius, w2, map_pow, mul_pow]

/-- Under `(C.8)`, the third `(C.7)` word is raised to its `p`-th power. -/
theorem frobenius_w3
    {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) :
    forms.frobenius.w3 = forms.w3 ^ p := by
  simp [frobenius, w3, map_pow, mul_pow]

end Step4C5NormalForms

/-- BG Appendix C `(C.8)` Frobenius entry: if the inverse field values of `a` and
`b` lie in `E` and satisfy the companion equation, then the inverse field values of
`a^p` and `b^p` again lie in `E` and satisfy the same companion equation. -/
theorem unitVal_inv_frobenius_pair (hq : q ≠ 0)
    {a b : NormSet.normOneUnits p q}
    (ha : unitVal a⁻¹ ∈ NormSet.normSetE p q)
    (hb : unitVal b⁻¹ ∈ NormSet.normSetE p q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2) :
    unitVal (a ^ p)⁻¹ ∈ NormSet.normSetE p q ∧
      unitVal (b ^ p)⁻¹ ∈ NormSet.normSetE p q ∧
        unitVal (a ^ p)⁻¹ + unitVal (b ^ p)⁻¹ = 2 := by
  have hpair := NormSet.normSetE_frobenius_pair
    p q hq ha hb hab
  simpa [unitVal, map_pow] using hpair

end Step4

end FieldNormalizerData

end OddOrder.BG.AppC

-- ===== OddOrder/BG/AppC_LemmaC3_Step4Capstone.lean =====
namespace OddOrder.BG.AppC

open OddOrder.GroupTheory

open scoped Pointwise

open scoped BigOperators

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

section Step4

/-- BG Appendix C exact `(C.9)` word equation.  This is the equality displayed
just before `(C.9)`: after comparing `(C.7)` for `(a,b)` with the Frobenius-powered
`(C.7)`, the remaining `w₁/w₂` word is a `t²`-conjugate of
`S₁ W₃^(p-1) S₁⁻¹`. -/
theorem _root_.solution
    (data : FieldNormalizerData p q G)
    {a b : NormSet.normOneUnits p q}
    (ha : unitVal a⁻¹ ∈ NormSet.normSetE p q)
    (hb : unitVal b⁻¹ ∈ NormSet.normSetE p q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b) :
    let S1 := data.sigma (primeLineElement p q forms.c1)
    let S3 := data.sigma (primeLineElement p q forms.c3)
    let W1 := data.sigma (SemidirectProduct.inr forms.w1 : NormSet.normOneFrobeniusGroup p q)
    let W2 := data.sigma (SemidirectProduct.inr forms.w2 : NormSet.normOneFrobeniusGroup p q)
    let W1p := data.sigma
      (SemidirectProduct.inr (forms.w1 ^ p) : NormSet.normOneFrobeniusGroup p q)
    let W2p := data.sigma
      (SemidirectProduct.inr (forms.w2 ^ p) : NormSet.normOneFrobeniusGroup p q)
    let W3pow := data.sigma
      (SemidirectProduct.inr (forms.w3 ^ (p - 1)) :
        NormSet.normOneFrobeniusGroup p q)
    (data.t ^ 2)⁻¹ * (W2p⁻¹ * S3⁻¹ * W1p⁻¹ * W1 * S3 * W2) * data.t ^ 2 =
      S1 * W3pow * S1⁻¹ := by
  classical
  dsimp only
  let S1 := data.sigma (primeLineElement p q forms.c1)
  let S2 := data.sigma (primeLineElement p q forms.c2)
  let S3 := data.sigma (primeLineElement p q forms.c3)
  let W1 := data.sigma (SemidirectProduct.inr forms.w1 : NormSet.normOneFrobeniusGroup p q)
  let W2 := data.sigma (SemidirectProduct.inr forms.w2 : NormSet.normOneFrobeniusGroup p q)
  let W3 := data.sigma (SemidirectProduct.inr forms.w3 : NormSet.normOneFrobeniusGroup p q)
  let W1p := data.sigma
    (SemidirectProduct.inr (forms.w1 ^ p) : NormSet.normOneFrobeniusGroup p q)
  let W2p := data.sigma
    (SemidirectProduct.inr (forms.w2 ^ p) : NormSet.normOneFrobeniusGroup p q)
  let W3p := data.sigma
    (SemidirectProduct.inr (forms.w3 ^ p) : NormSet.normOneFrobeniusGroup p q)
  let W3pow := data.sigma
    (SemidirectProduct.inr (forms.w3 ^ (p - 1)) :
      NormSet.normOneFrobeniusGroup p q)
  let A := W1 * S3 * W2
  let Ap := W1p * S3 * W2p
  let X := S1 * W3pow * S1⁻¹
  have hpow_pair := unitVal_inv_frobenius_pair data.q_prime.ne_zero ha hb hab
  have hC7 := data.relationC7 hab forms
  have hC7p := data.relationC7 hpow_pair.2.2 forms.frobenius
  have hC7' :
      data.t⁻¹ * S2 * data.t⁻¹ = (A * data.t ^ 2 * S1 * W3)⁻¹ := by
    simpa [A, S1, S2, S3, W1, W2, W3, mul_assoc] using hC7
  have hC7p' :
      data.t⁻¹ * S2 * data.t⁻¹ = (Ap * data.t ^ 2 * S1 * W3p)⁻¹ := by
    have hC7p0 := hC7p
    rw [forms.frobenius_w1, forms.frobenius_w2, forms.frobenius_w3] at hC7p0
    simpa [Ap, S1, S2, S3, W1p, W2p, W3p,
      Step4C5NormalForms.frobenius, mul_assoc] using hC7p0
  have hword : A * data.t ^ 2 * S1 * W3 = Ap * data.t ^ 2 * S1 * W3p := by
    have hinv : (A * data.t ^ 2 * S1 * W3)⁻¹ =
        (Ap * data.t ^ 2 * S1 * W3p)⁻¹ := hC7'.symm.trans hC7p'
    exact inv_inj.mp hinv
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have hp_eq : p = p - 1 + 1 :=
    (Nat.succ_pred_eq_of_pos hp_pos).symm
  have hW3_pow_mul_inv : W3 ^ p * W3⁻¹ = W3 ^ (p - 1) := by
    conv_lhs =>
      lhs
      rw [hp_eq]
    rw [pow_succ]
    group
  have hW3p_eq : W3p = W3 ^ p := by
    simp [W3p, W3, map_pow]
  have hW3pow_eq : W3pow = W3 ^ (p - 1) := by
    simp [W3pow, W3, map_pow]
  have hW3p_mul_inv : W3p * W3⁻¹ = W3pow := by
    calc
      W3p * W3⁻¹ = W3 ^ p * W3⁻¹ := by rw [hW3p_eq]
      _ = W3 ^ (p - 1) := hW3_pow_mul_inv
      _ = W3pow := hW3pow_eq.symm
  have hApA : Ap⁻¹ * A = data.t ^ 2 * X * (data.t ^ 2)⁻¹ := by
    calc
      Ap⁻¹ * A = Ap⁻¹ * (A * data.t ^ 2 * S1 * W3) * W3⁻¹ * S1⁻¹ *
          (data.t ^ 2)⁻¹ := by
        group
      _ = Ap⁻¹ * (Ap * data.t ^ 2 * S1 * W3p) * W3⁻¹ * S1⁻¹ *
          (data.t ^ 2)⁻¹ := by
        rw [hword]
      _ = data.t ^ 2 * S1 * (W3p * W3⁻¹) * S1⁻¹ *
          (data.t ^ 2)⁻¹ := by
        group
      _ = data.t ^ 2 * S1 * W3pow * S1⁻¹ * (data.t ^ 2)⁻¹ := by
        rw [hW3p_mul_inv]
      _ = data.t ^ 2 * X * (data.t ^ 2)⁻¹ := by
        simp [X]
        group
  have hleft : W2p⁻¹ * S3⁻¹ * W1p⁻¹ * W1 * S3 * W2 = Ap⁻¹ * A := by
    simp [A, Ap]
    group
  calc
    (data.t ^ 2)⁻¹ * (W2p⁻¹ * S3⁻¹ * W1p⁻¹ * W1 * S3 * W2) *
        data.t ^ 2 =
        (data.t ^ 2)⁻¹ * (Ap⁻¹ * A) * data.t ^ 2 := by
      rw [hleft]
    _ = X := by
      rw [hApA]
      group

end Step4

end FieldNormalizerData

end OddOrder.BG.AppC
