-- Prove2me | solution 1 for OddOrder.BG.AppC.FieldNormalizerData.relationC7
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:27:30.642675+00:00
-- url     : https://prove2.me/submissions/175f4248-362f-4667-9247-44b710d9377b

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/AppC_NormSetBasic.lean
--   OddOrder/BG/AppC_LemmaC3_Setup.lean
--   OddOrder/BG/AppC_LemmaC3_ConjugateLine.lean
--   OddOrder/BG/AppC_LemmaC3_ScalarCalculus.lean
--   OddOrder/BG/AppC_LemmaC3_NormalForms.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_AppC_FrobeniusBasics
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_Setup
import Definitions.Def_OddOrder_Mathlib_Subgroup
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_ConjugateLine
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_ScalarCalculus
import Definitions.Def_OddOrder_BG_AppC_NormSetBasic
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_NormalForms
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

-- ===== OddOrder/BG/AppC_NormSetBasic.lean =====
namespace OddOrder.BG.AppC.NormSet

open scoped Pointwise

open Polynomial Finset

variable (p q : ℕ)

/-- In the concrete Frobenius group `H = P ⋊ U`, conjugating an additive-kernel
point `s` by `u ∈ U` is multiplication by `u` on the finite field.  This is the
formal `u s u⁻¹ = u*s` bridge used to turn BG's class sums into the finite-field
pair condition. -/
theorem normOneFrobenius_conj_inl [Fact p.Prime] (u : normOneUnits p q)
    (s : GaloisField p q) :
    (SemidirectProduct.inr u : normOneFrobeniusGroup p q) *
        SemidirectProduct.inl (Multiplicative.ofAdd s) * SemidirectProduct.inr u⁻¹ =
      SemidirectProduct.inl
        (Multiplicative.ofAdd (((u : (GaloisField p q)ˣ) : GaloisField p q) * s)) := by
  rw [← SemidirectProduct.inl_aut, SemidirectProduct.inl_inj]
  exact Multiplicative.toAdd.injective (normOneMulAction_apply p q u s)

end OddOrder.BG.AppC.NormSet

-- ===== OddOrder/BG/AppC_LemmaC3_Setup.lean =====
namespace OddOrder.BG.AppC

open scoped Pointwise

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

/-- The transported prime-line generator normalizes `Q`. -/
theorem s_normalizes_Q (data : FieldNormalizerData p q G) :
    data.s ∈ Subgroup.normalizer (data.Q : Set G) :=
  data.W2_normalizes_Q data.s_mem_W2

end FieldNormalizerData

end OddOrder.BG.AppC

-- ===== OddOrder/BG/AppC_LemmaC3_ConjugateLine.lean =====
namespace OddOrder.BG.AppC

open scoped Pointwise

open scoped BigOperators

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

/-- The conjugate generator `t` also normalizes `Q`. -/
theorem t_normalizes_Q (data : FieldNormalizerData p q G) :
    data.t ∈ Subgroup.normalizer (data.Q : Set G) := by
  have hyN : data.y ∈ Subgroup.normalizer (data.Q : Set G) :=
    Subgroup.le_normalizer data.y_mem_Q
  dsimp [t]
  exact mul_mem (mul_mem hyN data.s_normalizes_Q) (inv_mem hyN)

/-- The first BG commutator factor `s⁻¹t` lies in `Q`. -/
theorem s_inv_mul_t_mem_Q (data : FieldNormalizerData p q G) :
    data.s⁻¹ * data.t ∈ data.Q := by
  have hsN_inv : data.s⁻¹ ∈ Subgroup.normalizer (data.Q : Set G) :=
    inv_mem data.s_normalizes_Q
  have hconj_y : data.s⁻¹ * data.y * data.s ∈ data.Q := by
    simpa using (Subgroup.mem_normalizer_iff.mp hsN_inv data.y).mp data.y_mem_Q
  have hy_inv : data.y⁻¹ ∈ data.Q := inv_mem data.y_mem_Q
  dsimp [t]
  simpa [mul_assoc] using mul_mem hconj_y hy_inv

private theorem inv_pow_mul_pow_mem_of_inv_mul_mem {H : Subgroup G} {a b : G}
    (haN : a ∈ Subgroup.normalizer (H : Set G)) (hrel : a⁻¹ * b ∈ H) :
    ∀ n : ℕ, (a⁻¹) ^ n * b ^ n ∈ H := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have haN_inv : a⁻¹ ∈ Subgroup.normalizer (H : Set G) := inv_mem haN
      have hconj : a⁻¹ * ((a⁻¹) ^ n * b ^ n) * a ∈ H := by
        simpa using (Subgroup.mem_normalizer_iff.mp haN_inv ((a⁻¹) ^ n * b ^ n)).mp ih
      have hprod : (a⁻¹ * ((a⁻¹) ^ n * b ^ n) * a) * (a⁻¹ * b) ∈ H :=
        mul_mem hconj hrel
      convert hprod using 1
      group

/-- The BG commutator factors `(s⁻¹)^n t^n` lie in `Q`. -/
theorem s_inv_pow_mul_t_pow_mem_Q (data : FieldNormalizerData p q G) (n : ℕ) :
    (data.s⁻¹) ^ n * data.t ^ n ∈ data.Q :=
  inv_pow_mul_pow_mem_of_inv_mul_mem data.s_normalizes_Q data.s_inv_mul_t_mem_Q n

/-- Elements of the transported `Q` commute.  This is the S16-facing form of
BG Appendix C Remark (B)/(X) used in Lemma C.3 Step 4 when rewriting (C.3) to
(C.4). -/
theorem Q_mul_comm (data : FieldNormalizerData p q G)
    {x y : G} (hx : x ∈ data.Q) (hy : y ∈ data.Q) :
    x * y = y * x := by
  have := data.Q_commutative
  exact setLike_mul_comm (s := data.Q) hx hy

/-- The opposite first commutator factor `t⁻¹s` lies in `Q`. -/
theorem t_inv_mul_s_mem_Q (data : FieldNormalizerData p q G) :
    data.t⁻¹ * data.s ∈ data.Q := by
  simpa using inv_mem data.s_inv_mul_t_mem_Q

/-- The opposite BG commutator factors `(t⁻¹)^n s^n` lie in `Q`. -/
theorem t_inv_pow_mul_s_pow_mem_Q (data : FieldNormalizerData p q G) (n : ℕ) :
    (data.t⁻¹) ^ n * data.s ^ n ∈ data.Q :=
  inv_pow_mul_pow_mem_of_inv_mul_mem data.t_normalizes_Q data.t_inv_mul_s_mem_Q n

end FieldNormalizerData

end OddOrder.BG.AppC

-- ===== OddOrder/BG/AppC_LemmaC3_ScalarCalculus.lean =====
namespace OddOrder.BG.AppC

open OddOrder.GroupTheory

open scoped Pointwise

open scoped BigOperators

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

section Step4

/-- The prime-field-line scalars are additive in the exponent: `s^x · s^y = s^{x+y}`. -/
theorem sScalar_mul (data : FieldNormalizerData p q G)
    (x y : GaloisField p q) :
    data.sScalar x * data.sScalar y = data.sScalar (x + y) := by
  rw [sScalar, sScalar, sScalar, ← map_mul data.sigma,
    ← map_mul (SemidirectProduct.inl :
      NormSet.additiveFieldGroup p q →*
        NormSet.normOneFrobeniusGroup p q),
    ← ofAdd_add]

/-- The distinguished generator is the scalar `s = s^1`. -/
theorem s_eq_sScalar_one (data : FieldNormalizerData p q G) :
    data.s = data.sScalar 1 := by
  rw [sScalar, FieldNormalizerData.s, primeLineGenerator]

/-- Conjugating the prime-line scalar `s^x` by `σ(inr a)` scales the exponent by
`↑a⁻¹`: `σ(inr a)⁻¹ · s^x · σ(inr a) = s^{(↑a⁻¹)·x}`.  This is BG's `s^a` notation. -/
theorem sScalar_conj (data : FieldNormalizerData p q G)
    (a : NormSet.normOneUnits p q) (x : GaloisField p q) :
    (data.sigma (SemidirectProduct.inr a))⁻¹ * data.sScalar x *
        data.sigma (SemidirectProduct.inr a) =
      data.sScalar (unitVal a⁻¹ * x) := by
  rw [sScalar, sScalar, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  rw [← map_inv]
  have h := NormSet.normOneFrobenius_conj_inl
    (p := p) (q := q) a⁻¹ x
  rw [inv_inv] at h
  exact h

/-- `s² = s^2` as a prime-line scalar. -/
theorem s_sq_eq_sScalar_two (data : FieldNormalizerData p q G) :
    data.s ^ 2 = data.sScalar 2 := by
  rw [s_eq_sScalar_one, pow_two, sScalar_mul]
  congr 1
  norm_num

/-- **BG Appendix C, Lemma C.3 Step 4 base relation** (mmd L4994): for norm-one
units `a, b` with `↑a⁻¹ + ↑b⁻¹ = 2`, BG's identity `s^a · s^b = s²`, where the BG
conjugate `s^a = σ(inr a)⁻¹ · s · σ(inr a) = s^{↑a⁻¹}`. -/
theorem sBGConj_mul_sBGConj (data : FieldNormalizerData p q G)
    (a b : NormSet.normOneUnits p q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2) :
    ((data.sigma (SemidirectProduct.inr a))⁻¹ * data.s *
          data.sigma (SemidirectProduct.inr a)) *
        ((data.sigma (SemidirectProduct.inr b))⁻¹ * data.s *
          data.sigma (SemidirectProduct.inr b)) =
      data.s ^ 2 := by
  have ha : (data.sigma (SemidirectProduct.inr a))⁻¹ * data.s *
      data.sigma (SemidirectProduct.inr a) = data.sScalar (unitVal a⁻¹) := by
    rw [s_eq_sScalar_one, sScalar_conj, mul_one]
  have hb : (data.sigma (SemidirectProduct.inr b))⁻¹ * data.s *
      data.sigma (SemidirectProduct.inr b) = data.sScalar (unitVal b⁻¹) := by
    rw [s_eq_sScalar_one, sScalar_conj, mul_one]
  rw [ha, hb, sScalar_mul, hab, s_sq_eq_sScalar_two]

/-- **BG Appendix C, Lemma C.3 Step 4 relation (C.2)** (mmd L4994): for norm-one
units `a, b` with `↑a⁻¹ + ↑b⁻¹ = 2`,
`s⁻² · (σ(inr a)⁻¹ s σ(inr a)) · (σ(inr b)⁻¹ s σ(inr b)) = 1`. -/
theorem relationC2 (data : FieldNormalizerData p q G)
    (a b : NormSet.normOneUnits p q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2) :
    data.s ^ (-2 : ℤ) *
        (((data.sigma (SemidirectProduct.inr a))⁻¹ * data.s *
            data.sigma (SemidirectProduct.inr a)) *
          ((data.sigma (SemidirectProduct.inr b))⁻¹ * data.s *
            data.sigma (SemidirectProduct.inr b))) = 1 := by
  rw [data.sBGConj_mul_sBGConj a b hab, zpow_neg, zpow_two, ← pow_two,
    inv_mul_cancel]

end Step4

end FieldNormalizerData

end OddOrder.BG.AppC

-- ===== OddOrder/BG/AppC_LemmaC3_NormalForms.lean =====
namespace OddOrder.BG.AppC

open OddOrder.GroupTheory

open scoped Pointwise

open scoped BigOperators

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

section Step4

/-- BG (C.4) connector 1: `s⁻³ t² s = t⁻¹ s⁻² t³`, by commuting `(s⁻¹)³t³` and
`t⁻¹s` inside the abelian `Q`. -/
theorem connectorC4_one (data : FieldNormalizerData p q G) :
    (data.s⁻¹) ^ 3 * data.t ^ 2 * data.s =
      data.t⁻¹ * (data.s⁻¹) ^ 2 * data.t ^ 3 :=
  calc
    (data.s⁻¹) ^ 3 * data.t ^ 2 * data.s
        = ((data.s⁻¹) ^ 3 * data.t ^ 3) * (data.t⁻¹ * data.s) := by group
    _ = (data.t⁻¹ * data.s) * ((data.s⁻¹) ^ 3 * data.t ^ 3) :=
          data.Q_mul_comm (data.s_inv_pow_mul_t_pow_mem_Q 3) data.t_inv_mul_s_mem_Q
    _ = data.t⁻¹ * (data.s⁻¹) ^ 2 * data.t ^ 3 := by group

/-- BG (C.4) connector 2: `s⁻² t⁻¹ s³ = t⁻³ s t²`, by commuting `(s⁻¹)²t²` and
`(t⁻¹)³s³` inside the abelian `Q`. -/
theorem connectorC4_two (data : FieldNormalizerData p q G) :
    (data.s⁻¹) ^ 2 * data.t⁻¹ * data.s ^ 3 =
      (data.t⁻¹) ^ 3 * data.s * data.t ^ 2 :=
  calc
    (data.s⁻¹) ^ 2 * data.t⁻¹ * data.s ^ 3
        = ((data.s⁻¹) ^ 2 * data.t ^ 2) * ((data.t⁻¹) ^ 3 * data.s ^ 3) := by group
    _ = ((data.t⁻¹) ^ 3 * data.s ^ 3) * ((data.s⁻¹) ^ 2 * data.t ^ 2) :=
          data.Q_mul_comm (data.s_inv_pow_mul_t_pow_mem_Q 2)
            (data.t_inv_pow_mul_s_pow_mem_Q 3)
    _ = (data.t⁻¹) ^ 3 * data.s * data.t ^ 2 := by group

/-- BG (C.4) connector 3: `s⁻¹ t⁻¹ s² = t⁻² s t`, by commuting `s⁻¹t` and
`(t⁻¹)²s²` inside the abelian `Q`. -/
theorem connectorC4_three (data : FieldNormalizerData p q G) :
    data.s⁻¹ * data.t⁻¹ * data.s ^ 2 =
      (data.t⁻¹) ^ 2 * data.s * data.t :=
  calc
    data.s⁻¹ * data.t⁻¹ * data.s ^ 2
        = (data.s⁻¹ * data.t) * ((data.t⁻¹) ^ 2 * data.s ^ 2) := by group
    _ = ((data.t⁻¹) ^ 2 * data.s ^ 2) * (data.s⁻¹ * data.t) :=
          data.Q_mul_comm data.s_inv_mul_t_mem_Q (data.t_inv_pow_mul_s_pow_mem_Q 2)
    _ = (data.t⁻¹) ^ 2 * data.s * data.t := by group

/-- **BG Appendix C, Lemma C.3 relation (C.4)** (mmd L4994, PDF p.150): the
backward conjugated `k = 3` relation
`s⁻³ t² M₁ t⁻¹ M₂ t⁻¹ M₃ s³ = 1`, where
`M₁ = s · (t⁻³ σ(inr a)⁻¹ t³) · s⁻²`, `M₂ = s³ · (t⁻² σ(inr (a b⁻¹)) t²) · s⁻¹`,
`M₃ = s² · (t⁻¹ σ(inr b) t) · s⁻³` are BG's `s^{k-2}(a⁻¹)^{t^k}s^{-k+1}` etc.  The
connector words between the conjugated factors `q`-swap (Connectors 1–3) and the
`t`-powers then telescope to `t⁻¹ · (C.2) · t = 1`. -/
theorem relationC4 (data : FieldNormalizerData p q G)
    (a b : NormSet.normOneUnits p q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2) :
    (data.s⁻¹) ^ 3 * data.t ^ 2 *
        (data.s *
            ((data.t⁻¹) ^ 3 * (data.sigma (SemidirectProduct.inr a))⁻¹ * data.t ^ 3) *
          (data.s⁻¹) ^ 2) *
      data.t⁻¹ *
        (data.s ^ 3 *
            ((data.t⁻¹) ^ 2 *
              (data.sigma (SemidirectProduct.inr a) *
                (data.sigma (SemidirectProduct.inr b))⁻¹) * data.t ^ 2) *
          data.s⁻¹) *
      data.t⁻¹ *
        (data.s ^ 2 *
            (data.t⁻¹ * data.sigma (SemidirectProduct.inr b) * data.t) *
          (data.s⁻¹) ^ 3) *
      data.s ^ 3 = 1 := by
  have hC2 := data.relationC2 a b hab
  calc
    (data.s⁻¹) ^ 3 * data.t ^ 2 *
          (data.s *
              ((data.t⁻¹) ^ 3 * (data.sigma (SemidirectProduct.inr a))⁻¹ * data.t ^ 3) *
            (data.s⁻¹) ^ 2) *
        data.t⁻¹ *
          (data.s ^ 3 *
              ((data.t⁻¹) ^ 2 *
                (data.sigma (SemidirectProduct.inr a) *
                  (data.sigma (SemidirectProduct.inr b))⁻¹) * data.t ^ 2) *
            data.s⁻¹) *
        data.t⁻¹ *
          (data.s ^ 2 *
              (data.t⁻¹ * data.sigma (SemidirectProduct.inr b) * data.t) *
            (data.s⁻¹) ^ 3) *
        data.s ^ 3
        = ((data.s⁻¹) ^ 3 * data.t ^ 2 * data.s) *
              ((data.t⁻¹) ^ 3 * (data.sigma (SemidirectProduct.inr a))⁻¹ * data.t ^ 3) *
              ((data.s⁻¹) ^ 2 * data.t⁻¹ * data.s ^ 3) *
              ((data.t⁻¹) ^ 2 *
                (data.sigma (SemidirectProduct.inr a) *
                  (data.sigma (SemidirectProduct.inr b))⁻¹) * data.t ^ 2) *
              (data.s⁻¹ * data.t⁻¹ * data.s ^ 2) *
              (data.t⁻¹ * data.sigma (SemidirectProduct.inr b) * data.t) := by
        group
    _ = (data.t⁻¹ * (data.s⁻¹) ^ 2 * data.t ^ 3) *
              ((data.t⁻¹) ^ 3 * (data.sigma (SemidirectProduct.inr a))⁻¹ * data.t ^ 3) *
              ((data.t⁻¹) ^ 3 * data.s * data.t ^ 2) *
              ((data.t⁻¹) ^ 2 *
                (data.sigma (SemidirectProduct.inr a) *
                  (data.sigma (SemidirectProduct.inr b))⁻¹) * data.t ^ 2) *
              ((data.t⁻¹) ^ 2 * data.s * data.t) *
              (data.t⁻¹ * data.sigma (SemidirectProduct.inr b) * data.t) := by
        rw [data.connectorC4_one, data.connectorC4_two, data.connectorC4_three]
    _ = data.t⁻¹ *
          (data.s ^ (-2 : ℤ) *
            (((data.sigma (SemidirectProduct.inr a))⁻¹ * data.s *
                data.sigma (SemidirectProduct.inr a)) *
              ((data.sigma (SemidirectProduct.inr b))⁻¹ * data.s *
                data.sigma (SemidirectProduct.inr b)))) *
          data.t := by
        group
    _ = data.t⁻¹ * 1 * data.t := by rw [hC2]
    _ = 1 := by group

/-- Relation `(C.4)` restated using the named BG `(C.5)` factors. -/
theorem relationC4_step4M (data : FieldNormalizerData p q G)
    (a b : NormSet.normOneUnits p q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2) :
    (data.s⁻¹) ^ 3 * data.t ^ 2 * data.step4M1 a *
      data.t⁻¹ * data.step4M2 a b * data.t⁻¹ * data.step4M3 b *
        data.s ^ 3 = 1 := by
  simpa [step4M1, step4M2, step4M3] using data.relationC4 a b hab

/-- Relation `(C.4)` after substituting the three `(C.5)` normal forms. -/
theorem relationC4_step4C5NormalForms
    (data : FieldNormalizerData p q G)
    {a b : NormSet.normOneUnits p q}
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b) :
    (data.s⁻¹) ^ 3 * data.t ^ 2 * forms.factor1 *
      data.t⁻¹ * forms.factor2 * data.t⁻¹ * forms.factor3 * data.s ^ 3 = 1 := by
  have h := data.relationC4_step4M a b hab
  rw [forms.hM1, forms.hM2, forms.hM3] at h
  simpa [Step4C5NormalForms.factor1, Step4C5NormalForms.factor2,
    Step4C5NormalForms.factor3] using h

/-- The first rearranged relation on the way to BG `(C.7)`: multiply `(C.4)` by
`s^3` on the left and `s^{-3}` on the right after substituting `(C.5)`. -/
theorem relationC7_seed
    (data : FieldNormalizerData p q G)
    {a b : NormSet.normOneUnits p q}
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b) :
    data.t ^ 2 * forms.factor1 * data.t⁻¹ * forms.factor2 * data.t⁻¹ * forms.factor3 =
      1 := by
  have h := data.relationC4_step4C5NormalForms hab forms
  calc
    data.t ^ 2 * forms.factor1 * data.t⁻¹ * forms.factor2 * data.t⁻¹ * forms.factor3 =
        data.s ^ 3 *
          ((data.s⁻¹) ^ 3 * data.t ^ 2 * forms.factor1 * data.t⁻¹ * forms.factor2 *
            data.t⁻¹ * forms.factor3 * data.s ^ 3) * (data.s ^ 3)⁻¹ := by
      group
    _ = data.s ^ 3 * 1 * (data.s ^ 3)⁻¹ := by rw [h]
    _ = 1 := by group

namespace Step4C5NormalForms

/-- The ambient reading of `w₁`: `σ(w₁) = t σ(v₂) t⁻¹ σ(u₃)`. -/
theorem sigma_inr_w1 {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) :
    data.sigma (SemidirectProduct.inr forms.w1 : NormSet.normOneFrobeniusGroup p q) =
      data.t * data.sigma (SemidirectProduct.inr forms.v2 : NormSet.normOneFrobeniusGroup p q) *
        data.t⁻¹ *
          data.sigma (SemidirectProduct.inr forms.u3 : NormSet.normOneFrobeniusGroup p q) := by
  unfold Step4C5NormalForms.w1
  simp only [map_mul]
  have hφ :
      data.sigma
          (SemidirectProduct.inr (data.tConjNormOneUnitsAut forms.v2) :
            NormSet.normOneFrobeniusGroup p q) =
        data.t * data.sigma (SemidirectProduct.inr forms.v2 : NormSet.normOneFrobeniusGroup p q) *
          data.t⁻¹ := by
    simpa using
      (data.t_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow 1 forms.v2).symm
  rw [hφ]

/-- The ambient reading of `w₂`: `σ(w₂) = σ(v₃) t² σ(u₁) t⁻²`. -/
theorem sigma_inr_w2 {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) :
    data.sigma (SemidirectProduct.inr forms.w2 : NormSet.normOneFrobeniusGroup p q) =
      data.sigma (SemidirectProduct.inr forms.v3 : NormSet.normOneFrobeniusGroup p q) *
        data.t ^ 2 *
          data.sigma (SemidirectProduct.inr forms.u1 : NormSet.normOneFrobeniusGroup p q) *
            (data.t ^ 2)⁻¹ := by
  unfold Step4C5NormalForms.w2
  simp only [map_mul]
  rw [← data.t_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow 2 forms.u1]
  group

/-- The ambient reading of `w₃`: `σ(w₃) = σ(v₁) t⁻¹ σ(u₂) t`. -/
theorem sigma_inr_w3 {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) :
    data.sigma (SemidirectProduct.inr forms.w3 : NormSet.normOneFrobeniusGroup p q) =
      data.sigma (SemidirectProduct.inr forms.v1 : NormSet.normOneFrobeniusGroup p q) *
        data.t⁻¹ * data.sigma (SemidirectProduct.inr forms.u2 : NormSet.normOneFrobeniusGroup p q) *
          data.t := by
  unfold Step4C5NormalForms.w3
  simp only [map_mul]
  rw [← data.t_inv_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow_inv 1 forms.u2]
  group

end Step4C5NormalForms

/-- BG Appendix C `(C.7)`, obtained by rearranging the `(C.5)` substitution relation and
absorbing the conjugated complement terms into `w₁`, `w₂`, and `w₃`. -/
theorem _root_.solution
    (data : FieldNormalizerData p q G)
    {a b : NormSet.normOneUnits p q}
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b) :
    data.t⁻¹ * data.sigma (primeLineElement p q forms.c2) * data.t⁻¹ =
      (data.sigma (SemidirectProduct.inr forms.w1 : NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q forms.c3) *
          data.sigma (SemidirectProduct.inr forms.w2 : NormSet.normOneFrobeniusGroup p q) *
            data.t ^ 2 * data.sigma (primeLineElement p q forms.c1) *
              data.sigma
                (SemidirectProduct.inr forms.w3 : NormSet.normOneFrobeniusGroup p q))⁻¹ := by
  let U1 := data.sigma (SemidirectProduct.inr forms.u1 : NormSet.normOneFrobeniusGroup p q)
  let V1 := data.sigma (SemidirectProduct.inr forms.v1 : NormSet.normOneFrobeniusGroup p q)
  let U2 := data.sigma (SemidirectProduct.inr forms.u2 : NormSet.normOneFrobeniusGroup p q)
  let V2 := data.sigma (SemidirectProduct.inr forms.v2 : NormSet.normOneFrobeniusGroup p q)
  let U3 := data.sigma (SemidirectProduct.inr forms.u3 : NormSet.normOneFrobeniusGroup p q)
  let V3 := data.sigma (SemidirectProduct.inr forms.v3 : NormSet.normOneFrobeniusGroup p q)
  let S1 := data.sigma (primeLineElement p q forms.c1)
  let S2 := data.sigma (primeLineElement p q forms.c2)
  let S3 := data.sigma (primeLineElement p q forms.c3)
  let W1 := data.sigma (SemidirectProduct.inr forms.w1 : NormSet.normOneFrobeniusGroup p q)
  let W2 := data.sigma (SemidirectProduct.inr forms.w2 : NormSet.normOneFrobeniusGroup p q)
  let W3 := data.sigma (SemidirectProduct.inr forms.w3 : NormSet.normOneFrobeniusGroup p q)
  have hseed :
      data.t ^ 2 * U1 * S1 * V1 * data.t⁻¹ * U2 * S2 * V2 * data.t⁻¹ * U3 * S3 * V3 =
        1 := by
    have h := data.relationC7_seed hab forms
    simpa [Step4C5NormalForms.factor1, Step4C5NormalForms.factor2,
      Step4C5NormalForms.factor3, U1, V1, U2, V2, U3, V3, S1, S2, S3, mul_assoc]
      using h
  have hw1_t : data.t⁻¹ * W1 = V2 * data.t⁻¹ * U3 := by
    dsimp [W1, V2, U3]
    rw [forms.sigma_inr_w1]
    group
  have hw2_t : W2 * data.t ^ 2 = V3 * data.t ^ 2 * U1 := by
    dsimp [W2, V3, U1]
    rw [forms.sigma_inr_w2]
    group
  have hw3_t : W3 * data.t⁻¹ = V1 * data.t⁻¹ * U2 := by
    dsimp [W3, V1, U2]
    rw [forms.sigma_inr_w3]
    group
  have hword :
      data.t ^ 2 * U1 * S1 * W3 * (data.t⁻¹ * S2 * data.t⁻¹) * W1 * S3 * V3 =
        1 := by
    calc
      data.t ^ 2 * U1 * S1 * W3 * (data.t⁻¹ * S2 * data.t⁻¹) * W1 * S3 * V3 =
          data.t ^ 2 * U1 * S1 * (W3 * data.t⁻¹) * S2 *
            (data.t⁻¹ * W1) * S3 * V3 := by
        group
      _ = data.t ^ 2 * U1 * S1 * (V1 * data.t⁻¹ * U2) * S2 *
            (V2 * data.t⁻¹ * U3) * S3 * V3 := by
        rw [hw3_t, hw1_t]
      _ = data.t ^ 2 * U1 * S1 * V1 * data.t⁻¹ * U2 * S2 * V2 * data.t⁻¹ * U3 * S3 * V3 := by
        group
      _ = 1 := hseed
  have hwordPrime :
      (data.t ^ 2 * U1 * S1 * W3) * (data.t⁻¹ * S2 * data.t⁻¹) *
          (W1 * S3 * V3) = 1 := by
    simpa [mul_assoc] using hword
  have hmain : data.t⁻¹ * S2 * data.t⁻¹ =
      (W1 * S3 * W2 * data.t ^ 2 * S1 * W3)⁻¹ := by
    calc
      data.t⁻¹ * S2 * data.t⁻¹ =
          (data.t ^ 2 * U1 * S1 * W3)⁻¹ *
            ((data.t ^ 2 * U1 * S1 * W3) * (data.t⁻¹ * S2 * data.t⁻¹) *
              (W1 * S3 * V3)) * (W1 * S3 * V3)⁻¹ := by
        group
      _ = (data.t ^ 2 * U1 * S1 * W3)⁻¹ * 1 * (W1 * S3 * V3)⁻¹ := by
        rw [hwordPrime]
      _ = ((W1 * S3 * V3) * (data.t ^ 2 * U1 * S1 * W3))⁻¹ := by
        group
      _ = (W1 * S3 * W2 * data.t ^ 2 * S1 * W3)⁻¹ := by
        have hD : W1 * S3 * W2 * data.t ^ 2 * S1 * W3 =
            (W1 * S3 * V3) * (data.t ^ 2 * U1 * S1 * W3) := by
          calc
            W1 * S3 * W2 * data.t ^ 2 * S1 * W3 =
                W1 * S3 * (W2 * data.t ^ 2) * S1 * W3 := by
              group
            _ = W1 * S3 * (V3 * data.t ^ 2 * U1) * S1 * W3 := by
              rw [hw2_t]
            _ = (W1 * S3 * V3) * (data.t ^ 2 * U1 * S1 * W3) := by
              group
        rw [← hD]
  simpa [S1, S2, S3, W1, W2, W3, mul_assoc] using hmain

end Step4

end FieldNormalizerData

end OddOrder.BG.AppC
