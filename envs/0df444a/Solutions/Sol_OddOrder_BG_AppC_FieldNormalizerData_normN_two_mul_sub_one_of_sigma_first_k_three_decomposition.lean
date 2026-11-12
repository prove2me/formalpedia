-- Prove2me | solution 1 for OddOrder.BG.AppC.FieldNormalizerData.normN_two_mul_sub_one_of_sigma_first_k_three_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:22:10.043306+00:00
-- url     : https://prove2.me/submissions/c090dab9-b049-4e10-a967-f04d40e4ec73

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/AppC_NormSetBasic.lean
--   OddOrder/BG/AppC_LemmaC3_Setup.lean
--   OddOrder/BG/AppC_LemmaC3_ConjugateLine.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_AppC_FrobeniusBasics
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_Setup
import Definitions.Def_OddOrder_Mathlib_Subgroup
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime
import Definitions.Def_OddOrder_BG_AppC_NormSetBasic
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_ConjugateLine
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

/-- **BG Appendix C, Lemma C.3, Step 4 final paragraph, concrete form**:
if the first `k = 3` equation of `(C.5)` has middle prime-line factor `s^{-1}`,
then reading the additive coordinate in `P ⋊ U` gives the generator relation
`N(2*w-1)=1` for the middle complement element `w`. -/
theorem normOneFrobenius_normN_two_mul_sub_one_of_first_k_three_decomposition
    [Fact p.Prime] (hq : q ≠ 0) (w u₁ v₁ : normOneUnits p q)
    (hdec :
      (SemidirectProduct.inl
          (Multiplicative.ofAdd (1 : GaloisField p q)) : normOneFrobeniusGroup p q) *
          SemidirectProduct.inr w *
        SemidirectProduct.inl
          (Multiplicative.ofAdd (-(2 : GaloisField p q))) =
      (SemidirectProduct.inr u₁ : normOneFrobeniusGroup p q) *
        SemidirectProduct.inl
          (Multiplicative.ofAdd (-(1 : GaloisField p q))) *
          SemidirectProduct.inr v₁) :
    normN p q
      ((2 : GaloisField p q) *
          (((w : normOneUnits p q) : (GaloisField p q)ˣ) : GaloisField p q) - 1) = 1 := by
  let F := GaloisField p q
  let H := normOneFrobeniusGroup p q
  let wF : F := (((w : normOneUnits p q) : (GaloisField p q)ˣ) : F)
  let u₁F : F := (((u₁ : normOneUnits p q) : (GaloisField p q)ˣ) : F)
  have hleft := congrArg (fun g : H => g.left.toAdd) hdec
  simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
    SemidirectProduct.left_inl, SemidirectProduct.right_inl,
    SemidirectProduct.left_inr, SemidirectProduct.right_inr, map_one, one_mul, mul_one,
    toAdd_mul, toAdd_ofAdd, normOneMulAction_apply] at hleft
  have hleft' : (1 : F) - 2 * wF = -u₁F := by
    simpa [F, wF, u₁F, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hleft
  have hu₁F : u₁F = (2 : F) * wF - 1 := by
    calc
      u₁F = -(-u₁F) := by ring
      _ = -((1 : F) - 2 * wF) := by rw [← hleft']
      _ = (2 : F) * wF - 1 := by ring
  rw [show ((2 : GaloisField p q) *
        (((w : normOneUnits p q) : (GaloisField p q)ˣ) : GaloisField p q) - 1) =
        (((u₁ : normOneUnits p q) : (GaloisField p q)ˣ) : GaloisField p q) by
      simpa [F, wF, u₁F] using hu₁F.symm]
  exact (mem_normOneUnits_iff_normN p q hq (u₁ : (GaloisField p q)ˣ)).mp u₁.property

end OddOrder.BG.AppC.NormSet

-- ===== OddOrder/BG/AppC_LemmaC3_Setup.lean =====
namespace OddOrder.BG.AppC

open scoped Pointwise

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

/-- The `s^{-2}` factor in BG C.3 Step 4 is the `-2` point of the concrete
prime-field line after transport by `σ`. -/
theorem s_zpow_neg_two_eq_primeLineElement_neg_two
    (data : FieldNormalizerData p q G) :
    data.s ^ (-2 : ℤ) =
      data.sigma (primeLineElement p q (-2 : ZMod p)) := by
  dsimp [s, primeLineElement, primeLineGenerator]
  let F := GaloisField p q
  let H := NormSet.normOneFrobeniusGroup p q
  have hpow_two :
      (SemidirectProduct.inl (Multiplicative.ofAdd (1 : F)) : H) ^ 2 =
        SemidirectProduct.inl (Multiplicative.ofAdd (2 : F)) := by
    rw [pow_two, ← map_mul (SemidirectProduct.inl :
      NormSet.additiveFieldGroup p q →* H)]
    congr
    apply Multiplicative.toAdd.injective
    change (1 : F) + 1 = 2
    ring
  have hneg_two :
      (algebraMap (ZMod p) F (-2 : ZMod p)) = -(2 : F) := by
    simp only [map_neg, map_ofNat]
  rw [← map_zpow]
  congr
  rw [zpow_neg, hneg_two]
  change ((SemidirectProduct.inl (Multiplicative.ofAdd (1 : F)) : H) ^ 2)⁻¹ =
    SemidirectProduct.inl (Multiplicative.ofAdd (-(2 : F)))
  have hpow_two_inv := congrArg Inv.inv hpow_two
  exact hpow_two_inv.trans (by simp [F])

end FieldNormalizerData

end OddOrder.BG.AppC

-- ===== OddOrder/BG/AppC_LemmaC3_ConjugateLine.lean =====
namespace OddOrder.BG.AppC

open scoped Pointwise

open scoped BigOperators

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

/-- BG Appendix C, Lemma C.3 Step 4 final paragraph, finite-field reading:
if a first `k = 3` normal form has middle prime-line factor `s^{-1}`,
then its additive coordinate gives `N(2*w-1)=1` for the middle complement
element `w`. -/
theorem _root_.solution
    (data : FieldNormalizerData p q G)
    (w u₁ v₁ : NormSet.normOneUnits p q)
    (hdec : data.s *
          data.sigma (SemidirectProduct.inr w : NormSet.normOneFrobeniusGroup p q) *
        data.s ^ (-2 : ℤ) =
      data.sigma (SemidirectProduct.inr u₁ : NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q (-1 : ZMod p)) *
          data.sigma (SemidirectProduct.inr v₁ : NormSet.normOneFrobeniusGroup p q)) :
    NormSet.normN p q
      ((2 : GaloisField p q) *
          (((w : NormSet.normOneUnits p q) :
              (GaloisField p q)ˣ) :
              GaloisField p q) - 1) = 1 := by
  let F := GaloisField p q
  let H := NormSet.normOneFrobeniusGroup p q
  have hline_neg_one :
      primeLineElement p q (-1 : ZMod p) =
        (SemidirectProduct.inl (Multiplicative.ofAdd (-(1 : F))) : H) := by
    simp [primeLineElement, F]
  have hline_neg_two :
      primeLineElement p q (-2 : ZMod p) =
        (SemidirectProduct.inl (Multiplicative.ofAdd (-(2 : F))) : H) := by
    simp [primeLineElement, F, map_neg, map_ofNat]
  have hσ :
      data.sigma
          ((SemidirectProduct.inl (Multiplicative.ofAdd (1 : F)) : H) *
              SemidirectProduct.inr w *
            SemidirectProduct.inl (Multiplicative.ofAdd (-(2 : F)))) =
        data.sigma
          ((SemidirectProduct.inr u₁ : H) *
            SemidirectProduct.inl (Multiplicative.ofAdd (-(1 : F))) *
              SemidirectProduct.inr v₁) := by
    calc
      data.sigma
          ((SemidirectProduct.inl (Multiplicative.ofAdd (1 : F)) : H) *
              SemidirectProduct.inr w *
            SemidirectProduct.inl (Multiplicative.ofAdd (-(2 : F)))) =
          data.s * data.sigma (SemidirectProduct.inr w : H) * data.s ^ (-2 : ℤ) := by
        have hs :
            data.s =
              data.sigma
                (SemidirectProduct.inl (Multiplicative.ofAdd (1 : F)) : H) := by
          simp [FieldNormalizerData.s, primeLineGenerator, F]
        have hsneg_two :
            data.s ^ (-2 : ℤ) =
              data.sigma
                (SemidirectProduct.inl (Multiplicative.ofAdd (-(2 : F))) : H) := by
          simpa [hline_neg_two] using data.s_zpow_neg_two_eq_primeLineElement_neg_two
        rw [map_mul, map_mul, hsneg_two, hs]
      _ = data.sigma (SemidirectProduct.inr u₁ : H) *
            data.sigma (primeLineElement p q (-1 : ZMod p)) *
              data.sigma (SemidirectProduct.inr v₁ : H) := by
        exact hdec
      _ = data.sigma
          ((SemidirectProduct.inr u₁ : H) *
            SemidirectProduct.inl (Multiplicative.ofAdd (-(1 : F))) *
              SemidirectProduct.inr v₁) := by
        simp [map_mul, hline_neg_one]
  have hH := data.sigma_injective hσ
  simpa [F] using
    NormSet.normOneFrobenius_normN_two_mul_sub_one_of_first_k_three_decomposition
      (p := p) (q := q) data.q_prime.ne_zero w u₁ v₁ hH

end FieldNormalizerData

end OddOrder.BG.AppC
