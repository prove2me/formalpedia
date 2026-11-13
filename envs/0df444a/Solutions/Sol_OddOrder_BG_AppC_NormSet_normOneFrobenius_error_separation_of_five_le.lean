-- Prove2me | solution 1 for OddOrder.BG.AppC.NormSet.normOneFrobenius_error_separation_of_five_le
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T07:39:34.607123+00:00
-- url     : https://prove2.me/submissions/5f77ca01-097e-4908-9380-76ccb8051e8b

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/AppC_NormSetBasic.lean
--   OddOrder/BG/AppC_NormOneInduce.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_AppC_NormSet
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ClassSumAlgebra
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InflationCharacter
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_LinearCharacter
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusGroup
import Definitions.Def_OddOrder_Mathlib_SemidirectProduct
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceTheorems
import Definitions.Def_OddOrder_BG_AppC_NormSetBasic
import Definitions.Def_OddOrder_BG_AppC_NormOneInduce
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
import Mathlib.Data.Set.Card.Arithmetic

-- ===== OddOrder/BG/AppC_NormSetBasic.lean =====
namespace OddOrder.BG.AppC.NormSet

open scoped Pointwise

open Polynomial Finset

variable (p q : ℕ)

/-- **BG Appendix C, Remark (VII)**: `|U| = (p^q - 1)/(p - 1)` for the
norm-one subgroup `U ≤ 𝔽_{p^q}ˣ`.  This is the `|U|` used in the `q ≥ 5`
character-sum branch of Lemma C.2. -/
theorem normOneUnits_card [Fact p.Prime] (hq : q ≠ 0) :
    Nat.card (normOneUnits p q) = (p ^ q - 1) / (p - 1) := by
  classical
  let f : (GaloisField p q)ˣ →* (ZMod p)ˣ :=
    Units.map (Algebra.norm (ZMod p) (S := GaloisField p q))
  have hf_surj : Function.Surjective f :=
    FiniteField.unitsMap_norm_surjective (ZMod p) (GaloisField p q)
  have hker : normOneUnits p q = f.ker := rfl
  have hcod : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  have hdom : Nat.card (GaloisField p q)ˣ = p ^ q - 1 := by
    rw [Nat.card_units, GaloisField.card p q hq]
  have hindex : f.ker.index = p - 1 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf_surj, Subgroup.card_top, hcod]
  have hmul : Nat.card (normOneUnits p q) * (p - 1) = p ^ q - 1 := by
    rw [hker, ← hindex, f.ker.card_mul_index, hdom]
  exact Nat.eq_div_of_mul_eq_right (ne_of_gt (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt))
    (by simpa [mul_comm] using hmul)

/-- If `1 < q`, then the norm-one subgroup has more than one element. -/
theorem normOneUnits_card_gt_one [Fact p.Prime] (hq : 1 < q) :
    1 < Nat.card (normOneUnits p q) := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hq0 : q ≠ 0 := by omega
  rw [normOneUnits_card p q hq0, ← Nat.geomSum_eq hp2 q]
  have hrange : Finset.range 2 ⊆ Finset.range q := by
    intro k hk
    exact Finset.mem_range.mpr (by
      have hk2 : k < 2 := Finset.mem_range.mp hk
      omega)
  have hle :
      (∑ k ∈ Finset.range 2, p ^ k) ≤ ∑ k ∈ Finset.range q, p ^ k :=
    Finset.sum_le_sum_of_subset_of_nonneg hrange
      (fun _ _ _ => Nat.zero_le _)
  have htwo : 1 < (∑ k ∈ Finset.range 2, p ^ k) := by
    simp
    omega
  exact htwo.trans_le hle

end OddOrder.BG.AppC.NormSet

-- ===== OddOrder/BG/AppC_NormOneInduce.lean =====
namespace OddOrder.BG.AppC.NormSet

open OddOrder.RepresentationTheory

open scoped commutatorElement

variable (p q : ℕ)

/-- The two largest terms in the geometric sum for `|U|` give a sharper lower
bound used in the `q >= 5` numerical separation. -/
theorem pow_sub_one_add_pow_sub_two_le_normOneUnits_card [Fact p.Prime] (hq : 2 ≤ q) :
    p ^ (q - 1) + p ^ (q - 2) ≤ Nat.card (normOneUnits p q) := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hq0 : q ≠ 0 := by omega
  rw [normOneUnits_card p q hq0, ← Nat.geomSum_eq hp2 q]
  have hsubset : ({q - 2, q - 1} : Finset ℕ) ⊆ Finset.range q := by
    intro k hk
    have hk' : k = q - 2 ∨ k = q - 1 := by
      simpa using hk
    rcases hk' with rfl | rfl <;> exact Finset.mem_range.mpr (by omega)
  have hle :
      (∑ k ∈ ({q - 2, q - 1} : Finset ℕ), p ^ k) ≤ ∑ k ∈ Finset.range q, p ^ k :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun _ _ _ => Nat.zero_le _)
  have hsum :
      (∑ k ∈ ({q - 2, q - 1} : Finset ℕ), p ^ k) =
        p ^ (q - 2) + p ^ (q - 1) := by
    have hne : q - 2 ≠ q - 1 := by omega
    simp [hne, add_comm]
  rw [hsum] at hle
  simpa [add_comm] using hle

/-- For `q >= 5`, the last two terms of `|U| = 1 + p + ... + p^(q-1)`
make `|U|^2` dominate the numerical bound needed for Appendix C Lemma C.2. -/
theorem normOneUnits_card_sq_ge_pow_mul_one_add_pow_sub_two [Fact p.Prime] (hq : 5 ≤ q) :
    p ^ q * (1 + p ^ (q - 2)) ≤ Nat.card (normOneUnits p q) ^ 2 := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hU := pow_sub_one_add_pow_sub_two_le_normOneUnits_card p q (by omega)
  have hsqU :
      (p ^ (q - 1) + p ^ (q - 2)) ^ 2 ≤ Nat.card (normOneUnits p q) ^ 2 :=
    Nat.pow_le_pow_left hU 2
  have hb_ge_p2 : p ^ 2 ≤ p ^ (q - 2) :=
    Nat.pow_le_pow_right hp1 (by omega)
  have haux : p ^ 2 ≤ p ^ (q - 2) * (2 * p + 1) :=
    hb_ge_p2.trans (Nat.le_mul_of_pos_right _ (by omega))
  have hpow :
      p ^ q * (1 + p ^ (q - 2)) ≤ (p ^ (q - 1) + p ^ (q - 2)) ^ 2 := by
    have hq1 : q - 1 = q - 2 + 1 := by omega
    have hq2 : q = q - 2 + 2 := by omega
    rw [hq1, hq2]
    simp [pow_add]
    nlinarith [haux]
  exact hpow.trans hsqU

/-- For `q >= 5`, the non-kernel error bound is separated from every possible
coefficient `c <= |U|`.  This is the pure numerical input for the class-sum
bridge in Appendix C Lemma C.2. -/
theorem _root_.solution [Fact p.Prime] (hq : 5 ≤ q) :
    ∀ c : ℕ, c ≤ Nat.card (normOneUnits p q) →
      (Nat.card (normOneUnits p q) : ℝ) *
          (((p ^ q : ℕ) : ℝ) * √(((p ^ q : ℕ) : ℝ))) <
        ‖((Nat.card (normOneUnits p q) : ℂ) ^ 3 -
          (c : ℂ) * ((p ^ q : ℕ) : ℂ))‖ := by
  intro c hc
  let U := Nat.card (normOneUnits p q)
  let N := p ^ q
  let B := p ^ (q - 2)
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  have hU_gt_one : 1 < U := by
    dsimp [U]
    exact normOneUnits_card_gt_one p q (by omega)
  have hU_pos_nat : 0 < U := Nat.lt_trans Nat.zero_lt_one hU_gt_one
  have hN_pos_nat : 0 < N := by
    dsimp [N]
    exact pow_pos hp_pos q
  have hB_pos_nat : 0 < B := by
    dsimp [B]
    exact pow_pos hp_pos (q - 2)
  have hsq : N * (1 + B) ≤ U ^ 2 := by
    dsimp [U, N, B]
    exact normOneUnits_card_sq_ge_pow_mul_one_add_pow_sub_two p q hq
  have hsq_add : N + N * B ≤ U ^ 2 := by
    simpa [mul_add, add_comm, add_left_comm, add_assoc] using hsq
  have hcN_le_UN : c * N ≤ U * N := Nat.mul_le_mul_right N hc
  have hUN_le_U3 : U * N ≤ U ^ 3 := by
    calc
      U * N ≤ U * (N + N * B) := Nat.mul_le_mul_left U (Nat.le_add_right _ _)
      _ ≤ U * (U ^ 2) := Nat.mul_le_mul_left U hsq_add
      _ = U ^ 3 := by ring
  have hcn_le_U3 : c * N ≤ U ^ 3 := hcN_le_UN.trans hUN_le_U3
  have hdiff_nat_ge : U * N * B ≤ U ^ 3 - c * N := by
    apply Nat.le_sub_of_add_le
    calc
      U * N * B + c * N ≤ U * N * B + U * N := Nat.add_le_add_left hcN_le_UN _
      _ = U * (N + N * B) := by ring
      _ ≤ U * (U ^ 2) := Nat.mul_le_mul_left U hsq_add
      _ = U ^ 3 := by ring
  have hN_lt_Bsq_nat : N < B ^ 2 := by
    dsimp [N, B]
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by omega)
  have hN_lt_Bsq_real : (N : ℝ) < (B : ℝ) ^ 2 := by
    exact_mod_cast hN_lt_Bsq_nat
  have hsqrt_lt : √(N : ℝ) < (B : ℝ) := by
    exact (Real.sqrt_lt (by positivity : 0 ≤ (N : ℝ)) (by positivity : 0 ≤ (B : ℝ))).2
      hN_lt_Bsq_real
  have hleft_lt :
      (U : ℝ) * ((N : ℝ) * √(N : ℝ)) < (U : ℝ) * ((N : ℝ) * (B : ℝ)) := by
    have hU_pos_real : 0 < (U : ℝ) := by exact_mod_cast hU_pos_nat
    have hN_pos_real : 0 < (N : ℝ) := by exact_mod_cast hN_pos_nat
    exact mul_lt_mul_of_pos_left
      (mul_lt_mul_of_pos_left hsqrt_lt hN_pos_real) hU_pos_real
  have hnorm_eq :
      ‖((U : ℂ) ^ 3 - (c : ℂ) * (N : ℂ))‖ = ((U ^ 3 - c * N : ℕ) : ℝ) := by
    have hcomplex :
        ((U : ℂ) ^ 3 - (c : ℂ) * (N : ℂ)) = ((U ^ 3 - c * N : ℕ) : ℂ) := by
      rw [Nat.cast_sub hcn_le_U3]
      norm_num
    rw [hcomplex, Complex.norm_natCast]
  change (U : ℝ) * ((N : ℝ) * √(N : ℝ)) <
    ‖((U : ℂ) ^ 3 - (c : ℂ) * (N : ℂ))‖
  calc
    (U : ℝ) * ((N : ℝ) * √(N : ℝ))
        < (U : ℝ) * ((N : ℝ) * (B : ℝ)) := hleft_lt
    _ = ((U * N * B : ℕ) : ℝ) := by
      norm_num [Nat.cast_mul]
      ring_nf
    _ ≤ ((U ^ 3 - c * N : ℕ) : ℝ) := by exact_mod_cast hdiff_nat_ge
    _ = ‖((U : ℂ) ^ 3 - (c : ℂ) * (N : ℂ))‖ := hnorm_eq.symm

end OddOrder.BG.AppC.NormSet
