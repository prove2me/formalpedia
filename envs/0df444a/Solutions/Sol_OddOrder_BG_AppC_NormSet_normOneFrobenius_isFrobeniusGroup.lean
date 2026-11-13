-- Prove2me | solution 1 for OddOrder.BG.AppC.NormSet.normOneFrobenius_isFrobeniusGroup
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T07:38:04.259072+00:00
-- url     : https://prove2.me/submissions/492e8749-f007-493d-9de7-45a70f6068f4

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

-- ===== OddOrder/BG/AppC_NormOneInduce.lean =====
namespace OddOrder.BG.AppC.NormSet

open OddOrder.RepresentationTheory

open scoped commutatorElement

variable (p q : ℕ)

/-- In `H = P ⋊ U`, the additive kernel is normal. -/
theorem normOneFrobeniusKernel_normal [Fact p.Prime] :
    (normOneFrobeniusKernel p q).Normal := by
  unfold normOneFrobeniusKernel normOneFrobeniusGroup
  exact OddOrder.Isaacs.Ch03.inl_range_normal (φ := normOneMulAction p q)

/-- In `H = P ⋊ U`, the additive kernel and norm-one complement are complements. -/
theorem normOneFrobeniusKernel_isComplement_normOneFrobeniusComplement [Fact p.Prime] :
    (normOneFrobeniusKernel p q).IsComplement' (normOneFrobeniusComplement p q) := by
  unfold normOneFrobeniusKernel normOneFrobeniusComplement normOneFrobeniusGroup
  exact OddOrder.Isaacs.Ch03.inl_range_isComplement_inr_range (φ := normOneMulAction p q)

/-- The additive kernel in `H = P ⋊ U` is nontrivial. -/
theorem normOneFrobeniusKernel_ne_bot [Fact p.Prime] :
    normOneFrobeniusKernel p q ≠ ⊥ := by
  intro hbot
  have hmem :
      (SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q)) :
        normOneFrobeniusGroup p q) ∈ normOneFrobeniusKernel p q :=
    ⟨Multiplicative.ofAdd (1 : GaloisField p q), rfl⟩
  have h_eq_one :
      (SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q)) :
        normOneFrobeniusGroup p q) = 1 := by
    rw [hbot] at hmem
    exact hmem
  have hfield_zero : (1 : GaloisField p q) = 0 :=
    ofAdd_eq_one.mp (SemidirectProduct.inl_inj.mp h_eq_one)
  exact one_ne_zero hfield_zero

/-- If `1 < q`, then the norm-one complement in `H = P ⋊ U` is nontrivial. -/
theorem normOneFrobeniusComplement_ne_bot [Fact p.Prime] (hq : 1 < q) :
    normOneFrobeniusComplement p q ≠ ⊥ := by
  have hcard : 1 < Nat.card (normOneFrobeniusComplement p q) := by
    unfold normOneFrobeniusComplement
    have h := Nat.card_congr (Equiv.ofInjective _ SemidirectProduct.inr_injective
      (β := normOneFrobeniusGroup p q))
    exact h ▸ normOneUnits_card_gt_one p q hq
  exact (Subgroup.one_lt_card_iff_ne_bot _).mp hcard

/-- The concrete group `H = P ⋊ U` used in BG Appendix C is a Frobenius group
with additive kernel `P` and norm-one complement `U`. -/
theorem _root_.solution [Fact p.Prime] (hq : 1 < q) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup (normOneFrobeniusGroup p q)
      (normOneFrobeniusKernel p q) (normOneFrobeniusComplement p q) where
  isNormal := normOneFrobeniusKernel_normal p q
  isComplement := normOneFrobeniusKernel_isComplement_normOneFrobeniusComplement p q
  ne_bot_kernel := normOneFrobeniusKernel_ne_bot p q
  ne_bot_complement := normOneFrobeniusComplement_ne_bot p q hq
  conj_frobenius := by
    intro a haA ha n hnN hn hfix
    rcases haA with ⟨u, rfl⟩
    rcases hnN with ⟨x, rfl⟩
    have hx : x.toAdd ≠ (0 : GaloisField p q) := by
      intro hx0
      apply hn
      rw [← ofAdd_toAdd x, hx0, ofAdd_zero, map_one]
    have hfix' :
        SemidirectProduct.inl
            (Multiplicative.ofAdd
              (((u : (GaloisField p q)ˣ) : GaloisField p q) * x.toAdd)) =
          (SemidirectProduct.inl (Multiplicative.ofAdd x.toAdd) :
            normOneFrobeniusGroup p q) := by
      rw [← normOneFrobenius_conj_inl p q u x.toAdd]
      simpa [ofAdd_toAdd] using hfix
    have hmul :
        (((u : (GaloisField p q)ˣ) : GaloisField p q) * x.toAdd) = x.toAdd :=
      Multiplicative.ofAdd.injective (SemidirectProduct.inl_inj.mp hfix')
    have huval : ((u : (GaloisField p q)ˣ) : GaloisField p q) = 1 := by
      apply mul_right_cancel₀ hx
      simpa using hmul
    have hu : u = 1 := by
      apply Subtype.ext
      exact Units.ext huval
    exact ha (by simp [hu])

end OddOrder.BG.AppC.NormSet
