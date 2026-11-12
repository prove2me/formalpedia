-- Prove2me | solution 1 for OddOrder.RepresentationTheory.classSumCoeff_mul_centralizer_card_eq_sum_irreducibleCharacter
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:08:36.900031+00:00
-- url     : https://prove2.me/submissions/aacdca89-eb38-4838-9c84-3879cd431956

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/CharacterCompleteness.lean
--   OddOrder/GroupTheory/RepresentationTheory/ClassSumCoefficientFormula.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterCount
import Definitions.Def_OddOrder_Mathlib_MonoidAlgebra
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ClassSumAlgebra
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterCompleteness
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Maschke
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

-- ===== OddOrder/GroupTheory/RepresentationTheory/CharacterCompleteness.lean =====
namespace OddOrder.RepresentationTheory

open Module (finrank)

section Count

variable {G : Type*} [Group G]

open Module (finrank)

/-- Irreducible character values satisfy `χ(g⁻¹) = star (χ(g))`. -/
theorem irreducibleCharacter_apply_inv [Finite G]
    (χ : IrreducibleCharacter G) (g : G) :
    (χ : ClassFunction G ℂ) g⁻¹ = star ((χ : ClassFunction G ℂ) g) := by
  obtain ⟨V, _, _, _, ρ, _, hχ⟩ := χ.isIrreducible
  rw [congrFun hχ g⁻¹, congrFun hχ g, character_inv ρ g]

end Count

end OddOrder.RepresentationTheory

-- ===== OddOrder/GroupTheory/RepresentationTheory/ClassSumCoefficientFormula.lean =====
namespace OddOrder.RepresentationTheory

open OddOrder.GroupTheory.CenterClassSum

variable {G : Type*} [Group G]

set_option backward.isDefEq.respectTransparency false in
/-- The chosen representative of a conjugacy class lies in that class. -/
theorem conjClass_mk_out (C : ConjClasses G) : ConjClasses.mk C.out = C := by
  rw [← ConjClasses.quotient_mk_eq_mk, Quotient.out_eq]

section Formula

variable [Fintype G] [DecidableEq (ConjClasses G)]

/-- The central-character product formula, expressed using only an irreducible-character
subtype value.  For a fixed irreducible character `χ`, summing the class-sum pair-count
coefficients against `χ` gives the expected product of the two central-character values. -/
theorem sum_classSumCoeff_mul_irreducibleCharacter_apply
    [Fintype (ConjClasses G)] (Ci Cj : ConjClasses G)
    (χ : IrreducibleCharacter G) :
    (∑ Cs : ConjClasses G,
        (classSumCoeff Ci Cj Cs : ℂ) *
          (χ : ClassFunction G ℂ) Cs.out) =
      ((Nat.card { x : G // ConjClasses.mk x = Ci } : ℂ) *
          (χ : ClassFunction G ℂ) Ci.out *
        ((Nat.card { x : G // ConjClasses.mk x = Cj } : ℂ) *
          (χ : ClassFunction G ℂ) Cj.out)) /
        (χ : ClassFunction G ℂ) (1 : G) := by
  classical
  obtain ⟨V, _, _, _, ρ, hρ, hχ⟩ := χ.isIrreducible
  have : Representation.IsIrreducible ρ := hρ
  have hdegree : ρ.character (1 : G) ≠ 0 := by
    have := nontrivial_of_isIrreducible ρ
    rw [ρ.char_one]
    exact Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  let ω : ConjClasses G → ℂ := fun C =>
    centralCharacterOfRep ρ ⟨classSum C, classSum_mem_center C⟩
  have hprod :
      ρ.character (1 : G) * (ω Ci * ω Cj) =
        ∑ Cs : ConjClasses G,
          (classSumCoeff Ci Cj Cs : ℂ) * ρ.character Cs.out := by
    rw [centralCharacterOfRep_classSum_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun Cs _ => ?_
    simpa [ω, smul_eq_mul, mul_assoc] using
      character_one_mul_coeff_mul_centralChar ρ Ci Cj Cs
  have hωi : ω Ci =
      ((Nat.card { x : G // ConjClasses.mk x = Ci } : ℂ) * ρ.character Ci.out) /
        ρ.character (1 : G) := by
    change centralCharacterOfRep ρ ⟨classSum Ci, classSum_mem_center Ci⟩ =
      ((Nat.card { x : G // ConjClasses.mk x = Ci } : ℂ) * ρ.character Ci.out) /
        ρ.character (1 : G)
    rw [centralCharacterOfRep_classSum,
      sum_character_eq_card_mul ρ Ci (conjClass_mk_out Ci), ρ.char_one]
  have hωj : ω Cj =
      ((Nat.card { x : G // ConjClasses.mk x = Cj } : ℂ) * ρ.character Cj.out) /
        ρ.character (1 : G) := by
    change centralCharacterOfRep ρ ⟨classSum Cj, classSum_mem_center Cj⟩ =
      ((Nat.card { x : G // ConjClasses.mk x = Cj } : ℂ) * ρ.character Cj.out) /
        ρ.character (1 : G)
    rw [centralCharacterOfRep_classSum,
      sum_character_eq_card_mul ρ Cj (conjClass_mk_out Cj), ρ.char_one]
  have hleft :
      ρ.character (1 : G) * (ω Ci * ω Cj) =
        ((Nat.card { x : G // ConjClasses.mk x = Ci } : ℂ) * ρ.character Ci.out *
          ((Nat.card { x : G // ConjClasses.mk x = Cj } : ℂ) * ρ.character Cj.out)) /
          ρ.character (1 : G) := by
    rw [hωi, hωj]
    field_simp [hdegree]
  calc
    (∑ Cs : ConjClasses G,
        (classSumCoeff Ci Cj Cs : ℂ) *
          (χ : ClassFunction G ℂ) Cs.out)
        = ∑ Cs : ConjClasses G,
            (classSumCoeff Ci Cj Cs : ℂ) * ρ.character Cs.out := by
          refine Finset.sum_congr rfl fun Cs _ => ?_
          rw [congrFun hχ Cs.out]
    _ = ρ.character (1 : G) * (ω Ci * ω Cj) := hprod.symm
    _ = ((Nat.card { x : G // ConjClasses.mk x = Ci } : ℂ) * ρ.character Ci.out *
          ((Nat.card { x : G // ConjClasses.mk x = Cj } : ℂ) * ρ.character Cj.out)) /
          ρ.character (1 : G) := hleft
    _ = ((Nat.card { x : G // ConjClasses.mk x = Ci } : ℂ) *
          (χ : ClassFunction G ℂ) Ci.out *
        ((Nat.card { x : G // ConjClasses.mk x = Cj } : ℂ) *
          (χ : ClassFunction G ℂ) Cj.out)) /
        (χ : ClassFunction G ℂ) (1 : G) := by
          rw [congrFun hχ Ci.out, congrFun hχ Cj.out, congrFun hχ (1 : G)]

/-- Class-sum coefficient formula with the centralizer factor left explicit.
For a target class `Cs`, multiplying the pair-count coefficient by `|C_G(Cs.out)|`
inverts the single-character central-character product formula by column orthogonality. -/
theorem _root_.solution
    (Ci Cj Cs : ConjClasses G) :
    (classSumCoeff Ci Cj Cs : ℂ) *
        (Nat.card (Subgroup.centralizer ({Cs.out} : Set G)) : ℂ) =
      ∑ χ : IrreducibleCharacter G,
        (((Nat.card { x : G // ConjClasses.mk x = Ci } : ℂ) *
            (χ : ClassFunction G ℂ) Ci.out *
          ((Nat.card { x : G // ConjClasses.mk x = Cj } : ℂ) *
            (χ : ClassFunction G ℂ) Cj.out)) /
          (χ : ClassFunction G ℂ) (1 : G)) *
          (χ : ClassFunction G ℂ) Cs.out⁻¹ := by
  classical
  let : Fintype (ConjClasses G) := Fintype.ofFinite _
  let coeff : ConjClasses G → ℂ := fun C => (classSumCoeff Ci Cj C : ℂ)
  let invVal : IrreducibleCharacter G → ℂ := fun χ =>
    (χ : ClassFunction G ℂ) Cs.out⁻¹
  let cent : ℂ := (Nat.card (Subgroup.centralizer ({Cs.out} : Set G)) : ℂ)
  have hcol : ∀ C : ConjClasses G,
      (∑ χ : IrreducibleCharacter G,
          (χ : ClassFunction G ℂ) C.out * invVal χ) =
        if C = Cs then cent else 0 := by
    intro C
    by_cases hC : C = Cs
    · subst C
      have h := column_orthogonality_diagonal (G := G) Cs.out
      simpa [invVal, cent, ← irreducibleCharacter_apply_inv] using h
    · have hnot : ¬ IsConj C.out Cs.out := by
        intro hconj
        apply hC
        have hmk : ConjClasses.mk C.out = ConjClasses.mk Cs.out :=
          ConjClasses.mk_eq_mk_iff_isConj.mpr hconj
        rwa [conjClass_mk_out C, conjClass_mk_out Cs] at hmk
      have h := column_orthogonality_not_conjugate (G := G) hnot
      simpa [invVal, ← irreducibleCharacter_apply_inv, hC] using h
  have hleft :
      (∑ χ : IrreducibleCharacter G,
          (∑ C : ConjClasses G,
            coeff C * (χ : ClassFunction G ℂ) C.out) * invVal χ) =
        coeff Cs * cent := by
    calc
      (∑ χ : IrreducibleCharacter G,
          (∑ C : ConjClasses G,
            coeff C * (χ : ClassFunction G ℂ) C.out) * invVal χ)
          = ∑ χ : IrreducibleCharacter G,
              ∑ C : ConjClasses G,
                (coeff C * (χ : ClassFunction G ℂ) C.out) * invVal χ := by
            refine Finset.sum_congr rfl fun χ _ => ?_
            rw [Finset.sum_mul]
      _ = ∑ C : ConjClasses G,
            ∑ χ : IrreducibleCharacter G,
              (coeff C * (χ : ClassFunction G ℂ) C.out) * invVal χ := by
            rw [Finset.sum_comm]
      _ = ∑ C : ConjClasses G,
            coeff C *
              ∑ χ : IrreducibleCharacter G,
                (χ : ClassFunction G ℂ) C.out * invVal χ := by
            refine Finset.sum_congr rfl fun C _ => ?_
            calc
              (∑ χ : IrreducibleCharacter G,
                  (coeff C * (χ : ClassFunction G ℂ) C.out) * invVal χ)
                  = ∑ χ : IrreducibleCharacter G,
                      coeff C * ((χ : ClassFunction G ℂ) C.out * invVal χ) := by
                    refine Finset.sum_congr rfl fun χ _ => ?_
                    ring
              _ = coeff C *
                    ∑ χ : IrreducibleCharacter G,
                      (χ : ClassFunction G ℂ) C.out * invVal χ := by
                    rw [Finset.mul_sum]
      _ = coeff Cs * cent := by
            rw [Finset.sum_eq_single Cs]
            · rw [hcol Cs, if_pos rfl]
            · intro C _ hC
              rw [hcol C, if_neg hC, mul_zero]
            · intro hCs
              exact (hCs (Finset.mem_univ Cs)).elim
  have hright :
      (∑ χ : IrreducibleCharacter G,
          (∑ C : ConjClasses G,
            coeff C * (χ : ClassFunction G ℂ) C.out) * invVal χ) =
        ∑ χ : IrreducibleCharacter G,
          (((Nat.card { x : G // ConjClasses.mk x = Ci } : ℂ) *
              (χ : ClassFunction G ℂ) Ci.out *
            ((Nat.card { x : G // ConjClasses.mk x = Cj } : ℂ) *
              (χ : ClassFunction G ℂ) Cj.out)) /
            (χ : ClassFunction G ℂ) (1 : G)) *
            (χ : ClassFunction G ℂ) Cs.out⁻¹ := by
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [sum_classSumCoeff_mul_irreducibleCharacter_apply Ci Cj χ]
  exact hleft.symm.trans hright

end Formula

end OddOrder.RepresentationTheory
