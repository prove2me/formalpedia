-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.exists_full_degree_parameter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:44:36.446513+00:00
-- url     : https://prove2.me/submissions/393f3aac-e179-4ddc-a555-1df2254db5c6

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement
import Lean.Elab.Tactic.Omega
import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldSpecialization

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes
open IntermediateField
namespace QEC.Coding.ExpanderCodes
theorem _root_.solution (p n : ℕ) [Fact p.Prime] (hDegree : 1 < n) :
    ∃ y : GaloisField p n, y ≠ 0 ∧ 1 + y ≠ 0 ∧
      Irreducible (minpoly (ZMod p) y) ∧
      (minpoly (ZMod p) y).natDegree = n ∧
      adjoin (ZMod p) ({y} : Set (GaloisField p n)) = ⊤ := by
  have hNonzero : n ≠ 0 := by omega
  obtain ⟨y, hGenerate⟩ :=
    Field.exists_primitive_element_of_finite_top (ZMod p) (GaloisField p n)
  have hProper : (⊥ : IntermediateField (ZMod p) (GaloisField p n)) ≠ ⊤ := by
    intro hEqual
    have hRank := bot_eq_top_iff_finrank_eq_one.mp hEqual
    rw [GaloisField.finrank p hNonzero] at hRank
    omega
  refine ⟨y, ?_, ?_, minpoly.irreducible (IsIntegral.of_finite (ZMod p) y), ?_,
    hGenerate⟩
  · intro hZero
    apply hProper
    simpa only [hZero, adjoin_zero] using hGenerate
  · intro hZero
    have hNegative : y = -(1 : GaloisField p n) := eq_neg_of_add_eq_zero_right hZero
    have hBot : adjoin (ZMod p) ({y} : Set (GaloisField p n)) = ⊥ :=
      adjoin_simple_eq_bot_iff.mpr (by
        rw [hNegative]
        exact (⊥ : IntermediateField (ZMod p) (GaloisField p n)).neg_mem
          (one_mem _))
    exact hProper (hBot.symm.trans hGenerate)
  · have hRank := (Field.primitive_element_iff_minpoly_natDegree_eq (ZMod p) y).mp
      hGenerate
    simpa only [GaloisField.finrank p hNonzero] using hRank
end QEC.Coding.ExpanderCodes
