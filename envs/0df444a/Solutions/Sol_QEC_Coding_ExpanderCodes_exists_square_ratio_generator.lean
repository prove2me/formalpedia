-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.exists_square_ratio_generator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:32:42.10429+00:00
-- url     : https://prove2.me/submissions/e17a5a02-3367-4f37-8039-95ad071ea09d

import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldQuadraticSplitting
import Mathlib.GroupTheory.Coset.Card
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.Linarith
import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldSquareParameters
import Theorems.Thm_QEC_Coding_ExpanderCodes_adjoin_square_generator_eq_top

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes
open IntermediateField
namespace QEC.Coding.ExpanderCodes
theorem _root_.solution {F K : Type*} [Field F] [Field K]
    [Finite K] [Algebra F K] (hCard : 3 < Nat.card K) :
    ∃ y t : K, y ≠ 0 ∧ 1 + y ≠ 0 ∧ t ≠ 0 ∧
      t ^ 2 = y / (1 + y) ∧ adjoin F ({y} : Set K) = ⊤ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hSquareNeOne : (g : K) ^ 2 ≠ 1 := by
    intro hEqual
    have hDvd : Nat.card K - 1 ∣ 2 := by
      rw [← Nat.card_units, ← orderOf_eq_card_of_forall_mem_zpowers hg]
      exact orderOf_dvd_of_pow_eq_one (Units.ext hEqual)
    have := Nat.le_of_dvd (by decide : 0 < 2) hDvd
    omega
  have hDenom : 1 - (g : K) ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hSquareNeOne)
  let y : K := (g : K) ^ 2 / (1 - (g : K) ^ 2)
  have hY : y ≠ 0 := div_ne_zero (pow_ne_zero 2 g.ne_zero) hDenom
  have hOneEq : 1 + y = (1 - (g : K) ^ 2)⁻¹ := by
    dsimp [y]
    field_simp
    ring
  have hOne : 1 + y ≠ 0 := by rw [hOneEq]; exact inv_ne_zero hDenom
  have hRatio : y / (1 + y) = (g : K) ^ 2 := by
    rw [hOneEq]
    dsimp [y]
    field_simp
  have hTop : adjoin F ({y} : Set K) = ⊤ := by
    have hMem : (g : K) ^ 2 ∈ adjoin F ({y} : Set K) := by
      rw [← hRatio]
      exact div_mem (mem_adjoin_simple_self F y)
        (add_mem (one_mem _) (mem_adjoin_simple_self F y))
    have hLe : adjoin F ({(g : K) ^ 2} : Set K) ≤ adjoin F ({y} : Set K) :=
      adjoin_le_iff.mpr (by
        intro z hz
        have hzEq : z = (g : K) ^ 2 := Set.mem_singleton_iff.mp hz
        rw [hzEq]
        exact hMem)
    rw [adjoin_square_generator_eq_top g hg] at hLe
    exact top_unique hLe
  exact ⟨y, g, hY, hOne, g.ne_zero, hRatio.symm, hTop⟩
end QEC.Coding.ExpanderCodes
