-- Prove2me | solution 1 for OpenQuantumProblem35.ghzState4_not_ame
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:10:13.783989+00:00
-- url     : https://prove2.me/submissions/ebc11455-f55b-4871-bd3d-faec60210e68

module
public import Mathlib
public import Definitions.Def_AME125_Defs
public import Theorems.Thm_OpenQuantumProblem35_mkStateVector_apply
public import Theorems.Thm_OpenQuantumProblem35_permuteState_apply
public import Theorems.Thm_OpenQuantumProblem35_permuteState_refl
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_leftIndex
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_rightIndex
public import Theorems.Thm_OpenQuantumProblem35_card_config
public import Theorems.Thm_OpenQuantumProblem35_maximallyMixed_apply
public import Theorems.Thm_OpenQuantumProblem35_diagonalState_apply
public import Theorems.Thm_OpenQuantumProblem35_diagonalState_combineFirst_two_of_ne
attribute [local simp] OpenQuantumProblem35.mkStateVector_apply
attribute [local simp] OpenQuantumProblem35.permuteState_apply
attribute [local simp] OpenQuantumProblem35.combineFirst_leftIndex
attribute [local simp] OpenQuantumProblem35.combineFirst_rightIndex
attribute [local simp] OpenQuantumProblem35.card_config
attribute [local simp] OpenQuantumProblem35.diagonalState_apply

set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35
namespace OpenQuantumProblem35
theorem _root_.solution {d : ℕ} (hd : 2 ≤ d) :
    ¬ IsAME (n := 4) (d := d) (ghzState4 d) := by
  intro hGHZ
  have hAME : IsAME (n := 4) (d := d) (diagonalState 4 d) := by
    simpa [ghzState4] using hGHZ
  let a0 : Fin d := ⟨0, by omega⟩
  let a1 : Fin d := ⟨1, by omega⟩
  let x01 : Config 2 d := fun i => if i = 0 then a0 else a1
  have hx01 : x01 0 ≠ x01 1 := by
    intro hEq
    have : (0 : ℕ) = 1 := by
      simpa [x01, a0, a1] using congrArg Fin.val hEq
    omega
  have hred0 :
      reducedDensityFirst (n := 4) (d := d) 2 (by decide) (diagonalState 4 d) x01 x01 = 0 := by
    rw [reducedDensityFirst]
    refine Finset.sum_eq_zero ?_
    intro z _
    have hz0 : diagonalState 4 d (combineFirst (n := 4) (d := d) 2 (by decide) x01 z) = 0 :=
      diagonalState_combineFirst_two_of_ne (x := x01) (z := z) hx01
    rw [hz0]
    simp
  have hentry :
      reducedDensityFirst (n := 4) (d := d) 2 (by decide) (diagonalState 4 d) x01 x01 =
        maximallyMixed 2 d x01 x01 := by
    have hredEq :
        reducedDensityFirst (n := 4) (d := d) 2 (by decide) (diagonalState 4 d) =
          maximallyMixed 2 d := by
      simpa [HasMaximallyMixedFirstReduction, permuteState_refl] using
        (hAME.2 (Equiv.refl (Fin 4)))
    exact congrArg (fun M : Matrix (Config 2 d) (Config 2 d) ℂ => M x01 x01) hredEq
  have hcontra : (0 : ℂ) = ((Fintype.card (Config 2 d) : ℂ)⁻¹) := by
    simpa [hred0, maximallyMixed_apply] using hentry
  have hcard_ne : (Fintype.card (Config 2 d) : ℂ) ≠ 0 := by
    have hd0 : d ≠ 0 := by omega
    have hcard_ne_nat : Fintype.card (Config 2 d) ≠ 0 := by
      simpa [card_config] using (pow_ne_zero 2 hd0)
    exact_mod_cast hcard_ne_nat
  exact (inv_ne_zero hcard_ne) hcontra.symm
end OpenQuantumProblem35
