-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.dominantCoweight_eq_fundamental_one_of_sum_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:05:43.24223+00:00
-- url     : https://prove2.me/submissions/56e235a6-06fc-40c8-8594-5fb488903c63

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) (weight : DominantCoweight d)
    (hsum : ∑ i, weight.exponent i = 1) :
    weight = fundamentalDominantCoweight d 1 := by
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  have hterm_le_one (i : Fin d) : weight.exponent i ≤ 1 := by
    calc
      weight.exponent i ≤ ∑ j, weight.exponent j := by
        exact Finset.single_le_sum
          (fun j _ => Nat.zero_le (weight.exponent j))
          (Finset.mem_univ i)
      _ = 1 := hsum
  have hfirst_ne_zero : weight.exponent (0 : Fin d) ≠ 0 := by
    intro hzero
    have hall : ∀ i, weight.exponent i = 0 := by
      intro i
      exact Nat.eq_zero_of_le_zero
        (hzero ▸ weight.antitone_exponent (Fin.zero_le i))
    have hsumZero : ∑ i, weight.exponent i = 0 := by
      simp [hall]
    omega
  have hfirst : weight.exponent (0 : Fin d) = 1 := by
    have hle := hterm_le_one (0 : Fin d)
    omega
  apply DominantCoweight.ext
  funext i
  simp only [fundamentalDominantCoweight]
  split_ifs with hi
  · have hiZero : i = 0 := by
      apply Fin.ext
      simp only [Fin.val_zero]
      omega
    simpa [hiZero] using hfirst
  · have hiNeZero : i ≠ 0 := by
      intro hiZero
      subst i
      simp at hi
    by_contra hnonzero
    have hiPos : 1 ≤ weight.exponent i :=
      Nat.one_le_iff_ne_zero.mpr hnonzero
    have hzeroMem : (0 : Fin d) ∈ Finset.univ.erase i := by
      simp [hiNeZero.symm]
    have hzeroLe : weight.exponent (0 : Fin d) ≤
        ∑ j ∈ Finset.univ.erase i, weight.exponent j := by
      exact Finset.single_le_sum
        (fun j _ => Nat.zero_le (weight.exponent j)) hzeroMem
    have hsplit := Finset.sum_erase_add
      (Finset.univ : Finset (Fin d)) weight.exponent (Finset.mem_univ i)
    rw [hsum] at hsplit
    omega
end QEC.Coding.HighDimensionalExpander.SphericalHecke
