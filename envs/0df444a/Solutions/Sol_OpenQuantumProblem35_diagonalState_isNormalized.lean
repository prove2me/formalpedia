-- Prove2me | solution 1 for OpenQuantumProblem35.diagonalState_isNormalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:08:02.83045+00:00
-- url     : https://prove2.me/submissions/c0e58782-d5fb-4b09-b9c5-1642a031473c

module
public import Mathlib
public import Definitions.Def_AME125_Defs
public import Theorems.Thm_OpenQuantumProblem35_mkStateVector_apply
public import Theorems.Thm_OpenQuantumProblem35_isNormalized_iff_norm_sq_eq_one
public import Theorems.Thm_OpenQuantumProblem35_permuteState_apply
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_leftIndex
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_rightIndex
public import Theorems.Thm_OpenQuantumProblem35_card_config
public import Theorems.Thm_OpenQuantumProblem35_diagonalState_apply
public import Theorems.Thm_OpenQuantumProblem35_constantConfig_injective
public import Theorems.Thm_OpenQuantumProblem35_isConstantConfig_iff_exists_constantConfig
public import Theorems.Thm_OpenQuantumProblem35_uniformCoeff_norm_sq
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
theorem _root_.solution {n d : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d) :
    IsNormalized (diagonalState n d) := by
  classical
  let S : Finset (Config n d) := Finset.univ.filter (fun x : Config n d => IsConstantConfig x)
  have hS :
      S = Finset.image (constantConfig (m := n) (d := d)) (Finset.univ : Finset (Fin d)) := by
    ext x
    simp [S, isConstantConfig_iff_exists_constantConfig (hn := hn) (x := x), eq_comm]
  have hcardS : S.card = d := by
    rw [hS]
    simpa using
      (Finset.card_image_of_injective
        (s := (Finset.univ : Finset (Fin d)))
        (f := constantConfig (m := n) (d := d))
        (constantConfig_injective (n := n) (d := d) hn))
  have hnorm_sq :
      ‖diagonalState n d‖ ^ 2 = 1 := by
    calc
      ‖diagonalState n d‖ ^ 2
          = ∑ x : Config n d, ‖diagonalState n d x‖ ^ 2 := by
              simpa using (EuclideanSpace.norm_sq_eq (diagonalState n d))
      _ = ∑ x : Config n d,
            if IsConstantConfig x then ‖uniformCoeff d‖ ^ 2 else 0 := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            by_cases hconst : IsConstantConfig x
            · simp [diagonalState_apply, hconst]
            · simp [diagonalState_apply, hconst]
      _ = (S.card : ℝ) * ‖uniformCoeff d‖ ^ 2 := by
            rw [← Finset.sum_filter
              (s := Finset.univ)
              (p := fun x : Config n d => IsConstantConfig x)
              (f := fun _ => ‖uniformCoeff d‖ ^ 2)]
            simp [S, Finset.sum_const, nsmul_eq_mul]
      _ = (d : ℝ) * ‖uniformCoeff d‖ ^ 2 := by
            rw [hcardS]
      _ = (d : ℝ) * ((d : ℝ)⁻¹) := by
            rw [uniformCoeff_norm_sq]
      _ = 1 := by
            have hd0 : d ≠ 0 := by omega
            have hdr : (d : ℝ) ≠ 0 := by
              exact_mod_cast hd0
            simpa using (mul_inv_cancel₀ hdr)
  exact (isNormalized_iff_norm_sq_eq_one (diagonalState n d)).2 hnorm_sq
end OpenQuantumProblem35
