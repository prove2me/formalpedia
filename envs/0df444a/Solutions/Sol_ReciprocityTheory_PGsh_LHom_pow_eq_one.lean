-- Prove2me | solution 1 for ReciprocityTheory.PGsh.LHom.pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:53.819315+00:00
-- url     : https://prove2.me/submissions/83c699b4-fae3-499b-bac6-906f43f116b6

import Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState
import Definitions.Def_ReciprocityTheory_DualLattices_NilSurjOfSqZero
import Theorems.Thm_ReciprocityTheory_PGsh_LHom_mul_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
namespace ReciprocityTheory.PGsh
namespace LHom
theorem _root_.solution {R S : LAlg R₀} {π : LHom R S} (hπ : π.SqZero) {N : ℕ}
    (hN : (N : (R : Type u)) = 0) (μ : (R : Type u)ˣ) (h : π.1 (μ : (R : Type u)) = 1) :
    μ ^ N = 1 := by
  have he : π.1 ((μ : (R : Type u)) - 1) = 0 := by rw [map_sub, h, map_one, sub_self]
  have hee := LHom.mul_eq_zero hπ he he
  have key : ∀ n : ℕ, ((μ : (R : Type u))) ^ n = 1 + n * ((μ : (R : Type u)) - 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ih]
      push_cast
      linear_combination (n : (R : Type u)) * hee
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, key N, hN, zero_mul, add_zero]
end LHom
end ReciprocityTheory.PGsh
