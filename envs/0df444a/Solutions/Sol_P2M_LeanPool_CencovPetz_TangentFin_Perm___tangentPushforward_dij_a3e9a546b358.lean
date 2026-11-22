-- Prove2me | solution 1 for P2M_LeanPool_CencovPetz_TangentFin_Perm___tangentPushforward_dij_a3e9a546b358
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:28:48.447034+00:00
-- url     : https://prove2.me/submissions/6993eb53-7c40-44d1-aa33-49274b4cd497

module
public import Definitions.Def_LeanPool_CencovPetz_UniformSimplex
public import Definitions.Def_LeanPool_CencovPetz_MonotoneMetric
public import Definitions.Def_LeanPool_CencovPetz_PermutationInvariance
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_PermutationInvariantBilinForm
public import Theorems.Thm_LeanPool_CencovPetz_TangentFin_Basis_dij_coe
public import Theorems.Thm_LeanPool_CencovPetz_TangentFin_Basis_dij_self
public import Theorems.Thm_P2M_LeanPool_CencovPetz_TangentFin_Perm___tangentPushforward_apply_274bdaf2bfd5
public import Theorems.Thm_LeanPool_CencovPetz_TangentFin_Perm_e_apply_symm
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_tangentPushforwardLinear_apply
public import Theorems.Thm_LeanPool_CencovPetz_Simplex_uniform_apply
public import Theorems.Thm_LeanPool_CencovPetz_fisherBilin_apply
public import Theorems.Thm_LeanPool_CencovPetz_tangentPushforward_apply
attribute [local simp] LeanPool.CencovPetz.MarkovMorphism.tangentPushforwardLinear_apply
attribute [local simp] LeanPool.CencovPetz.Simplex.uniform_apply
attribute [local simp] LeanPool.CencovPetz.fisherBilin.apply
attribute [local simp] LeanPool.CencovPetz.tangentPushforward_apply


attribute [local simp] LeanPool.CencovPetz.TangentFin.Basis.dij_coe
attribute [local simp] LeanPool.CencovPetz.TangentFin.Basis.dij_self

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
universe u
variable {n : ℕ}
open LeanPool.CencovPetz.TangentFin
open LeanPool.CencovPetz.TangentFin.Perm
open _root_.LeanPool.CencovPetz.TangentFin.Basis
namespace LeanPool.CencovPetz.TangentFin.Perm
theorem _root_.solution (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    (κ (n := n) σ).tangentPushforward (Basis.dij (n := n) i j) =
      Basis.dij (n := n) (σ i) (σ j) := by
  classical
  ext k
  rw [κ_tangentPushforward_apply]
  simp [Basis.dij_coe, e_apply_symm]
end LeanPool.CencovPetz.TangentFin.Perm
