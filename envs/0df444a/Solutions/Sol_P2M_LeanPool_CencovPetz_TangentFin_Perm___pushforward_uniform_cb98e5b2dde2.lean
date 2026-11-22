-- Prove2me | solution 1 for P2M_LeanPool_CencovPetz_TangentFin_Perm___pushforward_uniform_cb98e5b2dde2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:28:48.820318+00:00
-- url     : https://prove2.me/submissions/91455f18-4437-4df8-b109-cd5290c5d115

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
public import Theorems.Thm_P2M_LeanPool_CencovPetz_TangentFin_Perm___pushforward_apply_c5efb4e6fc74
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
theorem _root_.solution {n : ℕ} [Nonempty (Fin n)] (σ : Equiv.Perm (Fin n)) :
    (κ (n := n) σ).pushforward (Simplex.uniform (α := Fin n)) = Simplex.uniform (α := Fin n) := by
  classical
  ext k
  rw [κ_pushforward_apply]
  simp [Simplex.uniform_apply]
end LeanPool.CencovPetz.TangentFin.Perm
