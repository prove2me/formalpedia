-- Prove2me | solution 1 for Projectivization.mapOfInjective_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:53:40.117826+00:00
-- url     : https://prove2.me/submissions/56227322-e590-4081-9e0a-a64809af916b

module
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Definitions.Def_BornVolumeLean_Topology_Algebra_MulAction
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Maps.OpenQuotient
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Topology.Separation.Hausdorff
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_Topology
public import Theorems.Thm_Projectivization_continuous_iff

set_option autoImplicit false
@[expose] public section
public section
open Set Function Topology
open scoped LinearAlgebra.Projectivization
open Projectivization
variable {K V : Type*}
variable [DivisionRing K] [AddCommGroup V] [Module K V]
variable [TopologicalSpace V]
variable {W : Type*} [AddCommGroup W] [Module K W] [TopologicalSpace W]
namespace Projectivization
theorem _root_.solution
    (f : V →ₗ[K] W) (hf : Function.Injective f) (hf_cont : Continuous f) :
    Continuous (Projectivization.map f hf) := by
  rw [continuous_iff]
  -- The composition `(map f hf) ∘ mk' K` equals `mk' K ∘ f_sub` where
  -- `f_sub` is the corestriction of `f` to the nonzero subtype (with
  -- output non-zero via `hf`). Both factors are continuous: `mk'` by
  -- `continuous_mk'`, and `f_sub` via `subtype_mk` applied to `f`'s
  -- continuity composed with subtype projection.
  exact continuous_mk'.comp
    ((hf_cont.comp continuous_subtype_val).subtype_mk _)
end Projectivization
