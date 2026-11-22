-- Prove2me | solution 1 for Projectivization.mapEquiv_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:54:26.118671+00:00
-- url     : https://prove2.me/submissions/68e57dae-8e17-4a11-bd78-71c4eacf1408

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
public import Theorems.Thm_Projectivization_mapOfInjective_continuous

set_option autoImplicit false
@[expose] public section
public section
open Set Function Topology
open scoped LinearAlgebra.Projectivization
open Projectivization
variable {K V : Type*}
variable [DivisionRing K] [AddCommGroup V] [Module K V]
variable [TopologicalSpace V]
namespace Projectivization
theorem _root_.solution (e : V ≃ₗ[K] V) (he : Continuous (e : V → V)) :
    Continuous (mapEquiv e) :=
  mapOfInjective_continuous e.toLinearMap e.injective he
end Projectivization
