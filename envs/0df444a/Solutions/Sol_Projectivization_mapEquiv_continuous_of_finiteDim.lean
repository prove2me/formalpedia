-- Prove2me | solution 1 for Projectivization.mapEquiv_continuous_of_finiteDim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:55:02.636303+00:00
-- url     : https://prove2.me/submissions/45edcb8f-cbcf-46b5-8f08-89e700b5323c

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
public import Theorems.Thm_Projectivization_mapEquiv_continuous

set_option autoImplicit false
@[expose] public section
public section
open Set Function Topology
open scoped LinearAlgebra.Projectivization
open Projectivization
variable {K V : Type*}
variable [RCLike K] [NormedAddCommGroup V] [NormedSpace K V] [FiniteDimensional K V]
namespace Projectivization
theorem _root_.solution (e : V ≃ₗ[K] V) :
    Continuous (mapEquiv e) :=
  mapEquiv_continuous e (e : V →ₗ[K] V).continuous_of_finiteDimensional
end Projectivization
