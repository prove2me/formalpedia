-- Prove2me | solution 1 for OrderClosures.solovayVectorGenerator_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:07:27.596934+00:00
-- url     : https://prove2.me/submissions/5cef8825-e31b-427c-ae5d-70fcbe7f7189

module
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
public import Mathlib.Order.Heyting.Regular
public import Mathlib.Order.BooleanSubalgebra
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Topology.Category.Stonean.Basic
public import Mathlib.Order.PrimeSeparator
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Definitions.Def_LeanPool_OrderClosures_Solovay
public import Theorems.Thm_VectorSublattice_subset_generated


set_option autoImplicit true
@[expose] public section
public section
open Set
noncomputable section
open OrderClosures
universe u v
variable (Gamma : Type u) [LinearOrder Gamma] [WellFoundedLT Gamma]
  [TopologicalSpace Gamma] [DiscreteTopology Gamma]
omit [WellFoundedLT Gamma]
namespace OrderClosures
theorem _root_.solution
    {f : C(BooleanStone (RegularOpen (SolovayProduct Gamma)), ℝ)}
    (hf : f ∈ solovayVectorGenerators Gamma) :
    f ∈ solovayVectorSublattice Gamma := by
  exact
    (VectorSublattice.generated
      (solovayVectorGenerators Gamma)).toSubmodule.le_topologicalClosure
        (VectorSublattice.subset_generated (solovayVectorGenerators Gamma) hf)
end OrderClosures
