-- Prove2me | solution 1 for OrderClosures.isSeparable_solovayVectorSublattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:08:44.997794+00:00
-- url     : https://prove2.me/submissions/64e8d1ab-4550-4dbd-add4-e86809f64b86

module
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
public import Mathlib.Order.Heyting.Regular
public import Mathlib.Order.BooleanSubalgebra
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Topology.Category.Stonean.Basic
public import Mathlib.Order.PrimeSeparator
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Definitions.Def_LeanPool_OrderClosures_Solovay
public import Theorems.Thm_OrderClosures_solovayVectorGenerators_countable
public import Theorems.Thm_VectorSublattice_separableSpace_topologicalClosure_generated_of_countable


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
theorem _root_.solution :
    TopologicalSpace.IsSeparable (solovayVectorSublattice Gamma :
      Set C(BooleanStone (RegularOpen (SolovayProduct Gamma)), ℝ)) := by
  let : TopologicalSpace.SeparableSpace
      (solovayVectorSublattice Gamma).toSubmodule :=
    VectorSublattice.separableSpace_topologicalClosure_generated_of_countable
      (solovayVectorGenerators_countable Gamma)
  exact TopologicalSpace.IsSeparable.of_subtype
    (solovayVectorSublattice Gamma :
      Set C(BooleanStone (RegularOpen (SolovayProduct Gamma)), ℝ))
end OrderClosures
