-- Prove2me | solution 1 for OrderClosures.solovayVectorGenerators_countable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:07:24.709464+00:00
-- url     : https://prove2.me/submissions/5a805a69-d41c-4b32-837b-dcc9c6a77f7e

module
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
public import Mathlib.Order.Heyting.Regular
public import Mathlib.Order.BooleanSubalgebra
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Topology.Category.Stonean.Basic
public import Mathlib.Order.PrimeSeparator
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Definitions.Def_LeanPool_OrderClosures_Solovay

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
    (solovayVectorGenerators Gamma).Countable := by
  exact Set.countable_range _ |>.union (Set.countable_singleton _)
end OrderClosures
