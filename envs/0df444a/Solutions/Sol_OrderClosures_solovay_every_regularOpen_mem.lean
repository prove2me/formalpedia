-- Prove2me | solution 1 for OrderClosures.solovay_every_regularOpen_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:09:08.770572+00:00
-- url     : https://prove2.me/submissions/c6330858-196a-4f74-a9d9-2c6b0752a31e

module
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
public import Mathlib.Order.Heyting.Regular
public import Mathlib.Order.BooleanSubalgebra
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Topology.Category.Stonean.Basic
public import Mathlib.Order.PrimeSeparator
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Definitions.Def_LeanPool_OrderClosures_Solovay
public import Theorems.Thm_OrderClosures_regularOpen_eq_sSup_of_union
public import Theorems.Thm_OrderClosures_solovayCylinder_mem
public import Theorems.Thm_OrderClosures_solovay_union_cylinders_below

set_option autoImplicit true
@[expose] public section
public section
open Set
noncomputable section
open OrderClosures
universe u
variable (Gamma : Type u) [LinearOrder Gamma] [TopologicalSpace Gamma]
  [DiscreteTopology Gamma]
omit [LinearOrder Gamma]
namespace OrderClosures
theorem _root_.solution
    (L : BooleanSubalgebra (RegularOpen (SolovayProduct Gamma)))
    (hcomplete : IsCompleteBooleanSubalgebra L)
    (hA : ∀ n eta, solovayA Gamma n eta ∈ L)
    (U : RegularOpen (SolovayProduct Gamma)) : U ∈ L := by
  rw [regularOpen_eq_sSup_of_union U (solovayCylindersBelow Gamma U)
    (solovay_union_cylinders_below Gamma U)]
  apply hcomplete
  intro V hV
  rcases hV with ⟨F, g, rfl, hsub⟩
  exact solovayCylinder_mem Gamma L hA F g
end OrderClosures
