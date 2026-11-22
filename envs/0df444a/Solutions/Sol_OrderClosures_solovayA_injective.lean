-- Prove2me | solution 1 for OrderClosures.solovayA_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:06:40.818975+00:00
-- url     : https://prove2.me/submissions/5350eba9-347a-4f8f-9db0-099fd960f397

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
universe u
variable (Gamma : Type u) [LinearOrder Gamma] [TopologicalSpace Gamma]
  [DiscreteTopology Gamma]
namespace OrderClosures
theorem _root_.solution (n : ℕ) : Function.Injective (solovayA Gamma n) := by
  intro eta theta h
  by_contra hne
  have hsets := congrArg
    (fun U : RegularOpen (SolovayProduct Gamma) ↦
      (((U : TopologicalSpace.Opens (SolovayProduct Gamma)) :
        Set (SolovayProduct Gamma)))) h
  change {f : SolovayProduct Gamma | f n = eta} = {f | f n = theta} at hsets
  let f : SolovayProduct Gamma := fun _ ↦ eta
  have hf : f ∈ {g : SolovayProduct Gamma | g n = eta} := rfl
  rw [hsets] at hf
  exact hne hf
end OrderClosures
