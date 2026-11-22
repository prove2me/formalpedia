-- Prove2me | solution 1 for OrderClosures.solovayBad_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:06:20.242975+00:00
-- url     : https://prove2.me/submissions/0cfaced8-54e3-4398-8752-540a8542b852

module
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
public import Mathlib.Order.Heyting.Regular
public import Mathlib.Order.BooleanSubalgebra
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Topology.Category.Stonean.Basic
public import Mathlib.Order.PrimeSeparator
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Definitions.Def_LeanPool_OrderClosures_Solovay
public import Theorems.Thm_OrderClosures_regularOpenOfClopen_congr
public import Theorems.Thm_OrderClosures_regularOpenOfClopen_inf

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
theorem _root_.solution (m n : ℕ) (eta : Gamma) :
    solovayBad Gamma m n eta =
      solovayStrict Gamma m n ⊓ solovayNotLT Gamma m eta := by
  unfold solovayStrict solovayNotLT
  rw [← regularOpenOfClopen_inf]
  apply regularOpenOfClopen_congr
  rfl
end OrderClosures
