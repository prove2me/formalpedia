-- Prove2me | solution 1 for OrderClosures.solovayVectorSublattice_maximalOrderClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:12:11.439806+00:00
-- url     : https://prove2.me/submissions/3c769e24-fb2b-49e2-a911-980790c05de7

module
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
public import Mathlib.Order.Heyting.Regular
public import Mathlib.Order.BooleanSubalgebra
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Topology.Category.Stonean.Basic
public import Mathlib.Order.PrimeSeparator
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Definitions.Def_LeanPool_OrderClosures_Solovay
public import Theorems.Thm_OrderClosures_solovay_generates_regularOpen
public import Theorems.Thm_OrderClosures_booleanSubalgebraInVectorSublattice_complete
public import Theorems.Thm_OrderClosures_vectorSublattice_eq_top_of_booleanStoneIndicators
public import Theorems.Thm_OrderClosures_solovayVectorGenerator_mem

set_option autoImplicit true
@[expose] public section
public section
open Set
noncomputable section
open OrderClosures
universe u v
variable (Gamma : Type u) [LinearOrder Gamma] [WellFoundedLT Gamma]
  [TopologicalSpace Gamma] [DiscreteTopology Gamma]
namespace OrderClosures
theorem _root_.solution
    (Z : VectorSublattice
      C(BooleanStone (RegularOpen (SolovayProduct Gamma)), ℝ))
    (hYZ : solovayVectorSublattice Gamma ≤ Z)
    (hZorder : IsOrderClosed
      (Z : Set C(BooleanStone (RegularOpen (SolovayProduct Gamma)), ℝ))) :
    Z = ⊤ := by
  let B := RegularOpen (SolovayProduct Gamma)
  have hOne : (1 : C(BooleanStone B, ℝ)) ∈ Z := by
    apply hYZ
    apply solovayVectorGenerator_mem Gamma
    exact Or.inr (Set.mem_singleton _)
  let L : BooleanSubalgebra B :=
    booleanSubalgebraInVectorSublattice B Z hOne
  have hLcomplete : IsCompleteBooleanSubalgebra L :=
    booleanSubalgebraInVectorSublattice_complete B Z hOne hZorder
  have hLgen : ∀ m n, solovayB Gamma m n ∈ L := by
    intro m n
    change booleanStoneIndicator B (solovayB Gamma m n) ∈ Z
    apply hYZ
    apply solovayVectorGenerator_mem Gamma
    exact Or.inl ⟨(m, n), rfl⟩
  have hLtop : L = ⊤ :=
    solovay_generates_regularOpen Gamma L hLcomplete hLgen
  have hAllIndicators : ∀ b : B, booleanStoneIndicator B b ∈ Z := by
    intro b
    change b ∈ L
    rw [hLtop]
    trivial
  exact vectorSublattice_eq_top_of_booleanStoneIndicators B Z hOne
    hAllIndicators hZorder
end OrderClosures
