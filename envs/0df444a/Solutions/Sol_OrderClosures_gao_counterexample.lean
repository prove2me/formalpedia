-- Prove2me | solution 1 for OrderClosures.gao_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:16:25.838431+00:00
-- url     : https://prove2.me/submissions/6cec4b83-72ad-4417-a543-667fc78e4817

module
public import Mathlib.Data.Fintype.Order
public import Definitions.Def_LeanPool_OrderClosures_Solovay
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungCharacterization
public import Mathlib.Order.TransfiniteIteration
public import Mathlib.SetTheory.Ordinal.CantorNormalForm
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Counterexample
public import Theorems.Thm_OrderClosures_cardinalMk_le_densityCharacter_booleanStoneContinuousMap
public import Theorems.Thm_OrderClosures_isClosed_solovayVectorSublattice
public import Theorems.Thm_OrderClosures_isOrderComplete_continuousMap
public import Theorems.Thm_OrderClosures_isSeparable_solovayVectorSublattice
public import Theorems.Thm_OrderClosures_solovayA_injective
public import Theorems.Thm_OrderClosures_solovayVectorSublattice_maximalOrderClosed


set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v
namespace OrderClosures
theorem _root_.solution (κ : Cardinal.{u}) :
    ∃ (K : Type u) (_ : TopologicalSpace K) (_ : CompactSpace K) (_ : T2Space K),
      IsOrderComplete C(K, ℝ) ∧ κ ≤ densityCharacter C(K, ℝ) ∧
      ∃ Y : VectorSublattice C(K, ℝ),
        IsClosed (Y : Set C(K, ℝ)) ∧
          TopologicalSpace.IsSeparable (Y : Set C(K, ℝ)) ∧
          ∀ Z : VectorSublattice C(K, ℝ),
            Y ≤ Z → IsOrderClosed (Z : Set C(K, ℝ)) → Z = ⊤ := by
  induction κ using Cardinal.inductionOn with
  | _ Gamma =>
    classical
    obtain ⟨lin, wf⟩ := exists_wellFoundedLT Gamma
    let : LinearOrder Gamma := lin
    let : WellFoundedLT Gamma := wf
    let : TopologicalSpace Gamma := ⊥
    let : DiscreteTopology Gamma := ⟨rfl⟩
    let B := RegularOpen (SolovayProduct Gamma)
    let K := BooleanStone B
    refine ⟨K, inferInstance, inferInstance, inferInstance,
      isOrderComplete_continuousMap K, ?_,
      solovayVectorSublattice Gamma,
      isClosed_solovayVectorSublattice Gamma,
      isSeparable_solovayVectorSublattice Gamma, ?_⟩
    · calc
        Cardinal.mk Gamma ≤ Cardinal.mk B :=
          Cardinal.mk_le_of_injective (solovayA_injective Gamma 0)
        _ ≤ densityCharacter C(K, ℝ) :=
          cardinalMk_le_densityCharacter_booleanStoneContinuousMap B
    · intro Z hYZ hZorder
      exact solovayVectorSublattice_maximalOrderClosed Gamma Z hYZ hZorder
end OrderClosures
