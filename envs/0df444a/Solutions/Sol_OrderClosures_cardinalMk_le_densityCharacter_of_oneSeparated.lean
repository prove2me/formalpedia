-- Prove2me | solution 1 for OrderClosures.cardinalMk_le_densityCharacter_of_oneSeparated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:07:19.452723+00:00
-- url     : https://prove2.me/submissions/156b0c77-59cc-42f2-b53f-02fa5364c699

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
namespace OrderClosures
theorem _root_.solution
    {A : Type u} {X : Type u} [PseudoMetricSpace X]
    (e : A → X) (hsep : ∀ a b, a ≠ b → (1 : ℝ) ≤ dist (e a) (e b)) :
    Cardinal.mk A ≤ densityCharacter X := by
  unfold densityCharacter
  apply le_csInf
  · exact ⟨Cardinal.mk (Set.univ : Set X), Set.univ, dense_univ, rfl⟩
  · intro c hc
    rcases hc with ⟨D, hDdense, rfl⟩
    have hthird : (0 : ℝ) < 1 / 3 := by norm_num
    choose d hdD hdclose using fun a ↦ hDdense.exists_dist_lt (e a) hthird
    let φ : A → D := fun a ↦ ⟨d a, hdD a⟩
    apply Cardinal.mk_le_of_injective (f := φ)
    intro a b hab
    by_contra hne
    have hval : d a = d b := congrArg Subtype.val hab
    have hone : (1 : ℝ) ≤ dist (e a) (e b) := hsep a b hne
    have hlt : dist (e a) (e b) < 1 := by
      calc
        dist (e a) (e b) ≤ dist (e a) (d a) + dist (d a) (e b) :=
          dist_triangle _ _ _
        _ = dist (e a) (d a) + dist (e b) (d b) := by
          rw [hval, dist_comm (d b) (e b)]
        _ < 1 / 3 + 1 / 3 := add_lt_add (hdclose a) (hdclose b)
        _ < 1 := by norm_num
    exact (not_lt_of_ge hone) hlt
end OrderClosures
