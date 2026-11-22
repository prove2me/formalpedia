-- Prove2me | solution 1 for TwoBQO.dom_twoBQO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:43:06.261119+00:00
-- url     : https://prove2.me/submissions/4583f40d-4c6c-4b93-b102-d6b777c693d1

module
public import Mathlib.SetTheory.Ordinal.Basic
public import Definitions.Def_LeanPool_NashWilliams_Order_WellQuasiOrder_Regular
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Ramsey_Infinite
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_NashWilliams_Order_TwoBQO
public import Theorems.Thm_TwoBQO_iff_noBad
section
@[expose] public section
open Set Preorder
noncomputable section
namespace PairSeq
end PairSeq
variable {ι : Type*} (r : ι → ι → Prop) (s : ι → Type*) (t : ∀ i, s i → s i → Prop)
private theorem badSeq_dom_to_pairSeq {α : Type*} {r : α → α → Prop} (f : ℕ → Set α)
    (hbad : ∀ m n, m < n → ¬ DomOrder r (f m) (f n)) :
    ∃ f_ : PairSeq α, (∀ m n (hmn : m < n), f_ m n hmn ∈ f m) ∧ PairSeq.IsBad r f_ := by
  have hex : ∀ m n, m < n → ∃ x, x ∈ f m ∧ ∀ y ∈ f n, ¬ r x y := by
    intro m n hmn
    have h := hbad m n hmn
    unfold DomOrder at h
    push Not at h
    exact h
  let g : ∀ m n, m < n → α := fun m n hmn => Classical.choose (hex m n hmn)
  have hg_mem : ∀ m n (hmn : m < n), g m n hmn ∈ f m :=
    fun m n hmn => (Classical.choose_spec (hex m n hmn)).1
  have hg_bad : ∀ m n (hmn : m < n), ∀ y ∈ f n, ¬ r (g m n hmn) y :=
    fun m n hmn => (Classical.choose_spec (hex m n hmn)).2
  refine ⟨g, hg_mem, ?_⟩
  intro m n l hmn hnl
  exact hg_bad m n hmn (g n l hnl) (hg_mem n l hnl)
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Set Preorder
noncomputable section
variable {ι : Type*} (r : ι → ι → Prop) (s : ι → Type*) (t : ∀ i, s i → s i → Prop)
namespace TwoBQO
theorem _root_.solution {α : Type*} {r : α → α → Prop} (hr : TwoBQO r) :
    WellQuasiOrdered (DomOrder r) := by
  intro g
  by_contra hcon
  push Not at hcon
  obtain ⟨f_, _, hf_bad⟩ := badSeq_dom_to_pairSeq g hcon
  rw [TwoBQO.iff_noBad] at hr
  exact hr ⟨f_, hf_bad⟩
end TwoBQO
