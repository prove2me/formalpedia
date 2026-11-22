-- Prove2me | solution 1 for OrderClosures.positiveSubsetSuprema_isOrderClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:07:40.567661+00:00
-- url     : https://prove2.me/submissions/f952115a-9dfd-4b2d-bdc8-9208813c0398

module
public import Mathlib.Data.Fintype.Order
public import Definitions.Def_LeanPool_OrderClosures_Solovay
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungCharacterization
public import Mathlib.Order.TransfiniteIteration
public import Mathlib.SetTheory.Ordinal.CantorNormalForm
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Counterexample
public import Theorems.Thm_ClosedOrderIdeal_inf_toSubmodule
public import Theorems.Thm_ClosedOrderIdeal_mem_sInf
public import Theorems.Thm_ClosedOrderIdeal_sup_toSubmodule
public import Theorems.Thm_LLexpr_NormalForm_eval_add
public import Theorems.Thm_LLexpr_NormalForm_eval_inf
public import Theorems.Thm_LLexpr_NormalForm_eval_negate
public import Theorems.Thm_LLexpr_NormalForm_eval_smul
public import Theorems.Thm_LLexpr_NormalForm_eval_sup
public import Theorems.Thm_LLexpr_NormalForm_eval_var
public import Theorems.Thm_LLexpr_NormalForm_eval_zero
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_add
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_singleton
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_smul
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_sup
public import Theorems.Thm_LLexpr_eval_add
public import Theorems.Thm_LLexpr_eval_inf
public import Theorems.Thm_LLexpr_eval_reindexExpr
public import Theorems.Thm_LLexpr_eval_smul
public import Theorems.Thm_LLexpr_eval_sup
public import Theorems.Thm_LLexpr_eval_var
public import Theorems.Thm_LLexpr_eval_zero
public import Theorems.Thm_LLexpr_normalize_eval
public import Theorems.Thm_OrderConvergesTo_nonneg
public import Theorems.Thm_Positive_extension_apply
public import Theorems.Thm_VectorSublattice_coe_toSubmodule
public import Theorems.Thm_VectorSublattice_mem_bot
public import Theorems.Thm_VectorSublattice_mem_top
public import Theorems.Thm_coe_toCompletionVecLatHom
public import Theorems.Thm_sub_inf_eq_posPart
attribute [local simp] ClosedOrderIdeal.inf_toSubmodule
attribute [local simp] ClosedOrderIdeal.mem_sInf
attribute [local simp] ClosedOrderIdeal.sup_toSubmodule
attribute [local simp] LLexpr.NormalForm.eval_add
attribute [local simp] LLexpr.NormalForm.eval_inf
attribute [local simp] LLexpr.NormalForm.eval_negate
attribute [local simp] LLexpr.NormalForm.eval_smul
attribute [local simp] LLexpr.NormalForm.eval_sup
attribute [local simp] LLexpr.NormalForm.eval_var
attribute [local simp] LLexpr.NormalForm.eval_zero
attribute [local simp] LLexpr.SupLinearCombination.eval_add
attribute [local simp] LLexpr.SupLinearCombination.eval_singleton
attribute [local simp] LLexpr.SupLinearCombination.eval_smul
attribute [local simp] LLexpr.SupLinearCombination.eval_sup
attribute [local simp] LLexpr.eval_add
attribute [local simp] LLexpr.eval_inf
attribute [local simp] LLexpr.eval_reindexExpr
attribute [local simp] LLexpr.eval_smul
attribute [local simp] LLexpr.eval_sup
attribute [local simp] LLexpr.eval_var
attribute [local simp] LLexpr.eval_zero
attribute [local simp] LLexpr.normalize_eval
attribute [local simp] Positive.extension_apply
attribute [local simp] VectorSublattice.coe_toSubmodule
attribute [local simp] VectorSublattice.mem_bot
attribute [local simp] VectorSublattice.mem_top
attribute [local simp] coe_toCompletionVecLatHom



set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v
namespace OrderClosures
theorem _root_.solution
    {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
     {S : Set X} (hS : LatticeOrderedAddCommGroup.IsSolid S) :
    IsOrderClosed (positiveSubsetSuprema S) := by
  have hnonneg : ∀ {z : X}, z ∈ positiveSubsetSuprema S → 0 ≤ z := by
    intro z hz
    rcases hz with ⟨A, hAS, hAlub⟩
    by_cases hA : A.Nonempty
    · obtain ⟨a, ha⟩ := hA
      exact (hAS ha).2.trans (hAlub.1 ha)
    · have hupper : z ≤ z + z := hAlub.2 fun a ha ↦ (hA ⟨a, ha⟩).elim
      exact nonneg_of_le_add_right hupper
  have hdown : ∀ {y z : X}, 0 ≤ y → y ≤ z →
      z ∈ positiveSubsetSuprema S → y ∈ positiveSubsetSuprema S := by
    intro y z hy0 hyz hz
    rcases hz with ⟨A, hAS, hAlub⟩
    let B : Set X := (fun a ↦ a ⊓ y) '' A
    refine ⟨B, ?_, ?_⟩
    · rintro b ⟨a, ha, rfl⟩
      have ha0 : 0 ≤ a := (hAS ha).2
      have hab0 : 0 ≤ a ⊓ y := le_inf ha0 hy0
      have habs : |a ⊓ y| ≤ |a| := by
        simp [abs_of_nonneg hab0, abs_of_nonneg ha0]
      exact ⟨hS (hAS ha).1 habs, hab0⟩
    · constructor
      · rintro b ⟨a, ha, rfl⟩
        exact inf_le_right
      · intro w hw
        have hupperA : z + w - y ∈ upperBounds A := by
          intro a ha
          have haz : a ≤ z := hAlub.1 ha
          have haw : a ⊓ y ≤ w := hw ⟨a, ha, rfl⟩
          change a ≤ z + w - y
          calc
            a = (a - a ⊓ y) + (a ⊓ y) := by abel
            _ ≤ (z - y) + w := add_le_add (by
              rw [sub_inf_eq_posPart]
              exact (posPart_mono (sub_le_sub_right haz y)).trans_eq
                (posPart_of_nonneg (sub_nonneg.mpr hyz))) haw
            _ = z + w - y := by abel
        have hzw := hAlub.2 hupperA
        change y ≤ w
        apply sub_nonpos.mp
        have hcancel := sub_le_sub_left hzw z
        convert hcancel using 1 <;> abel
  intro x
  rintro ⟨ι, hpre, hdir, hne, f, hf, hfx⟩
  let : Preorder ι := hpre
  let : IsDirected ι (· ≤ ·) := hdir
  let : Nonempty ι := hne
  have hf0 : ∀ i, 0 ≤ f i := fun i ↦ hnonneg (hf i)
  have hx0 : 0 ≤ x := hfx.nonneg hf0
  rcases hfx with ⟨κ, hκpre, hκdir, hκne, r, hranti, hrnonneg, hrglb, hbound⟩
  let : Preorder κ := hκpre
  let : IsDirected κ (· ≤ ·) := hκdir
  let : Nonempty κ := hκne
  let y : κ → X := fun k ↦ (x - r k)⁺
  have hy_lub : IsLUB (Set.range y) x := by
    constructor
    · rintro _ ⟨k, rfl⟩
      exact show (x - r k) ⊔ 0 ≤ x from
        sup_le (sub_le_self _ (hrnonneg k)) hx0
    · intro c hc
      have hlow : x - c ∈ lowerBounds (Set.range r) := by
        rintro _ ⟨k, rfl⟩
        have hraw : x - r k ≤ c := (le_posPart _).trans (hc ⟨k, rfl⟩)
        exact sub_le_iff_le_add.mpr (by
          simpa [add_comm] using (sub_le_iff_le_add.mp hraw))
      exact sub_nonpos.mp (hrglb.2 hlow)
  have hy : ∀ k, y k ∈ positiveSubsetSuprema S := by
    intro k
    obtain ⟨i, hi⟩ := (hbound k).exists
    have hyfi : y k ≤ f i := by
      dsimp [y]
      have hi' : |x - f i| ≤ r k := by simpa [abs_sub_comm] using hi
      have hsub : x - f i ≤ r k := (le_abs_self _).trans hi'
      have hraw : x - r k ≤ f i := sub_le_iff_le_add.mpr (by
        simpa [add_comm] using (sub_le_iff_le_add.mp hsub))
      exact sup_le hraw (hf0 i)
    exact hdown (posPart_nonneg _) hyfi (hf i)
  choose A hAS hAlub using hy
  let B : Set X := {a | ∃ k, a ∈ A k}
  refine ⟨B, ?_, ?_⟩
  · rintro a ⟨k, ha⟩
    exact hAS k ha
  · constructor
    · rintro a ⟨k, ha⟩
      exact (hAlub k).1 ha |>.trans (hy_lub.1 ⟨k, rfl⟩)
    · intro c hc
      apply hy_lub.2
      rintro _ ⟨k, rfl⟩
      exact (hAlub k).2 fun a ha ↦ hc ⟨k, ha⟩
end OrderClosures
