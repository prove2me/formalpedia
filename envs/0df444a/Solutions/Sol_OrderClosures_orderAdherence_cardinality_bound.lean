-- Prove2me | solution 1 for OrderClosures.orderAdherence_cardinality_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:15:18.849813+00:00
-- url     : https://prove2.me/submissions/16a63012-6970-41f9-84e0-4c5fb8aac46b

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
public import Theorems.Thm_OrderConvergesTo_abs
public import Theorems.Thm_OrderConvergesTo_le_of_forall_le
public import Theorems.Thm_OrderConvergesTo_sub
public import Theorems.Thm_Positive_extension_apply
public import Theorems.Thm_VectorSublattice_coe_toSubmodule
public import Theorems.Thm_VectorSublattice_mem_bot
public import Theorems.Thm_VectorSublattice_mem_top
public import Theorems.Thm_abs_eq_zero_iff_zero
public import Theorems.Thm_coe_toCompletionVecLatHom
public import Theorems.Thm_orderConvergesTo_const
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
     (D : Set X) :
    Cardinal.mk (orderAdherence D) ≤
      (2 : Cardinal) ^ ((2 : Cardinal) ^ Cardinal.mk D) := by
  let Φ : orderAdherence D → Set (Set D) := fun x ↦
    {A | x.1 ∈ orderAdherence ((fun z : D ↦ z.1) '' A)}
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    apply Subtype.ext
    by_contra hne
    rcases x.2 with ⟨ι, hpre, hdir, hnon, f, hfD, hfx⟩
    let : Preorder ι := hpre
    let : IsDirected ι (· ≤ ·) := hdir
    let : Nonempty ι := hnon
    rcases hfx with ⟨κ, hκpre, hκdir, hκnon, r, hranti, hrnonneg, hrglb, hbound⟩
    let : Preorder κ := hκpre
    let : IsDirected κ (· ≤ ·) := hκdir
    let : Nonempty κ := hκnon
    have hk : ∃ k, ¬ |x.1 - y.1| ≤ r k := by
      by_contra hk
      push Not at hk
      have hlower : |x.1 - y.1| ∈ lowerBounds (Set.range r) := by
        rintro _ ⟨k, rfl⟩
        exact hk k
      have habs : |x.1 - y.1| = 0 :=
        le_antisymm (hrglb.2 hlower) (abs_nonneg _)
      exact hne (sub_eq_zero.mp ((abs_eq_zero_iff_zero _).mp habs))
    obtain ⟨k, hk⟩ := hk
    obtain ⟨i₀, hi₀⟩ := Filter.eventually_atTop.mp (hbound k)
    let fD : ι → D := fun i ↦ ⟨f i, hfD i⟩
    let A : Set D := Set.range (fun i : Set.Ici i₀ ↦ fD i.1)
    have hIci : DirectedOn (· ≤ ·) (Set.Ici i₀) := by
      intro a ha b hb
      obtain ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a b
      exact ⟨c, ha.trans hac, hac, hbc⟩
    let : IsDirectedOrder (Set.Ici i₀) := hIci.isDirectedOrder
    let : Nonempty (Set.Ici i₀) := ⟨⟨i₀, le_rfl⟩⟩
    have hrestrict : OrderConvergesTo (fun i : Set.Ici i₀ ↦ f i.1) x.1 := by
      refine ⟨κ, inferInstance, inferInstance, inferInstance, r, hranti, hrnonneg,
        hrglb, ?_⟩
      intro l
      obtain ⟨i₁, hi₁⟩ := Filter.eventually_atTop.mp (hbound l)
      obtain ⟨m, hi₀m, hi₁m⟩ := directed_of (· ≤ ·) i₀ i₁
      apply Filter.eventually_atTop.mpr
      refine ⟨⟨m, hi₀m⟩, ?_⟩
      intro j hj
      exact hi₁ j.1 (hi₁m.trans hj)
    have hxA : x.1 ∈ orderAdherence ((fun z : D ↦ z.1) '' A) := by
      refine ⟨Set.Ici i₀, inferInstance, inferInstance, inferInstance,
        fun i ↦ f i.1, ?_, hrestrict⟩
      intro i
      exact ⟨fD i.1, ⟨i, rfl⟩, rfl⟩
    have hxA' : A ∈ Φ x := hxA
    have hyA' : A ∈ Φ y := by
      rw [← hxy]
      exact hxA'
    change y.1 ∈ orderAdherence ((fun z : D ↦ z.1) '' A) at hyA'
    rcases hyA' with ⟨τ, hτpre, hτdir, hτnon, a, haA, hay⟩
    let : Preorder τ := hτpre
    let : IsDirected τ (· ≤ ·) := hτdir
    let : Nonempty τ := hτnon
    have habound : ∀ j, |a j - x.1| ≤ r k := by
      intro j
      rcases haA j with ⟨z, ⟨i, rfl⟩, hza⟩
      rw [← hza]
      exact hi₀ i.1 i.2
    have hybound : |y.1 - x.1| ≤ r k :=
      (hay.sub (orderConvergesTo_const x.1)).abs.le_of_forall_le habound
    exact hk (by simpa [abs_sub_comm] using hybound)
  calc
    Cardinal.mk (orderAdherence D) ≤ Cardinal.mk (Set (Set D)) :=
      Cardinal.mk_le_of_injective hΦ
    _ = (2 : Cardinal) ^ ((2 : Cardinal) ^ Cardinal.mk D) := by
      rw [Cardinal.mk_set, Cardinal.mk_set]
end OrderClosures
