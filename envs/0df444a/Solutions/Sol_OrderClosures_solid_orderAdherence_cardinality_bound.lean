-- Prove2me | solution 1 for OrderClosures.solid_orderAdherence_cardinality_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:15:37.938057+00:00
-- url     : https://prove2.me/submissions/c9ba906f-544e-4904-97f1-0bf41d6a1169

module
public import Mathlib.Data.Fintype.Order
public import Definitions.Def_LeanPool_OrderClosures_Solovay
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungCharacterization
public import Mathlib.Order.TransfiniteIteration
public import Mathlib.SetTheory.Ordinal.CantorNormalForm
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Counterexample
public import Theorems.Thm_OrderClosures_signedPositiveSubsetSuprema_isOrderClosed
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
public import Theorems.Thm_OrderClosures_orderAdherence_mono
public import Theorems.Thm_Positive_extension_apply
public import Theorems.Thm_VectorSublattice_coe_toSubmodule
public import Theorems.Thm_VectorSublattice_mem_bot
public import Theorems.Thm_VectorSublattice_mem_top
public import Theorems.Thm_coe_toCompletionVecLatHom
public import Theorems.Thm_negPart_le_abs
public import Theorems.Thm_posPart_le_abs
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
    Cardinal.mk (orderAdherence S) ≤ (2 : Cardinal) ^ Cardinal.mk S := by
  let E := signedPositiveSubsetSuprema S
  have hSE : S ⊆ E := by
    intro s hs
    constructor
    · refine ⟨{s⁺}, ?_, isLUB_singleton⟩
      rintro a rfl
      have hspos : |s⁺| ≤ |s| := by
        rw [abs_of_nonneg (posPart_nonneg s)]
        exact posPart_le_abs s
      exact ⟨hS hs hspos, posPart_nonneg s⟩
    · refine ⟨{s⁻}, ?_, isLUB_singleton⟩
      rintro a rfl
      have hsneg : |s⁻| ≤ |s| := by
        rw [abs_of_nonneg (negPart_nonneg s)]
        exact negPart_le_abs s
      exact ⟨hS hs hsneg, negPart_nonneg s⟩
  have hadhE : orderAdherence S ⊆ E := fun _ hx ↦
    signedPositiveSubsetSuprema_isOrderClosed hS (orderAdherence_mono hSE hx)
  let Aplus : E → Set X := fun x ↦ Classical.choose x.2.1
  let Aminus : E → Set X := fun x ↦ Classical.choose x.2.2
  have hAplus : ∀ x : E,
      Aplus x ⊆ S ∩ Ici 0 ∧ IsLUB (Aplus x) x.1⁺ := fun x ↦
    Classical.choose_spec x.2.1
  have hAminus : ∀ x : E,
      Aminus x ⊆ S ∩ Ici 0 ∧ IsLUB (Aminus x) x.1⁻ := fun x ↦
    Classical.choose_spec x.2.2
  let Ψ : E → Set S := fun x ↦
    {s | s.1 ∈ Aplus x ∨ -s.1 ∈ Aminus x}
  have hΨ : Function.Injective Ψ := by
    intro x y hxy
    have hplus_le : x.1⁺ ≤ y.1⁺ := (hAplus x).2.2 fun a ha ↦ by
      by_cases ha0 : a = 0
      · simp [ha0]
      · have haS : a ∈ S := ((hAplus x).1 ha).1
        have haΨx : (⟨a, haS⟩ : S) ∈ Ψ x := Or.inl ha
        have haΨy : (⟨a, haS⟩ : S) ∈ Ψ y := by
          rw [← hxy]
          exact haΨx
        rcases haΨy with hay | hnega
        · exact (hAplus y).2.1 hay
        · have hnega0 : 0 ≤ -a := ((hAminus y).1 hnega).2
          have : a = 0 := le_antisymm (by simpa using hnega0) ((hAplus x).1 ha).2
          exact (ha0 this).elim
    have hplus_ge : y.1⁺ ≤ x.1⁺ := (hAplus y).2.2 fun a ha ↦ by
      by_cases ha0 : a = 0
      · simp [ha0]
      · have haS : a ∈ S := ((hAplus y).1 ha).1
        have haΨy : (⟨a, haS⟩ : S) ∈ Ψ y := Or.inl ha
        have haΨx : (⟨a, haS⟩ : S) ∈ Ψ x := by
          rw [hxy]
          exact haΨy
        rcases haΨx with hax | hnega
        · exact (hAplus x).2.1 hax
        · have hnega0 : 0 ≤ -a := ((hAminus x).1 hnega).2
          have : a = 0 := le_antisymm (by simpa using hnega0) ((hAplus y).1 ha).2
          exact (ha0 this).elim
    have hminus_le : x.1⁻ ≤ y.1⁻ := (hAminus x).2.2 fun a ha ↦ by
      by_cases ha0 : a = 0
      · simp [ha0]
      · have haS : a ∈ S := ((hAminus x).1 ha).1
        have hnegS : -a ∈ S := hS haS (by simp)
        have haΨx : (⟨-a, hnegS⟩ : S) ∈ Ψ x := by
          right
          simpa using ha
        have haΨy : (⟨-a, hnegS⟩ : S) ∈ Ψ y := by
          rw [← hxy]
          exact haΨx
        rcases haΨy with hnega | hay
        · have hnega0 : 0 ≤ -a := ((hAplus y).1 hnega).2
          have : a = 0 := le_antisymm (by simpa using hnega0) ((hAminus x).1 ha).2
          exact (ha0 this).elim
        · exact (hAminus y).2.1 (by simpa using hay)
    have hminus_ge : y.1⁻ ≤ x.1⁻ := (hAminus y).2.2 fun a ha ↦ by
      by_cases ha0 : a = 0
      · simp [ha0]
      · have haS : a ∈ S := ((hAminus y).1 ha).1
        have hnegS : -a ∈ S := hS haS (by simp)
        have haΨy : (⟨-a, hnegS⟩ : S) ∈ Ψ y := by
          right
          simpa using ha
        have haΨx : (⟨-a, hnegS⟩ : S) ∈ Ψ x := by
          rw [hxy]
          exact haΨy
        rcases haΨx with hnega | hax
        · have hnega0 : 0 ≤ -a := ((hAplus x).1 hnega).2
          have : a = 0 := le_antisymm (by simpa using hnega0) ((hAminus y).1 ha).2
          exact (ha0 this).elim
        · exact (hAminus x).2.1 (by simpa using hax)
    apply Subtype.ext
    calc
      x.1 = x.1⁺ - x.1⁻ := (posPart_sub_negPart x.1).symm
      _ = y.1⁺ - y.1⁻ := by
        rw [le_antisymm hplus_le hplus_ge, le_antisymm hminus_le hminus_ge]
      _ = y.1 := posPart_sub_negPart y.1
  let θ : orderAdherence S → E := fun x ↦ ⟨x.1, hadhE x.2⟩
  have hθ : Function.Injective θ := fun x y hxy ↦ by
    apply Subtype.ext
    dsimp [θ] at hxy
    exact congrArg (fun z : E ↦ z.1) hxy
  calc
    Cardinal.mk (orderAdherence S) ≤ Cardinal.mk E := Cardinal.mk_le_of_injective hθ
    _ ≤ Cardinal.mk (Set S) := Cardinal.mk_le_of_injective hΨ
    _ = (2 : Cardinal) ^ Cardinal.mk S := Cardinal.mk_set
end OrderClosures
