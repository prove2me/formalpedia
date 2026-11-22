-- Prove2me | solution 1 for OrderClosures.booleanSubalgebraInVectorSublattice_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:08:37.574211+00:00
-- url     : https://prove2.me/submissions/f1a163d3-18e9-4f34-9251-923122406e84

module
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
public import Mathlib.Order.Heyting.Regular
public import Mathlib.Order.BooleanSubalgebra
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Topology.Category.Stonean.Basic
public import Mathlib.Order.PrimeSeparator
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Definitions.Def_LeanPool_OrderClosures_Solovay
public import Theorems.Thm_OrderClosures_booleanStoneClopen_sSup
public import Theorems.Thm_OrderClosures_booleanStoneIndicator_mono
public import Theorems.Thm_OrderClosures_booleanStoneIndicator_nonneg
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
public import Theorems.Thm_Positive_continuous
public import Theorems.Thm_Positive_extension_apply
public import Theorems.Thm_VectorSublattice_coe_toSubmodule
public import Theorems.Thm_VectorSublattice_mem_bot
public import Theorems.Thm_VectorSublattice_mem_top
public import Theorems.Thm_coe_toCompletionVecLatHom
public import Theorems.Thm_orderConvergesTo_of_monotone_isLUB
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
open Set
noncomputable section
open OrderClosures
universe u
variable (B : Type u) [CompleteBooleanAlgebra B]
namespace OrderClosures
theorem _root_.solution
    (Z : VectorSublattice C(BooleanStone B, ℝ))
    (hOne : (1 : C(BooleanStone B, ℝ)) ∈ Z)
    (hZclosed : IsOrderClosed (Z : Set C(BooleanStone B, ℝ))) :
    IsCompleteBooleanSubalgebra
      (booleanSubalgebraInVectorSublattice B Z hOne) := by
  intro S hS
  by_cases hSne : S.Nonempty
  · classical
    let I := {F : Finset S // F.Nonempty}
    let b₀ : S := ⟨hSne.some, hSne.some_mem⟩
    let F₀ : I := ⟨{b₀}, Finset.singleton_nonempty b₀⟩
    let : Nonempty I := ⟨F₀⟩
    let : IsDirected I (· ≤ ·) := ⟨fun F G ↦
      ⟨⟨F.1 ∪ G.1, F.2.mono Finset.subset_union_left⟩,
        Finset.subset_union_left, Finset.subset_union_right⟩⟩
    let u : I → C(BooleanStone B, ℝ) := fun F ↦
      F.1.sup' F.2 (fun b ↦ booleanStoneIndicator B b.1)
    have huZ : ∀ F, u F ∈ Z := by
      intro F
      apply Finset.sup'_mem (Z : Set C(BooleanStone B, ℝ))
        (fun _ hx _ hy ↦ Z.sup_mem hx hy) F.1 F.2
      intro b hb
      exact hS b.2
    have humono : Monotone u := by
      intro F G hFG
      change F.1.sup' F.2 (fun b ↦ booleanStoneIndicator B b.1) ≤
        G.1.sup' G.2 (fun b ↦ booleanStoneIndicator B b.1)
      exact Finset.sup'_mono
        (f := fun b : S ↦ booleanStoneIndicator B b.1)
        (s₁ := F.1) (s₂ := G.1) hFG F.2
    have hlub : IsLUB (Set.range u) (booleanStoneIndicator B (sSup S)) := by
      constructor
      · rintro _ ⟨F, rfl⟩
        apply Finset.sup'_le
        intro b hb
        exact booleanStoneIndicator_mono B (le_sSup b.2)
      · intro k hk
        have hkzero : (0 : C(BooleanStone B, ℝ)) ≤ k := by
          have hF₀k : u F₀ ≤ k := hk ⟨F₀, rfl⟩
          exact (booleanStoneIndicator_nonneg B b₀.1).trans (by
            simpa [u, F₀] using hF₀k)
        intro x
        by_cases hxs : x ∈ booleanStoneClopen B (sSup S)
        · have hxclosure : x ∈ closure
              (⋃ b ∈ S, booleanStoneClopen B b) := by
            rwa [← booleanStoneClopen_sSup]
          have hclosed : IsClosed {y : BooleanStone B | (1 : ℝ) ≤ k y} :=
            isClosed_le continuous_const k.continuous
          have hunion : (⋃ b ∈ S, booleanStoneClopen B b) ⊆
              {y : BooleanStone B | (1 : ℝ) ≤ k y} := by
            intro y hy
            simp only [Set.mem_iUnion] at hy
            rcases hy with ⟨b, hbS, hyb⟩
            let bs : S := ⟨b, hbS⟩
            let Fs : I := ⟨{bs}, Finset.singleton_nonempty bs⟩
            have hbind : booleanStoneIndicator B b ≤ k := by
              have hk' := hk ⟨Fs, rfl⟩
              simpa [u, Fs, bs] using hk'
            have := hbind y
            simpa [booleanStoneIndicator, hyb] using this
          have hxone : (1 : ℝ) ≤ k x :=
            closure_minimal hunion hclosed hxclosure
          simpa [booleanStoneIndicator, hxs] using hxone
        · have hxzero := hkzero x
          simpa [booleanStoneIndicator, hxs] using hxzero
    have hconv : OrderConvergesTo u (booleanStoneIndicator B (sSup S)) :=
      orderConvergesTo_of_monotone_isLUB humono hlub
    apply hZclosed
    exact ⟨I, inferInstance, inferInstance, inferInstance, u, huZ, hconv⟩
  · have hSempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hSne
    subst S
    simp
end OrderClosures
