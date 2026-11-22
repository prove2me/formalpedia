-- Prove2me | solution 1 for OrderClosures.ordinalProjection_incomparable_iInf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:12:57.806077+00:00
-- url     : https://prove2.me/submissions/f4c35744-f8d0-44ed-8755-c1ccad29e59a

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
public import Theorems.Thm_OrderClosures_continuousMap_exists_finite_coordinates
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
public import Theorems.Thm_OrderClosures_CNFListLT_trans
public import Theorems.Thm_OrderClosures_CNFStep_trans
public import Theorems.Thm_OrderClosures_cnfExtensionLE_partialOrder_and_subrelation
public import Theorems.Thm_OrderClosures_cnfExtensionLT_linear_above
public import Theorems.Thm_Positive_extension_apply
public import Theorems.Thm_VectorSublattice_coe_toSubmodule
public import Theorems.Thm_VectorSublattice_mem_bot
public import Theorems.Thm_VectorSublattice_mem_top
public import Theorems.Thm_coe_toCompletionVecLatHom
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
    (ξ : Ordinal.{u}) (Z : Set (GaoIndex ξ)) (hZ : Z.Infinite)
    (hinc : Z.Pairwise fun ζ ζ' ↦ ¬ cnfExtensionLE ζ.1 ζ'.1) :
    IsGLB (ordinalProjection ξ '' Z) 0 := by
  classical
  constructor
  · rintro p ⟨ζ, _, rfl⟩ x
    simp only [ordinalProjection]
    split_ifs <;> norm_num
  · intro f hf x
    by_contra hfx
    have hfxpos : 0 < f x := lt_of_not_ge hfx
    obtain ⟨F, hF⟩ := continuousMap_exists_finite_coordinates f x
      isOpen_Ioi hfxpos
    let bad : Set (GaoIndex ξ) := ⋃ i ∈ (F : Set (GaoIndex ξ)),
      {ζ | ζ ∈ Z ∧ x.1 i = true ∧ cnfExtensionLE i.1 ζ.1}
    have hbad : bad.Finite := by
      apply F.finite_toSet.biUnion
      intro i _
      apply Set.Subsingleton.finite
      intro ζ hζ ζ' hζ'
      rcases hζ with ⟨hζZ, _, hiζ⟩
      rcases hζ' with ⟨hζ'Z, _, hiζ'⟩
      by_contra hne
      have hnot := hinc hζZ hζ'Z hne
      rcases hiζ with hiζ | hiζ
      · have : i = ζ := Subtype.ext hiζ
        subst i
        exact hnot hiζ'
      rcases hiζ' with hiζ' | hiζ'
      · have : i = ζ' := Subtype.ext hiζ'
        subst i
        exact (hinc hζ'Z hζZ (Ne.symm hne)) (Or.inr hiζ)
      · rcases lt_trichotomy ζ.1 ζ'.1 with hlt | heq | hgt
        · exact hnot (Or.inr
            ((cnfExtensionLT_linear_above i.1 hiζ hiζ').mpr hlt))
        · exact hne (Subtype.ext heq)
        · exact (hinc hζ'Z hζZ (Ne.symm hne))
            (Or.inr ((cnfExtensionLT_linear_above i.1 hiζ' hiζ).mpr hgt))
    obtain ⟨ζ, hζZ, hζbad⟩ := hZ.exists_notMem_finite hbad
    let y : GaoIndex ξ → Bool := fun a ↦
      if cnfExtensionLE a.1 ζ.1 then false else x.1 a
    have hy_mono : ∀ a b : GaoIndex ξ,
        cnfExtensionLT a.1 b.1 → y a ≤ y b := by
      intro a b hab
      dsimp [y]
      by_cases ha : cnfExtensionLE a.1 ζ.1
      · rw [if_pos ha]
        exact Bool.false_le _
      · rw [if_neg ha]
        by_cases hb : cnfExtensionLE b.1 ζ.1
        · exact (ha (cnfExtensionLE_partialOrder_and_subrelation.1.trans
            a.1 b.1 ζ.1 (Or.inr hab) hb)).elim
        · rw [if_neg hb]
          exact x.2 a b hab
    let yK : GaoCompactSpace ξ := ⟨y, hy_mono⟩
    have hyF : ∀ i ∈ F, yK.1 i = x.1 i := by
      intro i hi
      dsimp [yK, y]
      by_cases hxi : x.1 i = true
      · rw [if_neg]
        intro hiζ
        apply hζbad
        simp only [bad, Set.mem_iUnion]
        exact ⟨i, Finset.mem_coe.mpr hi, hζZ, hxi, hiζ⟩
      · have hxi' : x.1 i = false := Bool.eq_false_of_not_eq_true hxi
        by_cases hiζ : cnfExtensionLE i.1 ζ.1
        · rw [if_pos hiζ, hxi']
        · rw [if_neg hiζ, hxi']
    have hfy : 0 < f yK := hF yK hyF
    have hfζ := hf ⟨ζ, hζZ, rfl⟩ yK
    have hyζ : yK.1 ζ = false := by
      dsimp [yK, y]
      rw [if_pos (show cnfExtensionLE ζ.1 ζ.1 from Or.inl rfl)]
    simp only [ordinalProjection, hyζ, Bool.false_eq_true, ↓reduceIte] at hfζ
    exact not_lt_of_ge hfζ hfy
end OrderClosures
