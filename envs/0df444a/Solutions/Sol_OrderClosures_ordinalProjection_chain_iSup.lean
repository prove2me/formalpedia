-- Prove2me | solution 1 for OrderClosures.ordinalProjection_chain_iSup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:14:29.440804+00:00
-- url     : https://prove2.me/submissions/f855dd7a-da6c-4825-b8a9-be53782f0fe2

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
public import Theorems.Thm_OrderClosures_continuousMap_exists_finite_coordinates
public import Theorems.Thm_OrderClosures_ordinalProjection_le_iff
public import Theorems.Thm_OrderClosures_cnfExtensionLE_chain_lub
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
public import Theorems.Thm_OrderClosures_CNFListLT_ordinal_lt
public import Theorems.Thm_OrderClosures_CNFListLT_trans
public import Theorems.Thm_OrderClosures_CNFStep_trans
public import Theorems.Thm_OrderClosures_cnfExtensionLE_partialOrder_and_subrelation
public import Theorems.Thm_OrderClosures_cnfExtensionLT_iff_CNFListLT
public import Theorems.Thm_OrderClosures_cnfExtensionLT_linear_above
public import Theorems.Thm_OrderConvergesTo_le
public import Theorems.Thm_OrderConvergesTo_sup
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
    (ξ : Ordinal.{u}) (Z : Set (GaoIndex ξ)) (α : GaoIndex ξ)
    (hne : Z.Nonempty)
    (hchain : ∀ ⦃ζ⦄, ζ ∈ Z → ∀ ⦃ζ'⦄, ζ' ∈ Z →
      cnfExtensionLE ζ.1 ζ'.1 ∨ cnfExtensionLE ζ'.1 ζ.1)
    (hsup : IsLUB ((fun ζ : GaoIndex ξ ↦ ζ.1) '' Z) α.1) :
    IsLUB (ordinalProjection ξ '' Z) (ordinalProjection ξ α) := by
  classical
  constructor
  · rintro _ ⟨ζ, hζ, rfl⟩
    exact (ordinalProjection_le_iff ξ ζ α).2
      (cnfExtensionLE_chain_lub ξ Z α hchain hsup ζ hζ)
  · intro f hf
    by_cases hαZ : α ∈ Z
    · exact hf ⟨α, hαZ, rfl⟩
    · intro x
      by_cases hx : x.1 α = true
      · change (if x.1 α = true then 1 else 0) ≤ f x
        rw [if_pos hx]
        by_contra hle
        have hfx : f x < 1 := lt_of_not_ge hle
        obtain ⟨F, hF⟩ := continuousMap_exists_finite_coordinates f x
          isOpen_Iio hfx
        have hαpos : 0 < α.1 := by
          rw [pos_iff_ne_zero]
          intro hαzero
          obtain ⟨ζ, hζ⟩ := hne
          have hζα : ζ.1 ≤ α.1 := hsup.1 ⟨ζ, hζ, rfl⟩
          have hζzero : ζ.1 = 0 :=
            le_antisymm (hαzero ▸ hζα) (zero_le : (0 : Ordinal) ≤ ζ.1)
          apply hαZ
          have hζeq : ζ = α := Subtype.ext (hζzero.trans hαzero.symm)
          exact hζeq ▸ hζ
        let Fα := F.filter fun i ↦ i.1 < α.1
        let δ : Ordinal.{u} := Fα.sup fun i ↦ i.1
        have hδα : δ < α.1 := by
          apply (Finset.sup_lt_iff hαpos).2
          intro i hi
          exact (Finset.mem_filter.mp hi).2
        have hex : ∃ ζ ∈ Z, δ < ζ.1 := by
          by_contra h
          push Not at h
          have hαδ : α.1 ≤ δ := hsup.2 (by
            rintro _ ⟨ζ, hζ, rfl⟩
            exact h ζ hζ)
          exact (not_le_of_gt hδα) hαδ
        obtain ⟨ζ₀, hζ₀Z, hδζ₀⟩ := hex
        let y : GaoIndex ξ → Bool := fun a ↦
          if cnfExtensionLE ζ₀.1 a.1 then true else x.1 a
        have hy_mono : ∀ a b : GaoIndex ξ,
            cnfExtensionLT a.1 b.1 → y a ≤ y b := by
          intro a b hab
          dsimp [y]
          by_cases ha : cnfExtensionLE ζ₀.1 a.1
          · have hb : cnfExtensionLE ζ₀.1 b.1 :=
              cnfExtensionLE_partialOrder_and_subrelation.1.trans
                ζ₀.1 a.1 b.1 ha (Or.inr hab)
            rw [if_pos ha, if_pos hb]
          · rw [if_neg ha]
            by_cases hb : cnfExtensionLE ζ₀.1 b.1
            · rw [if_pos hb]
              exact Bool.le_true _
            · rw [if_neg hb]
              exact x.2 a b hab
        have hζ₀α : cnfExtensionLT ζ₀.1 α.1 := by
          rcases cnfExtensionLE_chain_lub ξ Z α hchain hsup ζ₀ hζ₀Z with
            heq | hlt
          · have hsubeq : ζ₀ = α := Subtype.ext heq
            exact (hαZ (hsubeq ▸ hζ₀Z)).elim
          · exact hlt
        have hζ₀αOrd : ζ₀.1 < α.1 :=
          CNFListLT.ordinal_lt (cnfExtensionLT_iff_CNFListLT.mp hζ₀α)
        let yK : GaoCompactSpace ξ := ⟨y, hy_mono⟩
        have hyF : ∀ i ∈ F, yK.1 i = x.1 i := by
          intro i hi
          dsimp [yK, y]
          by_cases hζ₀i : cnfExtensionLE ζ₀.1 i.1
          · rw [if_pos hζ₀i]
            have hζ₀iOrd : ζ₀.1 ≤ i.1 :=
              cnfExtensionLE_partialOrder_and_subrelation.2 hζ₀i
            by_cases hiα : i.1 < α.1
            · have hiFα : i ∈ Fα := Finset.mem_filter.mpr ⟨hi, hiα⟩
              have hiδ : i.1 ≤ δ := Finset.le_sup (f := fun j ↦ j.1) hiFα
              exact (not_lt_of_ge hiδ (hδζ₀.trans_le hζ₀iOrd)).elim
            · have hαi : α.1 ≤ i.1 := le_of_not_gt hiα
              rcases hαi.eq_or_lt with hαeqi | hαi
              · have hsubeq : α = i := Subtype.ext hαeqi
                subst i
                exact hx.symm
              · have hζ₀iLT : cnfExtensionLT ζ₀.1 i.1 := by
                  rcases hζ₀i with hζ₀eqi | hζ₀i
                  · exact (not_lt_of_ge hαi.le (hζ₀eqi ▸ hζ₀αOrd)).elim
                  · exact hζ₀i
                have hαiLT : cnfExtensionLT α.1 i.1 :=
                  (cnfExtensionLT_linear_above ζ₀.1 hζ₀α hζ₀iLT).mpr hαi
                exact (Bool.le_iff_imp.mp (x.2 α i hαiLT) hx).symm
          · rw [if_neg hζ₀i]
        have hfy : f yK < 1 := hF yK hyF
        have hupper := hf ⟨ζ₀, hζ₀Z, rfl⟩ yK
        have hyζ₀ : yK.1 ζ₀ = true := by
          dsimp [yK, y]
          rw [if_pos (show cnfExtensionLE ζ₀.1 ζ₀.1 from Or.inl rfl)]
        change (if yK.1 ζ₀ = true then 1 else 0) ≤ f yK at hupper
        rw [if_pos hyζ₀] at hupper
        exact (not_lt_of_ge hupper hfy).elim
      · have hnonneg : 0 ≤ f x := by
          obtain ⟨ζ, hζ⟩ := hne
          have hproj : 0 ≤ ordinalProjection ξ ζ x := by
            change 0 ≤ if x.1 ζ = true then 1 else 0
            split_ifs <;> norm_num
          exact hproj.trans (hf ⟨ζ, hζ, rfl⟩ x)
        simp only [ordinalProjection, hx]
        exact hnonneg
end OrderClosures
