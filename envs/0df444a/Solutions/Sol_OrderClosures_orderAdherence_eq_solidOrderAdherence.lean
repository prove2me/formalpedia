-- Prove2me | solution 1 for OrderClosures.orderAdherence_eq_solidOrderAdherence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:55:38.614842+00:00
-- url     : https://prove2.me/submissions/af760b5b-0b88-47f6-accf-fc2f2add876b

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Pi
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_MeyerNieberg
public import Definitions.Def_LeanPool_OrderClosures_BanLat_LatticeSeminorm
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Sublattice
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Tactic_LLexpr
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Examples_CofK_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Operators_Hom
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
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
public import Theorems.Thm_OrderConvergesTo_inf
public import Theorems.Thm_OrderConvergesTo_neg
public import Theorems.Thm_OrderConvergesTo_sup
public import Theorems.Thm_Positive_extension_apply
public import Theorems.Thm_VectorSublattice_coe_toSubmodule
public import Theorems.Thm_VectorSublattice_mem_bot
public import Theorems.Thm_VectorSublattice_mem_top
public import Theorems.Thm_coe_toCompletionVecLatHom
public import Theorems.Thm_orderConvergesTo_const
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
open OrderClosures
universe u v
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
omit [VectorLattice X]
namespace OrderClosures
theorem _root_.solution {A : Set X}
    (hA : LatticeOrderedAddCommGroup.IsSolid A) :
    orderAdherence A = solidOrderAdherence A := by
  ext x
  constructor
  · rintro ⟨ι, hpre, hdir, hne, f, hfA, hf⟩
    let : Preorder ι := hpre
    let : IsDirected ι (· ≤ ·) := hdir
    let : Nonempty ι := hne
    rcases hf with ⟨κ, hκpre, hκdir, hκne, r, hranti, hrnonneg, hrglb, hbound⟩
    let : Preorder κ := hκpre
    let : IsDirected κ (· ≤ ·) := hκdir
    let : Nonempty κ := hκne
    let y : κ → X := fun k ↦ (|x| - r k)⁺
    have hy_mono : Monotone y := by
      intro k l hkl
      exact posPart_mono (sub_le_sub_left (hranti hkl) |x|)
    have hy_mem : ∀ k, y k ∈ A := by
      intro k
      obtain ⟨i, hi⟩ := (hbound k).exists
      have hx_le : |x| ≤ |f i| + r k := by
        calc
          |x| = |(x - f i) + f i| := by congr 1; abel
          _ ≤ |x - f i| + |f i| := abs_add_le _ _
          _ = |f i| + |x - f i| := add_comm _ _
          _ ≤ |f i| + r k := add_le_add_right (by simpa [abs_sub_comm] using hi) _
      have hsub : |x| - r k ≤ |f i| := sub_le_iff_le_add.mpr hx_le
      have hy_le : y k ≤ |f i| :=
        show (|x| - r k) ⊔ 0 ≤ |f i| from sup_le hsub (abs_nonneg _)
      exact hA (hfA i) (by simpa [y, abs_of_nonneg (posPart_nonneg _)] using hy_le)
    have hy_lub : IsLUB (Set.range y) |x| := by
      refine ⟨?_, ?_⟩
      · rintro _ ⟨k, rfl⟩
        exact show (|x| - r k) ⊔ 0 ≤ |x| from
          sup_le (sub_le_self _ (hrnonneg k)) (abs_nonneg _)
      · intro c hc
        have hlow : |x| - c ∈ lowerBounds (Set.range r) := by
          rintro _ ⟨k, rfl⟩
          have hraw : |x| - r k ≤ c := (le_posPart _).trans (hc ⟨k, rfl⟩)
          exact sub_le_iff_le_add.mpr (by
            simpa [add_comm] using (sub_le_iff_le_add.mp hraw))
        exact sub_nonpos.mp (hrglb.2 hlow)
    refine ⟨|x|, ?_, ?_⟩
    · refine ⟨abs_nonneg x, Set.range y, ?_, ?_, ?_, hy_lub⟩
      · rintro _ ⟨k, rfl⟩
        exact ⟨hy_mem k, posPart_nonneg _⟩
      · exact Set.range_nonempty y
      · rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩
        obtain ⟨m, hkm, hlm⟩ := directed_of (· ≤ ·) k l
        exact ⟨y m, ⟨m, rfl⟩, hy_mono hkm, hy_mono hlm⟩
    · simp
  · rintro ⟨z, hz, hxz⟩
    rcases hz with ⟨hz, B, hBA, hBne, hBdir, hBlub⟩
    have hxz' : |x| ≤ z := by simpa [abs_of_nonneg hz] using hxz
    let : Nonempty B := hBne.to_subtype
    let : IsDirectedOrder B := hBdir.isDirectedOrder
    let b : B → X := fun w ↦ w.1
    have hb_mono : Monotone b := by
      intro p q hpq
      exact hpq
    have hb_range : Set.range b = B := by
      ext w
      simp [b]
    have hb_order : OrderConvergesTo b z :=
      orderConvergesTo_of_monotone_isLUB hb_mono (by simpa [hb_range] using hBlub)
    let g : B → X := fun w ↦ (x ⊓ b w) ⊔ (-b w)
    have hg_mem : ∀ w, g w ∈ A := by
      intro w
      have hw := hBA w.2
      have hg_upper : g w ≤ b w := by
        exact sup_le inf_le_right ((neg_nonpos.mpr hw.2).trans hw.2)
      have hg_lower : -g w ≤ b w := by
        simpa using neg_le_neg (show -b w ≤ g w from le_sup_right)
      have hg_abs : |g w| ≤ b w := (abs_le').2 ⟨hg_upper, hg_lower⟩
      exact hA hw.1 (by simpa [b, abs_of_nonneg hw.2] using hg_abs)
    have hxbounds : x ≤ z ∧ -x ≤ z := (abs_le').mp hxz'
    have hnegzx : -z ≤ x := by simpa using neg_le_neg hxbounds.2
    have hlim : x ⊓ z ⊔ -z = x := by
      rw [inf_eq_left.mpr hxbounds.1, sup_eq_left.mpr hnegzx]
    have hg_order : OrderConvergesTo g x := by
      have h := ((orderConvergesTo_const (X := X) (ι := B) x).inf hb_order).sup hb_order.neg
      simpa [g, hlim] using h
    exact ⟨B, inferInstance, inferInstance, inferInstance, g, hg_mem, hg_order⟩
end OrderClosures
