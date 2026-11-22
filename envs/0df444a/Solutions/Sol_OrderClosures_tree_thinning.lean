-- Prove2me | solution 1 for OrderClosures.tree_thinning
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:14:37.132516+00:00
-- url     : https://prove2.me/submissions/f852eed0-8d7f-4f54-8901-a03e810762c6

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Bands
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Moderated
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
public import Theorems.Thm_OrderClosures_le_lastBandOccurrence
public import Theorems.Thm_OrderClosures_mem_bandsAt_iff
public import Theorems.Thm_OrderConvergesTo_sup
public import Theorems.Thm_Positive_extension_apply
public import Theorems.Thm_VectorSublattice_coe_toSubmodule
public import Theorems.Thm_VectorSublattice_mem_bot
public import Theorems.Thm_VectorSublattice_mem_top
public import Theorems.Thm_coe_toCompletionVecLatHom
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
open Set Filter Topology
open scoped NNReal Topology
universe u
namespace OrderClosures
theorem _root_.solution
    (n : ℕ) (w : ℕ → TreeCoefficients n) (Λ : Finset (TreeBandIndex n))
    (hΛ : recurrentBands n w ⊆ (Λ : Set (TreeBandIndex n))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ B ∉ Λ,
      {m | (treeBandProjection n B (w (φ m))).support.Nonempty}.Subsingleton := by
  classical
  let φ : ℕ → ℕ := fun m ↦ Nat.rec 0 (fun _ r ↦
    max (r + 1) (((bandsAt n (w r)).filter fun B ↦ B ∉ Λ).sup fun B ↦
      lastBandOccurrence n w B + 1)) m
  have hφ_succ (m : ℕ) : φ (m + 1) =
      max (φ m + 1) (((bandsAt n (w (φ m))).filter fun B ↦ B ∉ Λ).sup fun B ↦
        lastBandOccurrence n w B + 1) := by simp [φ]
  have hφ : StrictMono φ := by
    apply strictMono_nat_of_lt_succ
    intro m
    rw [hφ_succ]
    exact (Nat.lt_succ_self _).trans_le (le_max_left _ _)
  refine ⟨φ, hφ, ?_⟩
  intro B hBΛ
  have hBfinite : {m | (treeBandProjection n B (w m)).support.Nonempty}.Finite := by
    apply Set.not_infinite.mp
    intro hInf
    exact hBΛ (hΛ hInf)
  intro i hi j hj
  by_contra hij
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have hBbands : B ∈ bandsAt n (w (φ i)) :=
      (mem_bandsAt_iff n _ B).mpr hi
    have hBfilter : B ∈ (bandsAt n (w (φ i))).filter fun B ↦ B ∉ Λ :=
      Finset.mem_filter.mpr ⟨hBbands, hBΛ⟩
    have hlast_lt_succ : lastBandOccurrence n w B < φ (i + 1) := by
      have hle := Finset.le_sup
        (s := (bandsAt n (w (φ i))).filter fun B ↦ B ∉ Λ)
        (f := fun B ↦ lastBandOccurrence n w B + 1) hBfilter
      change lastBandOccurrence n w B + 1 ≤ _ at hle
      have hle' := hle.trans (le_max_right (φ i + 1)
        (((bandsAt n (w (φ i))).filter fun B ↦ B ∉ Λ).sup fun B ↦
          lastBandOccurrence n w B + 1))
      rw [← hφ_succ] at hle'
      omega
    have hsucc_le : φ (i + 1) ≤ φ j := hφ.monotone (Nat.succ_le_iff.mpr hijlt)
    have hjlast := le_lastBandOccurrence n w B hBfinite hj
    omega
  · have hBbands : B ∈ bandsAt n (w (φ j)) :=
      (mem_bandsAt_iff n _ B).mpr hj
    have hBfilter : B ∈ (bandsAt n (w (φ j))).filter fun B ↦ B ∉ Λ :=
      Finset.mem_filter.mpr ⟨hBbands, hBΛ⟩
    have hlast_lt_succ : lastBandOccurrence n w B < φ (j + 1) := by
      have hle := Finset.le_sup
        (s := (bandsAt n (w (φ j))).filter fun B ↦ B ∉ Λ)
        (f := fun B ↦ lastBandOccurrence n w B + 1) hBfilter
      change lastBandOccurrence n w B + 1 ≤ _ at hle
      have hle' := hle.trans (le_max_right (φ j + 1)
        (((bandsAt n (w (φ j))).filter fun B ↦ B ∉ Λ).sup fun B ↦
          lastBandOccurrence n w B + 1))
      rw [← hφ_succ] at hle'
      omega
    have hsucc_le : φ (j + 1) ≤ φ i := hφ.monotone (Nat.succ_le_iff.mpr hjilt)
    have hilast := le_lastBandOccurrence n w B hBfinite hi
    omega
end OrderClosures
