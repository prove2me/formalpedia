-- Prove2me | solution 1 for OrderClosures.finalSpace_weakFatou
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:20:16.137792+00:00
-- url     : https://prove2.me/submissions/de1b63eb-6b5c-479d-bfd5-31c0fae999ee

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Moderated
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_FinalSpace
public import Theorems.Thm_OrderClosures_finalCoordinateEmbedding_ne
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
public import Theorems.Thm_OrderClosures_component_basic
public import Theorems.Thm_OrderClosures_component_weakFatou
public import Theorems.Thm_OrderConvergesTo_le
public import Theorems.Thm_OrderConvergesTo_nonneg
public import Theorems.Thm_OrderConvergesTo_smul
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
theorem _root_.solution :
    IsCompleteFor finalLatticeNorm ∧ HasWeakFatouProperty finalLatticeNorm 2 := by
  have hcomplete : IsCompleteFor finalLatticeNorm := by
    intro f hf
    have hcoordCauchy (k : ℕ) :
        ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ q ≥ N,
          componentLatticeNorm k ((f m).1 k - (f q).1 k) < ε := by
      intro ε hε
      obtain ⟨N, hN⟩ := hf ε hε
      refine ⟨N, fun m hm q hq ↦ ?_⟩
      exact (componentNorm_le_finalNormValue (f m - f q) k).trans_lt
        (hN m hm q hq)
    choose x hx using fun k ↦ (component_basic k).2.1 (fun m ↦ (f m).1 k) (hcoordCauchy k)
    have hxVanishes : componentVanishes x := by
      change Tendsto (fun k ↦ componentLatticeNorm k (x k)) atTop (nhds 0)
      rw [Metric.tendsto_atTop]
      intro ε hε
      have hthird : 0 < ε / 3 := div_pos hε (by norm_num)
      obtain ⟨N, hN⟩ := hf (ε / 3) hthird
      have hfN : Tendsto (fun k ↦ componentLatticeNorm k ((f N).1 k))
          atTop (nhds 0) := (f N).2
      rw [Metric.tendsto_atTop] at hfN
      obtain ⟨K, hK⟩ := hfN (ε / 3) hthird
      refine ⟨K, fun k hk ↦ ?_⟩
      obtain ⟨L, hL⟩ := hx k (ε / 3) hthird
      let m := max N L
      have hmN : N ≤ m := le_max_left _ _
      have hmL : L ≤ m := le_max_right _ _
      have hmx : componentLatticeNorm k ((f m).1 k - x k) < ε / 3 := hL m hmL
      have hfmN : componentLatticeNorm k ((f m).1 k - (f N).1 k) < ε / 3 := by
        exact (componentNorm_le_finalNormValue (f m - f N) k).trans_lt (hN m hmN N le_rfl)
      have hfNk : componentLatticeNorm k ((f N).1 k) < ε / 3 := by
        have := hK k hk
        rw [Real.dist_eq, sub_zero, abs_of_nonneg ((componentLatticeNorm k).nonneg _)] at this
        exact this
      have hneg : componentLatticeNorm k (x k - (f m).1 k) =
          componentLatticeNorm k ((f m).1 k - x k) := by
        rw [show x k - (f m).1 k = -((f m).1 k - x k) by abel,
          show -((f m).1 k - x k) = (-1 : ℝ) • ((f m).1 k - x k) by simp,
          (componentLatticeNorm k).smul]
        norm_num
      have hxbound : componentLatticeNorm k (x k) < ε := by
        calc
          componentLatticeNorm k (x k) =
              componentLatticeNorm k ((x k - (f m).1 k) +
                (((f m).1 k - (f N).1 k) + (f N).1 k)) := by
            congr 1
            abel
          _ ≤ componentLatticeNorm k (x k - (f m).1 k) +
              componentLatticeNorm k (((f m).1 k - (f N).1 k) + (f N).1 k) :=
            (componentLatticeNorm k).add_le _ _
          _ ≤ componentLatticeNorm k (x k - (f m).1 k) +
              (componentLatticeNorm k ((f m).1 k - (f N).1 k) +
                componentLatticeNorm k ((f N).1 k)) :=
            add_le_add le_rfl ((componentLatticeNorm k).add_le _ _)
          _ < ε := by rw [hneg]; linarith
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ((componentLatticeNorm k).nonneg _)]
      exact hxbound
    let x₀ : FinalSpace := ⟨x, hxVanishes⟩
    refine ⟨x₀, ?_⟩
    intro ε hε
    have hhalf : 0 < ε / 2 := half_pos hε
    obtain ⟨N, hN⟩ := hf (ε / 2) hhalf
    refine ⟨N, fun q hq ↦ ?_⟩
    have hcoord (k : ℕ) :
        componentLatticeNorm k ((f q).1 k - x k) ≤ ε / 2 := by
      apply le_of_forall_pos_le_add
      intro δ hδ
      obtain ⟨L, hL⟩ := hx k δ hδ
      let m := max N L
      have hmN : N ≤ m := le_max_left _ _
      have hmL : L ≤ m := le_max_right _ _
      calc
        componentLatticeNorm k ((f q).1 k - x k) =
            componentLatticeNorm k (((f q).1 k - (f m).1 k) +
              ((f m).1 k - x k)) := by
          congr 1
          abel
        _ ≤ componentLatticeNorm k ((f q).1 k - (f m).1 k) +
            componentLatticeNorm k ((f m).1 k - x k) :=
          (componentLatticeNorm k).add_le _ _
        _ ≤ ε / 2 + δ :=
          (add_lt_add (componentNorm_le_finalNormValue (f q - f m) k |>.trans_lt
            (hN q hq m hmN)) (hL m hmL)).le
    have hfinal : finalLatticeNorm (f q - x₀) ≤ ε / 2 := by
      apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨k, rfl⟩
      exact hcoord k
    exact hfinal.trans_lt (by linarith)
  have hweak : HasWeakFatouProperty finalLatticeNorm 2 := by
    refine ⟨by norm_num, ?_⟩
    intro ι _ _ _ f x hfmono hfpos hflub c hfc
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨k, rfl⟩
    have hcoordLUB : IsLUB (Set.range fun i ↦ (f i).1 k) (x.1 k) := by
      constructor
      · rintro _ ⟨i, rfl⟩
        exact hflub.1 ⟨i, rfl⟩ k
      · intro z hz
        let y : FinalSpace := x + finalCoordinateEmbedding k (z - x.1 k)
        have hyupper : y ∈ upperBounds (Set.range f) := by
          rintro _ ⟨i, rfl⟩ m
          by_cases hmk : m = k
          · subst m
            simpa [y] using hz ⟨i, rfl⟩
          · have hix := hflub.1 ⟨i, rfl⟩ m
            simpa [y, finalCoordinateEmbedding_ne k m hmk] using hix
        have hxy := hflub.2 hyupper k
        simpa [y] using hxy
    exact (component_weakFatou k).2.2 (fun i ↦ (f i).1 k) (x.1 k)
      (fun _ _ hij ↦ hfmono hij k) (fun i ↦ hfpos i k) hcoordLUB c
      (fun i ↦ (componentNorm_le_finalNormValue (f i) k).trans (hfc i))
  exact ⟨hcomplete, hweak⟩
end OrderClosures
