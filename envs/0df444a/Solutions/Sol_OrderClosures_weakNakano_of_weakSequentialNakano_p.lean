-- Prove2me | solution 1 for OrderClosures.weakNakano_of_weakSequentialNakano_p
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:03:00.756585+00:00
-- url     : https://prove2.me/submissions/8e01b754-5512-4ebc-9cd6-3b1c0b9ea423

module
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Reductions
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
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
namespace OrderClosures
theorem _root_.solution
    {Y : Type u} [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [NormedVectorLattice Y] [TopologicalSpace.SeparableSpace Y]
    (p : PaperLatticeNorm Y) {K : ℝ}
    (hseq : IsWeakSequentialNakanoConstant (X := Y) p K) :
    IsWeakNakanoConstant (X := Y) p K := by
  refine ⟨hseq.1, ?_⟩
  intro A hApos hAdir hAbdd hAp ε hε
  classical
  by_cases hAempty : A = ∅
  · subst A
    refine ⟨0, le_rfl, by simp, ?_⟩
    rw [show p 0 = 0 from p.eq_zero_iff 0 |>.2 rfl]
    linarith [hseq.1]
  have hAne : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hAempty
  let : Nonempty ↥A := ⟨⟨Classical.choose hAne, Classical.choose_spec hAne⟩⟩
  let : TopologicalSpace.SeparableSpace ↥A := inferInstance
  obtain ⟨d, hdense⟩ := TopologicalSpace.exists_dense_seq ↥A
  let join : ↥A → ↥A → ↥A := fun a b ↦
    ⟨Classical.choose (hAdir a.1 a.2 b.1 b.2),
      (Classical.choose_spec (hAdir a.1 a.2 b.1 b.2)).1⟩
  have hjoin_left (a b : ↥A) : a.1 ≤ (join a b).1 :=
    (Classical.choose_spec (hAdir a.1 a.2 b.1 b.2)).2.1
  have hjoin_right (a b : ↥A) : b.1 ≤ (join a b).1 :=
    (Classical.choose_spec (hAdir a.1 a.2 b.1 b.2)).2.2
  let z : ℕ → ↥A := fun m ↦
    Nat.rec (d 0) (fun k a ↦ join a (d (k + 1))) m
  have hz_succ (m : ℕ) : z (m + 1) = join (z m) (d (m + 1)) := by simp [z]
  have hzmono : Monotone (fun m ↦ (z m).1) := by
    apply monotone_nat_of_le_succ
    intro m
    rw [hz_succ]
    exact hjoin_left _ _
  have hd_le_z : ∀ m, (d m).1 ≤ (z m).1 := by
    intro m
    cases m with
    | zero => simp [z]
    | succ m => rw [hz_succ]; exact hjoin_right _ _
  have hzpos : ∀ m, 0 ≤ (z m).1 := fun m ↦ hApos (z m).2
  have hzbdd : BddAbove (Set.range fun m ↦ (z m).1) := by
    rcases hAbdd with ⟨b, hb⟩
    exact ⟨b, by rintro _ ⟨m, rfl⟩; exact hb (z m).2⟩
  have hzp : ∀ m, p (z m).1 ≤ 1 := fun m ↦ hAp _ (z m).2
  obtain ⟨y, hypos, hyupper, hyp⟩ :=
    hseq.2 (fun m ↦ (z m).1) hzmono hzpos hzbdd hzp ε hε
  refine ⟨y, hypos, ?_, hyp⟩
  have hd_upper : ∀ m, (d m).1 ≤ y := fun m ↦ (hd_le_z m).trans (hyupper m)
  have hclosed : IsClosed {a : ↥A | a.1 ≤ y} :=
    isClosed_Iic.preimage continuous_subtype_val
  have hclosure : closure (Set.range d) ⊆ {a : ↥A | a.1 ≤ y} := by
    apply closure_minimal
    · rintro _ ⟨m, rfl⟩
      exact hd_upper m
    · exact hclosed
  intro q hq
  exact hclosure (by rw [hdense.closure_eq]; exact Set.mem_univ ⟨q, hq⟩)
end OrderClosures
