-- Prove2me | solution 1 for OrderClosures.fatou_iterated_unitBall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:10:34.318194+00:00
-- url     : https://prove2.me/submissions/28fde97d-32d6-47a7-b4e4-4f0c5fb15e20

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
public import Theorems.Thm_OrderClosures_orderAdherence_eq_solidOrderAdherence
public import Theorems.Thm_OrderClosures_subset_orderAdherence
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
    (p : PaperLatticeNorm X) (hp : HasFatouProperty p) :
    ∀ m ≥ 1, iteratedOrderAdherence (unitBallFor p) m = unitBallFor p := by
  have hsolid : LatticeOrderedAddCommGroup.IsSolid (unitBallFor p) := by
    intro y hy x hxy
    exact (p.solid hxy).trans hy
  have hstep : orderAdherence (unitBallFor p) = unitBallFor p := by
    apply Set.Subset.antisymm
    · rw [orderAdherence_eq_solidOrderAdherence hsolid]
      rintro x ⟨z, hz, hxz⟩
      rcases hz with ⟨hz0, B, hB, hBne, hBdir, hBlub⟩
      let : Nonempty B := hBne.to_subtype
      let : IsDirectedOrder B := hBdir.isDirectedOrder
      let f : B → X := fun b ↦ b.1
      have hfmono : Monotone f := fun _ _ h ↦ h
      have hfrange : Set.range f = B := by
        ext y
        simp [f]
      have hpnorm := hp f z hfmono (fun b ↦ (hB b.2).2)
        (by simpa [hfrange] using hBlub)
      have hpz : p z ≤ 1 := hpnorm.2 (by
        rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
        exact (hB b.2).1)
      exact (p.solid hxz).trans hpz
    · exact subset_orderAdherence (unitBallFor p)
  have hall : ∀ m, iteratedOrderAdherence (unitBallFor p) m = unitBallFor p := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
        simp only [iteratedOrderAdherence]
        rw [ih, hstep]
  exact fun m _ ↦ hall m
end OrderClosures
