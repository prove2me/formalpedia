-- Prove2me | solution 1 for OrderClosures.weakFatou_iterated_unitBall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:15:55.042086+00:00
-- url     : https://prove2.me/submissions/18defdfb-e923-4d31-b951-3d733088ce71

module
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Reductions
public import Theorems.Thm_OrderClosures_iteratedOrderAdherence_mono_and_scale
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
public import Theorems.Thm_OrderClosures_orderAdherence_mono
public import Theorems.Thm_OrderConvergesTo_le
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
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
namespace OrderClosures
theorem _root_.solution
    (p : PaperLatticeNorm X) {K : ℝ} (hK : HasWeakFatouProperty p K) :
    ∀ m ≥ 1, iteratedOrderAdherence (unitBallFor p) m ⊆
      scaleSet (K ^ m) (unitBallFor p) := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK.1
  have hsolid : LatticeOrderedAddCommGroup.IsSolid (unitBallFor p) := by
    intro y hy x hxy
    exact (p.solid hxy).trans hy
  have hstep : orderAdherence (unitBallFor p) ⊆ scaleSet K (unitBallFor p) := by
    rw [orderAdherence_eq_solidOrderAdherence hsolid]
    rintro x ⟨z, hz, hxz⟩
    rcases hz with ⟨hz0, B, hB, hBne, hBdir, hBlub⟩
    let : Nonempty B := hBne.to_subtype
    let : IsDirectedOrder B := hBdir.isDirectedOrder
    let f : B → X := fun b ↦ b.1
    have hfmono : Monotone f := fun _ _ h ↦ h
    have hfrange : Set.range f = B := by
      ext y
      simp [f]
    have hpz : p z ≤ K := by
      have h := hK.2 f z hfmono (fun b ↦ (hB b.2).2)
        (by simpa [hfrange] using hBlub) 1
        (fun b ↦ hB b.2 |>.1)
      simpa using h
    have hpx : p x ≤ K := (p.solid hxz).trans hpz
    refine ⟨K⁻¹ • x, ?_, by simp [smul_smul, hKpos.ne']⟩
    change p (K⁻¹ • x) ≤ 1
    rw [p.smul, abs_of_pos (inv_pos.mpr hKpos)]
    calc
      K⁻¹ * p x ≤ K⁻¹ * K :=
        mul_le_mul_of_nonneg_left hpx (inv_nonneg.mpr hKpos.le)
      _ = 1 := inv_mul_cancel₀ hKpos.ne'
  intro m
  induction m with
  | zero =>
      intro hm
      omega
  | succ m ih =>
      intro _
      by_cases hm0 : m = 0
      · subst m
        simpa [iteratedOrderAdherence] using hstep
      · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
        have hpowpos : 0 < K ^ m := pow_pos hKpos m
        have hscale :=
          (iteratedOrderAdherence_mono_and_scale
            (A := unitBallFor p) (B := unitBallFor p) hpowpos).2.1
        intro x hx
        change x ∈ orderAdherence (iteratedOrderAdherence (unitBallFor p) m) at hx
        have hxscaled : x ∈ orderAdherence (scaleSet (K ^ m) (unitBallFor p)) :=
          orderAdherence_mono (ih hm1) hx
        rw [hscale] at hxscaled
        rcases hxscaled with ⟨y, hy, hyx⟩
        rcases hstep hy with ⟨z, hz, hzy⟩
        refine ⟨z, hz, ?_⟩
        calc
          K ^ (m + 1) • z = K ^ m • (K • z) := by rw [pow_succ, mul_smul]
          _ = K ^ m • y := congrArg (fun w ↦ K ^ m • w) hzy
          _ = x := hyx
end OrderClosures
