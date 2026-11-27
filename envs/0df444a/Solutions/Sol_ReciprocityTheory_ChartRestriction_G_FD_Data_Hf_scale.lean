-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.Hf_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:26:01.784125+00:00
-- url     : https://prove2.me/submissions/7d663bef-acb8-4f29-a35c-fdb1c432d921

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowFixesComplementOfIsotropic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_hC_flow_e
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_hC_right_flow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_col_flow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_hC_ppos_e
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_flowMat_mulVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_gramPos_det_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hC_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hC_add_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hC_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hC_sub_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hC_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
variable (ξ : Fin r → E) (τ : X.Ψ)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution (hiso : hermC τ.1 X.Gm (emb τ.1 ξ) (emb τ.1 ξ) = 0) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (s : X.Ψ → ℂ) (hxs : X.flow ξ s x ∈ X.dom) :
    ∃ k : ℂ, k ≠ 0 ∧ ∀ v : Fin r → ℂ, hermC τ.1 X.Gm v (emb τ.1 ξ) = 0 →
      X.Hf x τ v (emb τ.1 ξ) = k * X.Hf (X.flow ξ s x) τ v (emb τ.1 ξ) := by
  set e := emb τ.1 ξ with he
  set T := X.flowMat ξ τ (s τ) with hTdef
  set β : ℂ := -(I * X.c τ * s τ) with hβ
  set A := X.gramPos x τ with hAdef
  set A' := X.gramPos (X.flow ξ s x) τ with hA'def
  set l : Fin X.p0 → ℂ := fun a => hermC τ.1 X.Gm (col (mat x τ) (Fin.castLE X.p0_le a)) e with hl
  have hAdet := gramPos_det_ne X hx τ
  have hA'det := gramPos_det_ne X hxs τ
  have hsymm : ∀ v w, hermC τ.1 X.Gm v w = conj (hermC τ.1 X.Gm w v) := fun v w =>
    hC_symm τ.1 X.Gm X.Gm_herm w v

  have hA' : ∀ a b, A' a b = A a b + (β + conj β) * l a * conj (l b) := by
    intro a b
    have h1 : A' a b = hermC τ.1 X.Gm (Matrix.mulVec T (col (mat x τ) (Fin.castLE X.p0_le a)))
        (Matrix.mulVec T (col (mat x τ) (Fin.castLE X.p0_le b))) := by
      simp only [hA'def, gramPos, gram, Matrix.submatrix_apply, Matrix.of_apply, col_flow, hTdef]
    rw [h1, flowMat_mulVec, flowMat_mulVec, hC_add_left, hC_add_right, hC_add_right, hC_smul_left,
      hC_smul_left, hC_smul_right, hC_smul_right, hiso, hsymm e (col (mat x τ) (Fin.castLE X.p0_le b))]
    simp only [hAdef, gramPos, gram, Matrix.submatrix_apply, Matrix.of_apply, hl, hβ, map_mul]
    ring

  have hA'mul : ∀ y : Fin X.p0 → ℂ, Matrix.mulVec A' y =
      Matrix.mulVec A y + ((β + conj β) * dotProduct (fun b => conj (l b)) y) • l := by
    intro y
    funext a
    simp only [Matrix.mulVec, dotProduct, hA', Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
      Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  set y := Matrix.mulVec A⁻¹ l with hy
  have hAy : Matrix.mulVec A y = l := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit hAdet), Matrix.one_mulVec]
  set k : ℂ := 1 + (β + conj β) * dotProduct (fun b => conj (l b)) y with hk
  have hA'y : Matrix.mulVec A' y = k • l := by
    rw [hA'mul, hAy, hk, add_smul, one_smul]
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hA'y
    have hy0 : y = 0 := by
      have := congrArg (Matrix.mulVec A'⁻¹) hA'y
      rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (Ne.isUnit hA'det), Matrix.one_mulVec,
        Matrix.mulVec_zero] at this
    have hl0 : l = 0 := by rw [← hAy, hy0, Matrix.mulVec_zero]
    rw [hk] at h0
    simp [hy0] at h0
  have hyk : y = k • Matrix.mulVec A'⁻¹ l := by
    have := congrArg (Matrix.mulVec A'⁻¹) hA'y
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (Ne.isUnit hA'det), Matrix.one_mulVec,
      Matrix.mulVec_smul] at this
  refine ⟨k, hk0, fun v hv => ?_⟩
  have hcv : (fun b => hermC τ.1 X.Gm v (col (mat (X.flow ξ s x) τ) (Fin.castLE X.p0_le b))) =
      fun b => hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le b)) := by
    funext b; rw [col_flow, hC_right_flow X ξ τ _ _ _ hv]
  have hlT : (fun a => hermC τ.1 X.Gm (col (mat (X.flow ξ s x) τ) (Fin.castLE X.p0_le a)) e) = l := by
    funext a; rw [col_flow, hC_flow_e X ξ τ hiso]
  simp only [Hf]
  rw [hC_sub_left, hC_sub_left, hC_smul_left, hC_smul_left, hv, sub_zero, sub_zero,
    hC_ppos_e, hC_ppos_e, hcv, hlT]
  rw [show Matrix.mulVec (X.gramPos x τ)⁻¹ (fun a => hermC τ.1 X.Gm (col (mat x τ)
      (Fin.castLE X.p0_le a)) e) = y from rfl, hyk, dotProduct_smul, smul_eq_mul]
  ring
end ReciprocityTheory.ChartRestriction.G.FD.Data
