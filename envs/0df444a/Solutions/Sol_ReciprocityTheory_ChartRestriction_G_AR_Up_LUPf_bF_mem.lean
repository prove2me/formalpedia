-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.bF_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:49:27.548194+00:00
-- url     : https://prove2.me/submissions/61ff7536-072a-4be2-9c58-5c33acb0ee3e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUPf_Lm_lowU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUPf_lminors_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero


section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r)
variable {X x0}
private lemma Lm_mul_apply_eq_zero_of_lt {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i k : Fin n) (hki : k < i)
    (hdet : (lb M i).det ≠ 0) : (Lm M * M) i k = 0 := by
  have hkey : ∑ j : Fin i, wv M i j * M (Fin.castLE i.isLt.le j) k = M i k := by
    have h1 : vecMul (wv M i) (lb M i) = fun j : Fin i => M i (Fin.castLE i.isLt.le j) := by
      unfold wv
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.vecMul_one]
    have h2 := congrFun h1 ⟨k.1, hki⟩
    simp only [Matrix.vecMul, dotProduct, Matrix.submatrix_apply] at h2
    exact h2
  have hf : ∀ j : Fin n, Lm M i j * M j k =
      (if h : (j : ℕ) < i then -wv M i ⟨j, h⟩ * M j k else 0) + (if j = i then M j k else 0) := by
    intro j
    simp only [Lm, Matrix.of_apply]
    by_cases h : (j : ℕ) < i
    · have hne : j ≠ i := fun e => by rw [e] at h; exact lt_irrefl _ h
      rw [dif_pos h, dif_pos h, if_neg hne]
      ring
    · rw [dif_neg h, dif_neg h]
      by_cases e : j = i
      · rw [if_pos e, if_pos e]
        ring
      · rw [if_neg e, if_neg e]
        ring
  have hg : ∑ j : Fin n, (if h : (j : ℕ) < i then -wv M i ⟨j, h⟩ * M j k else 0) =
      ∑ j : Fin i, -wv M i j * M (Fin.castLE i.isLt.le j) k := by
    symm
    apply Finset.sum_of_injOn (Fin.castLE i.isLt.le)
    · exact (Fin.castLE_injective _).injOn
    · intro _ _
      exact Finset.mem_coe.mpr (Finset.mem_univ _)
    · intro j _ hj
      rw [dif_neg]
      intro hlt
      exact hj ⟨⟨j.1, hlt⟩, Finset.mem_coe.mpr (Finset.mem_univ _), Fin.ext rfl⟩
    · intro j _
      split_ifs with h
      · rfl
      · exact absurd j.isLt h
  rw [Matrix.mul_apply, Finset.sum_congr rfl fun j _ => hf j, Finset.sum_add_distrib, hg,
    Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ _), ← hkey]
  simp only [neg_mul, Finset.sum_neg_distrib, neg_add_cancel]
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r)
variable {X x0}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
theorem _root_.solution {x : Frame X.Ψ r} (_hx : x ∈ X.dom) (hΔ : DeltaF X x0 x ≠ 0) : bF X x0 x ∈ Bor X.Ψ r := by
  show ∀ τ : X.Ψ, (mat (bF X x0 x) τ).det ≠ 0 ∧ ∀ a c : Fin r, c < a → bF X x0 x τ a c = 0
  intro τ
  have hM := lminors_ne hΔ τ
  refine ⟨?_, fun a c hca => ?_⟩
  · show (Lm (Mx X x0 x τ) * Mx X x0 x τ).det ≠ 0
    rw [Matrix.det_mul, (Lm_lowU _).det, one_mul]
    exact hM (Fin.last r)
  · show (Lm (Mx X x0 x τ) * Mx X x0 x τ) a c = 0
    exact Lm_mul_apply_eq_zero_of_lt _ a c hca (hM a.castSucc)
end ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
