-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.IW.zero_mem_OmF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:05:12.63434+00:00
-- url     : https://prove2.me/submissions/05c4f26b-aff0-4d14-99af-8bc95198f7c0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_cpt_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.AR.Up.IW.V_zero_app
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IW
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff Matrix ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
private theorem gram_eq_lemma (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
private theorem mem_dom_of_isOrth' (x0 : Frame X.Ψ r) (ho : IsOrth X x0) : x0 ∈ X.dom := by
  have hsq : ∀ a : ℕ, sgn X.p0 a * sgn X.p0 a = 1 := fun a => by
    unfold sgn; split_ifs <;> norm_num
  have hd : ∀ τ : X.Ψ, ∀ i : Fin (r + 1), dmin X.Gm x0 τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    intro τ i
    unfold dmin lminor
    rw [ho τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    unfold psgn
    rw [Complex.ofReal_prod, ← Fin.prod_univ_eq_prod_range]
    rfl
  simp only [Data.dom, GG, Set.mem_setOf_eq]
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · intro h0
    have h3 := congrArg Matrix.det (ho τ)
    rw [gram_eq_lemma, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul,
      Matrix.det_diagonal] at h3
    exact (Finset.prod_ne_zero_iff.mpr (fun a _ => Complex.ofReal_ne_zero.mpr
      (by unfold sgn; split_ifs <;> norm_num))) h3.symm
  · have hps : psgn X.p0 i * psgn X.p0 i = 1 := by
      unfold psgn
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one (fun a _ => hsq a)
    rw [hd τ i, Complex.ofReal_re, hps]
    exact one_pos
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.IW
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.IW
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff Matrix ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IW
theorem _root_.solution (x0 : Frame X.Ψ r) (ho : IsOrth X x0) : (0 : V (nd X)) ∈ OmF X x0 := by
  show cpt X x0 0 ∈ X.dom
  rw [cpt_zero]
  exact mem_dom_of_isOrth' X x0 ho
end ReciprocityTheory.ChartRestriction.G.AR.Up.IW
