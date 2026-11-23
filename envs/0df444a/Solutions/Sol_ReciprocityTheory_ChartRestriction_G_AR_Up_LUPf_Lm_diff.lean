-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.Lm_diff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:35:29.037793+00:00
-- url     : https://prove2.me/submissions/17cf1a55-7304-4b91-85d4-a5c725865218

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUPf_diffOn_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUPf_Mx_diff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUPf_det_lb
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



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
  Metric
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {x0 : Frame X.Ψ r}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
theorem _root_.solution (τ : X.Ψ) (i k : Fin r) :
    DifferentiableOn ℂ (fun x => Lm (Mx X x0 x τ) i k) (cellL X x0) := by
  have hl : ∀ x ∈ cellL X x0, ∀ k : Fin (r + 1), lminor (Mx X x0 x τ) k ≠ 0 := by
    intro x hx k
    have h1 : DeltaF X x0 x ≠ 0 := hx.2
    unfold DeltaF at h1
    exact Finset.prod_ne_zero_iff.mp (Finset.prod_ne_zero_iff.mp h1 τ (Finset.mem_univ _)) k
      (Finset.mem_univ _)
  by_cases h1 : (k : ℕ) < i
  · simp only [Lm, Matrix.of_apply, h1, ↓reduceDIte]
    have hinv : ∀ a b, DifferentiableOn ℂ (fun x => (lb (Mx X x0 x τ) i)⁻¹ a b) (cellL X x0) :=
      diffOn_inv (fun x => lb (Mx X x0 x τ) i) (fun a b => (Mx_diff τ _ _).differentiableOn)
        (fun x hx => by rw [det_lb]; exact hl x hx _)
    have hM : ∀ a b, DifferentiableOn ℂ (fun x => Mx X x0 x τ a b) (cellL X x0) :=
      fun a b => (Mx_diff τ a b).differentiableOn
    simp only [wv, Matrix.vecMul, dotProduct]
    refine DifferentiableOn.fun_neg ?_
    refine DifferentiableOn.fun_sum fun j _ => ?_
    exact (hM i _).mul (hinv j ⟨k, h1⟩)
  · by_cases h2 : k = i
    · subst h2
      simp only [Lm, Matrix.of_apply, lt_irrefl, ↓reduceDIte, ↓reduceIte]
      fun_prop
    · simp only [Lm, Matrix.of_apply, h1, ↓reduceDIte, h2, ↓reduceIte]
      fun_prop
end ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
