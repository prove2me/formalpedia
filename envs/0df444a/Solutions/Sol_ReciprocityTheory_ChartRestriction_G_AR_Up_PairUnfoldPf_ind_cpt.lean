-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.ind_cpt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:48:54.808381+00:00
-- url     : https://prove2.me/submissions/ab4bf4c1-35b0-46cc-b7b8-7db9a41c0011

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPfB
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
  {x0 : Frame X.Ψ r} (D : ExtFPf.LUData X x0) (FF : Set (V (nd X)))
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
theorem _root_.solution {z : V (nd X)} (hz : z ∈ OmF X x0) {M : Type*} [One M] [Zero M] :
    (T D FF).indicator (1 : Frame X.Ψ r → M) (cpt X x0 z) = FF.indicator 1 z := by
  have hb : (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) ∈ Bor X.Ψ r := by
    refine fun τ => ⟨?_, fun a c hca => ?_⟩
    · show Matrix.det (1 : Matrix (Fin r) (Fin r) ℂ) ≠ 0
      simp
    · exact Matrix.one_apply_ne hca.ne'
  have h1 : rmul (cpt X x0 z) (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)) = cpt X x0 z := by
    funext τ
    first
      | exact Matrix.mul_one _
      | simp [ReciprocityTheory.ChartRestriction.G.FD.rmul, ReciprocityTheory.ChartRestriction.G.FD.mat]
  obtain ⟨hΔ, hzz, -⟩ := D.uniq z hz _ hb
  rw [h1] at hΔ hzz
  have hiff : cpt X x0 z ∈ T D FF ↔ z ∈ FF := by
    constructor
    · intro h
      have h' : D.zOf (cpt X x0 z) ∈ FF := h.2.2
      rw [hzz] at h'
      exact h'
    · intro h
      show _ ∧ _ ∧ _
      refine ⟨hz, hΔ, ?_⟩
      rw [hzz]
      exact h
  by_cases hF : z ∈ FF
  · rw [Set.indicator_of_mem (hiff.2 hF), Set.indicator_of_mem hF]
    rfl
  · first
      | rw [Set.indicator_of_notMem (fun h => hF (hiff.1 h)), Set.indicator_of_notMem hF]
      | rw [Set.indicator_of_not_mem (fun h => hF (hiff.1 h)), Set.indicator_of_not_mem hF]
end ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
