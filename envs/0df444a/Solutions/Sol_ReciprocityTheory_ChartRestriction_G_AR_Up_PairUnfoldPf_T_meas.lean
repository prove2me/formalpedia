-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.T_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:56:06.965623+00:00
-- url     : https://prove2.me/submissions/601b61ba-f056-4865-901f-ea15473380ce

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPfA
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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
variable {X} {x0 : Frame X.Ψ r} (D : ExtFPf.LUData X x0) (FF : Set (V (nd X)))
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
theorem _root_.solution (hFF : MeasurableSet FF) : MeasurableSet (T D FF) := by
  have hdom : IsOpen X.dom := by
    have hc : ∀ (τ : X.Ψ) (i : Fin (r + 1)), Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
      intro τ i
      unfold dmin lminor
      refine (Continuous.matrix_submatrix ?_ _ _).matrix_det
      refine continuous_matrix fun a b => ?_
      simp only [gram, hermC, col, mat, Matrix.of_apply]
      fun_prop
    have hm : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => (mat x τ).det := fun τ =>
      Continuous.matrix_det (continuous_apply τ)
    have he : X.dom = ⋂ τ : X.Ψ, ({x | (mat x τ).det ≠ 0} ∩
        ⋂ i : Fin (r + 1), {x | 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}) := by
      ext x
      simp [GG]
    rw [he]
    exact isOpen_iInter_of_finite fun τ => (isOpen_ne_fun (hm τ) continuous_const).inter
      (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const
        (continuous_const.mul (Complex.continuous_re.comp (hc τ i))))
  classical
  let U : Set (Frame X.Ψ r) := {x | x ∈ X.dom ∧ D.Δ x ≠ 0}
  have hU : IsOpen U := hdom.inter (isOpen_ne_fun D.hΔ.continuous continuous_const)
  have hg : Measurable (U.piecewise D.zOf fun _ => 0) :=
    D.hz.continuousOn.measurable_piecewise continuousOn_const hU.measurableSet
  have hT : T D FF = U ∩ (U.piecewise D.zOf fun _ => 0) ⁻¹' FF := by
    ext x
    simp only [T, U, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, by rw [Set.piecewise_eq_of_mem _ _ _ (show x ∈ U from ⟨h1, h2⟩)]; exact h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      rw [Set.piecewise_eq_of_mem _ _ _ (show x ∈ U from ⟨h1, h2⟩)] at h3
      exact ⟨h1, h2, h3⟩
  rw [hT]
  exact hU.measurableSet.inter (hg hFF)
end ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
