-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.phiF_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:21:45.188674+00:00
-- url     : https://prove2.me/submissions/c74d0456-4949-40d0-ac0d-f87cd5cc9e02

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE
open NumberField Complex Matrix Topology Filter MeasureTheory Set ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB
  ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS
open scoped ComplexConjugate ContDiff ENNReal
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE
theorem _root_.solution {f0 : Frame X.Ψ r → ℂ} {W : Frame X.Ψ r → ℝ≥0∞} (hf : ContinuousOn f0 X.dom)
    (hW : Measurable W) : Measurable (phiF X f0 W) := by
  classical
  have hopen : IsOpen X.dom := by
    have h1 : X.dom = ⋂ τ : X.Ψ, ({x : Frame X.Ψ r | (mat x τ).det ≠ 0} ∩
        ⋂ i : Fin (r + 1), {x | 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}) := by
      ext x
      simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]
      rfl
    rw [h1]
    refine isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
    · refine isOpen_ne_fun ?_ continuous_const
      unfold mat
      fun_prop
    · refine isOpen_lt continuous_const ?_
      unfold dmin lminor ReciprocityTheory.ChartRestriction.G.FD.gram ReciprocityTheory.ChartRestriction.G.FD.hermC ReciprocityTheory.ChartRestriction.G.FD.col mat
      fun_prop
  unfold phiF
  refine Measurable.mul ?_ hW
  refine ContinuousOn.measurable_piecewise ?_ continuousOn_const hopen.measurableSet
  exact ENNReal.continuous_ofReal.comp_continuousOn (hf.norm.pow 2)
end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE
