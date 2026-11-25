-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.measurableSet_SW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:03:39.618187+00:00
-- url     : https://prove2.me/submissions/c428a082-7b63-488c-b8ca-81aadf555af1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfI
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_isCompact_CmatSet
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_continuous_gramF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_continuous_gramTF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
private lemma isOpen_X_dom : IsOpen X.dom := by
  have e : X.dom = ⋂ τ : X.Ψ, ({x : Frame X.Ψ r | (mat x τ).det ≠ 0} ∩
      ⋂ i : Fin (r + 1), {x : Frame X.Ψ r | 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}) := by
    ext x
    simp [Data.dom, GG]
  rw [e]
  refine isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
  · have hm : Continuous fun x : Frame X.Ψ r => mat x τ := continuous_apply τ
    exact isOpen_ne_fun hm.matrix_det continuous_const
  · have hg : Continuous fun x : Frame X.Ψ r => gram τ.1 X.Gm (mat x τ) :=
      (continuous_apply τ).comp (continuous_gramF X)
    have hc : Continuous fun x : Frame X.Ψ r => (dmin X.Gm x τ i).re := by
      unfold dmin lminor
      exact Complex.continuous_re.comp (hg.matrix_submatrix _ _).matrix_det
    exact isOpen_lt continuous_const (continuous_const.mul hc)
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution : MeasurableSet (SW X) := by
  have e : SW X = X.dom ∩ gramF X ⁻¹' (gramTF X '' CmatSet X) := by
    ext y
    simp only [SW, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨h1, β, hβ, hg⟩
      exact ⟨h1, β, hβ, funext fun τ => (hg τ).symm⟩
    · rintro ⟨h1, β, hβ, hg⟩
      exact ⟨h1, β, hβ, fun τ => (congrFun hg τ).symm⟩
  rw [e]
  have h1 : MeasurableSet X.dom := (isOpen_X_dom X).measurableSet
  have h2 : IsClosed (gramF X ⁻¹' (gramTF X '' CmatSet X)) :=
    ((isCompact_CmatSet X).image (continuous_gramTF X)).isClosed.preimage (continuous_gramF X)
  exact h1.inter h2.measurableSet
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
