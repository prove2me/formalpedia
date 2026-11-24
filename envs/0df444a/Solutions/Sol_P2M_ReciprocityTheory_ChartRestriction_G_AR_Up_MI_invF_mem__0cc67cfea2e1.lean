-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_invF_mem__0cc67cfea2e1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:31.132269+00:00
-- url     : https://prove2.me/submissions/df745f12-f704-40c4-a280-7f069e764087

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) : invF X b ∈ Bor X.Ψ r := by
  simp only [Bor, Set.mem_setOf_eq] at hb ⊢
  intro τ
  obtain ⟨hd, hup⟩ := hb τ
  have hu : (mat b τ).BlockTriangular id := fun a c h => hup a c h
  letI := (mat b τ).invertibleOfIsUnitDet (isUnit_iff_ne_zero.2 hd)
  have hinv := Matrix.blockTriangular_inv_of_blockTriangular hu
  refine ⟨?_, fun a c h => hinv h⟩
  intro h0
  have h1 := Matrix.det_mul (mat b τ) (mat b τ)⁻¹
  rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd), Matrix.det_one] at h1
  have h0' : ((mat b τ)⁻¹).det = 0 := h0
  rw [h0', mul_zero] at h1
  exact one_ne_zero h1
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
