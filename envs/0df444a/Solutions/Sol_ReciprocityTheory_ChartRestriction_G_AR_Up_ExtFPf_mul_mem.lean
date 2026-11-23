-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:20:51.308253+00:00
-- url     : https://prove2.me/submissions/3b8124b0-c6d7-4f4c-a9c0-8c6fe90cd09b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_upper_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r)
private lemma mem_bor_iff' {Ψ : Finset (E →+* ℂ)} {b : Frame Ψ r} :
    b ∈ Bor Ψ r ↔ ∀ τ : Ψ, (mat b τ).det ≠ 0 ∧ ∀ a c : Fin r, c < a → b τ a c = 0 :=
  Iff.rfl
private lemma mat_rmul' {Ψ : Finset (E →+* ℂ)} (x b : Frame Ψ r) (τ : Ψ) :
    mat (rmul x b) τ = mat x τ * mat b τ :=
  rfl
variable {X} {x0 : Frame X.Ψ r} (D : LUData X x0)
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
theorem _root_.solution {b b' : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (hb' : b' ∈ Bor X.Ψ r) :
    rmul b b' ∈ Bor X.Ψ r := by
  rw [mem_bor_iff']
  intro τ
  refine ⟨?_, ?_⟩
  · rw [mat_rmul', Matrix.det_mul]
    exact mul_ne_zero (mem_bor_iff'.1 hb τ).1 (mem_bor_iff'.1 hb' τ).1
  · refine (upper_iff X _ τ).2 ?_
    rw [mat_rmul']
    exact ((upper_iff X b τ).1 (mem_bor_iff'.1 hb τ).2).mul ((upper_iff X b' τ).1 (mem_bor_iff'.1 hb' τ).2)
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
