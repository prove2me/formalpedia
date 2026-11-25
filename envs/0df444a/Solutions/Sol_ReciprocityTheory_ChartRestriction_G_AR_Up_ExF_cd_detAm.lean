-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.cd_detAm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:00:22.421712+00:00
-- url     : https://prove2.me/submissions/6db05479-e430-4e27-b20f-dbe3d023c340

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_cd_Am_entry
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
open NumberField Complex Matrix Topology Filter ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD ReciprocityTheory.ChartRestriction.G.AR.Up.ExhE
open scoped ComplexConjugate ComplexOrder ContDiff
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
private lemma cd_det_lemma {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {k : ℕ} {M : F → Matrix (Fin k) (Fin k) ℂ}
    (h : ∀ i j, ContDiff 𝕜 ∞ fun z => M z i j) : ContDiff 𝕜 ∞ fun z => (M z).det := by
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => h _ _)
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
open NumberField Complex Matrix Topology Filter ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD ReciprocityTheory.ChartRestriction.G.AR.Up.ExhE
open scoped ComplexConjugate ComplexOrder ContDiff
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
theorem _root_.solution (τ : X.Ψ) : ContDiff ℝ ∞ fun z : V (nd X) => (Am X z τ).det := by
  exact cd_det_lemma (M := fun z : V (nd X) => Am X z τ) fun a c => cd_Am_entry X τ a c
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
