-- Prove2me | solution 1 for PIW.FdPA.chartNorm_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:32:09.253976+00:00
-- url     : https://prove2.me/submissions/a793c0c5-e3e1-4199-b2cc-64dbf540077e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_ZnNonneg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_Frames
import Theorems.Thm_PIW_FdPA_opN_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PIW PIW.FdPA
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex Metric
open scoped ComplexConjugate
noncomputable section
namespace PIW.FdPA
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] : ZnSmul E := by
  intro r X t Z
  unfold Data.zN
  have h : ∀ τ, Data.opN (Matrix.of ((t • Z) τ)) = ‖t‖ * Data.opN (Matrix.of (Z τ)) := by
    intro τ
    rw [← opN_smul]
    rfl
  simp only [h]
  rw [Real.mul_iSup_of_nonneg (norm_nonneg t)]
end PIW.FdPA
