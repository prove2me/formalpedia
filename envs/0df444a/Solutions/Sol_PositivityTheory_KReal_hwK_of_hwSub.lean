-- Prove2me | solution 1 for PositivityTheory.KReal.hwK_of_hwSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:35:16.824321+00:00
-- url     : https://prove2.me/submissions/a5e79369-63f4-4091-8cb3-62a72b4fe2dd

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
import Theorems.Thm_PI_FockOneDegW_Swap_mem_hwSub_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
variable {p q r s : ℕ}
namespace PositivityTheory.KReal
theorem _root_.solution {m n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {act : Mat m n →ₗ[ℂ] Module.End ℂ V}
    {μ : Ix m n → ℚ} {v : V} : v ∈ hwSub act μ ↔ HwK (units act) μ v :=
  PI.FockOneDegW.Swap.mem_hwSub_iff act μ v
end PositivityTheory.KReal
