-- Prove2me | solution 1 for P2M_PositivityTheory_KReal_le_genG__33d9f57319d5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:09:52.952627+00:00
-- url     : https://prove2.me/submissions/f9d9dcdc-540f-4853-868e-39af13ec859f

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasGl
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreMain

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
variable {r s : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.KReal
theorem _root_.solution (act : Mat r s →ₗ[ℂ] Module.End ℂ M) (S : Submodule ℂ M) : S ≤ genG act S :=
  le_sInf fun _ hN => hN.1
end PositivityTheory.KReal
