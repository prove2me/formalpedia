-- Prove2me | solution 1 for PositivityTheory.KReal.kSt_cycK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:27:22.424392+00:00
-- url     : https://prove2.me/submissions/6250def7-5f66-46f8-95b9-bb1d1f4cec5f

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc

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
variable {r s : ℕ}
namespace PositivityTheory.KReal
theorem _root_.solution {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Ix r s → Ix r s → Module.End ℂ M) (f : M) :
    KSt ρ (cycK ρ f) := by
  intro a b hab x hx
  exact Submodule.mem_sInf.2 fun N hN => hN.2 a b hab x (Submodule.mem_sInf.1 hx N hN)
end PositivityTheory.KReal
