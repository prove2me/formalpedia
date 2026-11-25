-- Prove2me | solution 1 for PositivityTheory.KReal.self_mem_cycK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:26:10.106048+00:00
-- url     : https://prove2.me/submissions/d162e698-6d26-4b6e-a517-4a7bbe8827c5

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
    f ∈ cycK ρ f := by
  exact Submodule.mem_sInf.2 fun N hN => hN.1
end PositivityTheory.KReal
