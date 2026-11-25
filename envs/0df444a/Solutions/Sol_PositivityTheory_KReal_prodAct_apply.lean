-- Prove2me | solution 1 for PositivityTheory.KReal.prodAct_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:34:50.667971+00:00
-- url     : https://prove2.me/submissions/44b766c0-bf3e-4666-a0d5-581a5249a88c

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreGraph

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
namespace PositivityTheory.KReal
theorem _root_.solution {p q : ℕ} {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (ρA : Mat p q →ₗ[ℂ] Module.End ℂ A) (ρB : Mat p q →ₗ[ℂ] Module.End ℂ B) (Z : Mat p q) (n : A × B) :
    prodAct ρA ρB Z n = (ρA Z n.1, ρB Z n.2) := rfl
end PositivityTheory.KReal
