-- Prove2me | solution 1 for P2M_PositivityTheory_KReal_genG_le__7406e1e366d6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:11:49.598121+00:00
-- url     : https://prove2.me/submissions/e628bdd1-5928-48e2-88ad-5845c76186c6

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
theorem _root_.solution {act : Mat r s →ₗ[ℂ] Module.End ℂ M} {S N : Submodule ℂ M} (h1 : S ≤ N)
    (h2 : ∀ W, ∀ x ∈ N, act W x ∈ N) : genG act S ≤ N :=
  sInf_le ⟨h1, h2⟩
end PositivityTheory.KReal
