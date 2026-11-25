-- Prove2me | solution 1 for PositivityTheory.KReal.minusPart_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:45:37.210243+00:00
-- url     : https://prove2.me/submissions/464284fc-d866-4f88-981d-99d73c17d7ef

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreHarm
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreSplit

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
theorem _root_.solution {σ : Type} (A : Module.End ℂ (MvPolynomial σ ℂ)) {d : ℕ} (hd : d < 2)
    {Q : MvPolynomial σ ℂ} (hQ : Q ∈ homog σ d) : minusPart A Q = 0 := by
  unfold minusPart
  refine finsum_eq_zero_of_forall_eq_zero fun e => ?_
  rw [homogeneousComponent_of_mem hQ, if_neg (by omega), map_zero, map_zero]
end PositivityTheory.KReal
