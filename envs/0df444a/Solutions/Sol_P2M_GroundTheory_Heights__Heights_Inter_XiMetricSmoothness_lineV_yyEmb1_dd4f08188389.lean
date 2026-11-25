-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_lineV_yyEmb1_dd4f08188389
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:30:46.675252+00:00
-- url     : https://prove2.me/submissions/3a23c11c-f959-4916-99af-655e9cdd49d7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PXiMetric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
open scoped ComplexOrder
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.XiMetricSmoothness
variable {D : ℕ} (S : ProjectiveLineBundle D) {N : ℕ} {F : S.ι → S.ν → S.κ → S.κ → MRing S.YIdx} {q : ℕ}
  {r : Fin q → MRing S.YIdx} {b : Fin q → T.YBlk → ℕ}
namespace GroundTheory.Heights₂.Heights.Inter.XiMetricSmoothness
theorem _root_.solution (z : (Σ k, S.WIdx k) → ℂ) :
    lineV (fun p => z (T.yyEmb 1 p)) = fun k : S.κ => z ⟨.line1, k⟩ := by
  funext k
  simp [lineV, T.yyEmb]
end GroundTheory.Heights₂.Heights.Inter.XiMetricSmoothness
