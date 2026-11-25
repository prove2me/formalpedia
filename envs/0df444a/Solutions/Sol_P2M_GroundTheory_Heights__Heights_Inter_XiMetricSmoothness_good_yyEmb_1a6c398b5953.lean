-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_good_yyEmb_1a6c398b5953
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:31:26.753196+00:00
-- url     : https://prove2.me/submissions/adc27fa9-4d60-4b56-ae2f-2487e6e77fde

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
theorem _root_.solution {z : (Σ k, S.WIdx k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (j : Fin 2) :
    ∀ k, ∃ i, (fun p => z (T.yyEmb j p)) ⟨k, i⟩ ≠ 0 := by
  intro k
  rcases k with _ | _ | _
  · exact hz .base
  · exact hz .det
  · fin_cases j
    · obtain ⟨i, hi⟩ := hz .line0
      exact ⟨i, by simpa [T.yyEmb] using hi⟩
    · obtain ⟨i, hi⟩ := hz .line1
      exact ⟨i, by simpa [T.yyEmb] using hi⟩
end GroundTheory.Heights₂.Heights.Inter.XiMetricSmoothness
