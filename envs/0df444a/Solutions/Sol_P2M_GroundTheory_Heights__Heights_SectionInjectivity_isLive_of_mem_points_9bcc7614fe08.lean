-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionInjectivity_isLive_of_mem_points_9bcc7614fe08
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:15:30.399283+00:00
-- url     : https://prove2.me/submissions/1cfa0cc4-872d-4a29-a27c-fcb89f8515e2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroMore

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.SectionInjectivity
set_option linter.unusedSectionVars false
namespace GroundTheory.Heights₂.Heights.SectionInjectivity
theorem _root_.solution {P : ArithVariety n} {z : Cone n ℂ} (hz : z ∈ P.points ℂ)
    {c : (k : ι) → Fin (n k + 1)} (hc : ∀ k, z k (c k) ≠ 0) :
    ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal := fun k hk ↦
  hc k (by simpa [evalCone] using hz.2 _ hk)
end GroundTheory.Heights₂.Heights.SectionInjectivity
