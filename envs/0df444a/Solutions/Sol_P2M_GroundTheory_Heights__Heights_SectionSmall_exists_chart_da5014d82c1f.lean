-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionSmall_exists_chart_da5014d82c1f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:15:01.616247+00:00
-- url     : https://prove2.me/submissions/770b1575-5062-4858-91a2-93af3f3942c7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PSectionSmall

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
open GroundTheory.Heights₂.Heights.SectionSmall
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights.SectionSmall
theorem _root_.solution {P : ArithVariety n} {z : Cone n ℂ} (hz : z ∈ P.points ℂ) :
    ∃ c : (k : ι) → Fin (n k + 1), ∀ k, z k (c k) ≠ 0 := by
  have h : ∀ k, ∃ i, z k i ≠ 0 := fun k ↦ Function.ne_iff.mp (hz.1 k)
  choose c hc using h
  exact ⟨c, hc⟩
end GroundTheory.Heights₂.Heights.SectionSmall
