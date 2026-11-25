-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_blockIncl_injective_ce1f2084d84c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:25:40.907166+00:00
-- url     : https://prove2.me/submissions/c320b534-b806-490d-83f9-e0f8e6d217cf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_VarsSubsetRangeBlockIncl

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
omit [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (k₀ : ι) : Function.Injective (blockIncl (n := n) k₀) := by
  rintro ⟨⟨⟩, i⟩ ⟨⟨⟩, j⟩ h
  simp only [blockIncl, Sigma.mk.injEq, heq_eq_eq, true_and] at h
  subst h; rfl
end GroundTheory.Heights₂.Heights
