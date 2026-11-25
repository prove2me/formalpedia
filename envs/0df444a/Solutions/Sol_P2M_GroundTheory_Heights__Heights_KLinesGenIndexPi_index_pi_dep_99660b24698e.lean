-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesGenIndexPi_index_pi_dep_99660b24698e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:00:35.232354+00:00
-- url     : https://prove2.me/submissions/45422f56-756c-4239-b2aa-d1d2e0b631d5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesGenIndexPi

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
open GroundTheory.Heights₂.Heights.KLinesGenIndexPi
open AddSubgroup
variable {η : Type} {G : Type} [AddCommGroup G]
namespace GroundTheory.Heights₂.Heights.KLinesGenIndexPi
theorem _root_.solution [Fintype η] {β : η → Type} [∀ i, AddCommGroup (β i)]
    (H : ∀ i, AddSubgroup (β i)) :
    (AddSubgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  simp_rw [AddSubgroup.index, ← Nat.card_pi]
  refine Nat.card_congr
    ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientAddGroup.leftRel_pi]
end GroundTheory.Heights₂.Heights.KLinesGenIndexPi
