-- Prove2me | solution 1 for PositivityTheory.CW.CompactGroupFacts.compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:37:07.888503+00:00
-- url     : https://prove2.me/submissions/a7033193-b0a8-46b0-a1ae-5ac7ecb79296

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IsInLieAlgebraISmulAddConjTranspose
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_GroupFactsHolds
import Theorems.Thm_PositivityTheory_CW_CompactGroupFacts_hilbert_schmidt_continuous
import Theorems.Thm_PositivityTheory_CW_CompactGroupFacts_isClosed_UJ
import Theorems.Thm_PositivityTheory_CW_CompactGroupFacts_entry_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.CompactGroupFacts
variable {n : ℕ}
namespace PositivityTheory.CW.CompactGroupFacts
theorem _root_.solution (ε : Fin n → Bool) (ρ : ℝ) : IsCompact {g | g ∈ UJset ε ∧ hs2 g ≤ ρ} := by
  let K : Set (Fin n → Fin n → ℂ) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) (Real.sqrt ρ)
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hK.of_isClosed_subset ((isClosed_UJ ε).inter (isClosed_le hilbert_schmidt_continuous continuous_const)) ?_
  rintro g ⟨-, hg⟩ i - j -
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact Real.le_sqrt_of_sq_le ((entry_le g i j).trans hg)
end PositivityTheory.CW.CompactGroupFacts
