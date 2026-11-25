-- Prove2me | solution 1 for PositivityTheory.CW.EigenspaceOrthogonality.beta_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:24:39.688692+00:00
-- url     : https://prove2.me/submissions/f3b787e5-dac6-4244-9bbd-bff3db025864

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_EigenspacesOrthogonalOfCalculus

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
open PositivityTheory.CW.EigenspaceOrthogonality
variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {A : Module.End ℂ V}
namespace PositivityTheory.CW.EigenspaceOrthogonality
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → V) (w : V) :
    beta ε E A (∑ i ∈ s, f i) w = ∑ i ∈ s, beta ε E A (f i) w := by
  simp only [beta, map_sum, sum_inner]
  exact Finset.sum_comm
end PositivityTheory.CW.EigenspaceOrthogonality
