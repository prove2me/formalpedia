-- Prove2me | solution 1 for PositivityTheory.CW.EigenSumRepresentation.beta_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:24:47.777785+00:00
-- url     : https://prove2.me/submissions/b8a3d280-fac8-41d1-ad11-7daafe950fbc

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_WordFiltrationCommute

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
open PositivityTheory.CW.EigenSumRepresentation
variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type}
namespace PositivityTheory.CW.EigenSumRepresentation
theorem _root_.solution {E : Fin n → Fin n → Module.End ℂ V} (A : Module.End ℂ V) {κ : Type} (s : Finset κ) (v : κ → V) :
    beta ε E A (∑ k ∈ s, v k) (∑ k ∈ s, v k) = ∑ l ∈ s, ∑ k ∈ s, beta ε E A (v k) (v l) := by
  simp only [beta, map_sum, sum_inner, inner_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]
end PositivityTheory.CW.EigenSumRepresentation
