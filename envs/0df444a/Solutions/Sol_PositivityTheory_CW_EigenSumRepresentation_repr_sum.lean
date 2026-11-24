-- Prove2me | solution 1 for PositivityTheory.CW.EigenSumRepresentation.repr_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:50:44.76451+00:00
-- url     : https://prove2.me/submissions/f8dd6678-40a6-4c77-9f8b-f0724575bd35

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
theorem _root_.solution {b : Module.Basis ι ℂ V} (T : Finset ι) (y : V) (hy : (b.repr y).support ⊆ T) :
    y = ∑ j ∈ T, b.repr y j • b j := by
  conv_lhs => rw [← b.linearCombination_repr y]
  rw [Finsupp.linearCombination_apply]
  exact Finsupp.sum_of_support_subset _ hy _ (fun i _ => zero_smul ℂ (b i))
end PositivityTheory.CW.EigenSumRepresentation
