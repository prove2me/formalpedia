-- Prove2me | solution 1 for PositivityTheory.CW.EigenSumRepresentation.eig_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:24:50.511954+00:00
-- url     : https://prove2.me/submissions/adab8483-f42e-4320-95b6-f8bcba9e5f11

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
theorem _root_.solution {E : Fin n → Fin n → Module.End ℂ V} {b : Module.Basis ι ℂ V} {μ : ι → ℝ}
    (heig : ∀ i, Eig ε E (μ i) (b i)) (s : Finset ι) (c : ι → ℂ) (ν : ℝ) (hs : ∀ j ∈ s, μ j = ν) :
    Eig ε E ν (∑ j ∈ s, c j • b j) := by
  unfold Eig
  rw [map_sum, smul_sum]
  refine sum_congr rfl fun j hj => ?_
  rw [map_smul, show casimirK ε E (b j) = _ from heig j, hs j hj, smul_comm]
end PositivityTheory.CW.EigenSumRepresentation
