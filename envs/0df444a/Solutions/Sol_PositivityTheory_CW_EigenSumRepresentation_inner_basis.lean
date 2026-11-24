-- Prove2me | solution 1 for PositivityTheory.CW.EigenSumRepresentation.inner_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:51:07.699859+00:00
-- url     : https://prove2.me/submissions/d2b12622-361d-4aea-b377-dcb5cbb8f633

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
theorem _root_.solution {b : Module.Basis ι ℂ V} (hb : Orthonormal ℂ b) (i : ι) (y : V) :
    inner ℂ (b i) y = b.repr y i := by
  have h := hb.inner_right_finsupp (b.repr y) i
  rwa [b.linearCombination_repr] at h
end PositivityTheory.CW.EigenSumRepresentation
