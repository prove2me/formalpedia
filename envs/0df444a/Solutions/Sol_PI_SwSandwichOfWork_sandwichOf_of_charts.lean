-- Prove2me | solution 1 for PI.SwSandwichOfWork.sandwichOf_of_charts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:28:52.318573+00:00
-- url     : https://prove2.me/submissions/204c8d12-b59d-472a-954f-2b4691afd54e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LongWeylElementSquare
import Definitions.Def_Formalism_PeriodIntegrals_SwSand
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_SandwichOfOfCharts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology Classical
open scoped ENNReal NNReal
open PI PI.SwSandwichOfWork
open PI.SwBig PI.SwSand
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra
namespace PI.SwSandwichOfWork
theorem _root_.solution (h0 : NormRL) (h1 : LogG) (h2 : ChartFwdOf) (h3 : ChartBwdOf)
    (h4 : SideB) (h5 : SideA) : SandwichOf := by
  intro hLieG hLieWb hGauss hPhiForm hBig hPhiDeriv hLIso hW0 hLieEN hExpN
  have hF : ChartFwd := h2 h0 h1 hW0 hBig hPhiForm hPhiDeriv hLieWb hExpN hLIso
  have hB : ChartBwd := h3 h0 h1 hW0 hBig hPhiForm hPhiDeriv hLieWb hExpN hLIso
  intro k r ε hε hε1
  obtain ⟨δ₁, hδ₁, hB'⟩ := h4 h0 hLieG hLieWb hPhiForm hLieEN hLIso hF k r ε hε hε1
  obtain ⟨δ₂, hδ₂, hA'⟩ := h5 h0 hLieG hLieWb hGauss hPhiForm hW0 hLieEN hExpN hLIso hB k r ε hε hε1
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro ρ hρ hρδ n c m n' hn hm hn'
  exact ⟨hA' ρ hρ (lt_of_lt_of_le hρδ (min_le_right _ _)) n c m n' hn hm hn',
    hB' ρ hρ (lt_of_lt_of_le hρδ (min_le_left _ _)) n c m n' hn hm hn'⟩
end PI.SwSandwichOfWork
