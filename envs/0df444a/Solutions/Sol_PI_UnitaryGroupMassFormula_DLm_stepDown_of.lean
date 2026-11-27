-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DLm.stepDown_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:21:00.514195+00:00
-- url     : https://prove2.me/submissions/5f8775bf-4756-4b57-93b1-a3543268290e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_DensLemmaOfCut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.DLm
namespace PI.UnitaryGroupMassFormula.DLm
theorem _root_.solution (CV : ℕ) (hR : RunExists) (hJ : DownJ CV) (hT : DownTop CV) (hA : StepAdm CV) :
    StepDown CV := by
  intro m ih k r Wp Wq _ _ _ _ _ _ D A ε mm F' γ μR θ hH hr hε hA' hmm hF hs hJ0 hrel hG hz hθ hi
  by_cases h0 : zc D γ = 0
  · exact ih k r Wp Wq D A ε mm F' γ μR θ hH hr hε hA' hmm hF hs hJ0 hrel hG (by omega) hθ hi
  · obtain ⟨i, j, hij⟩ := hR k r Wp Wq D γ hG (by omega)
    have hy : Hyps CV D A ε mm F' := ⟨hr, hε, hA', hmm, hF, hs, hJ0⟩
    rcases Nat.lt_or_ge j (r + 1) with hj | hj
    · exact hJ hA m ih k r Wp Wq D A ε mm F' γ μR θ i j hH hy hrel hG hz hij (by omega) hθ hi
    · have hjr : j = r + 1 := le_antisymm hij.2.2.1 hj
      subst hjr
      exact hT hA m ih k r Wp Wq D A ε mm F' γ μR θ i hH hy hrel hG hz hij hθ hi
end PI.UnitaryGroupMassFormula.DLm
