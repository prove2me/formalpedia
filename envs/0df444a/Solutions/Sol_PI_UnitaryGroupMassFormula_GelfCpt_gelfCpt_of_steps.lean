-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.GelfCpt.gelfCpt_of_steps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:40:25.413168+00:00
-- url     : https://prove2.me/submissions/3c53c0c2-b6c4-48e8-bce5-40ee4249c2cd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGelfandAverage_AvgStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGelfandAverage_GelfCptOfSteps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.GelfCpt
open MeasureTheory Matrix
namespace PI.UnitaryGroupMassFormula.GelfCpt
theorem _root_.solution (hAvg : AvgStep) (hMul : MulStep) (hSpan : PI.UMultOne.IntSpan)
    (hConv : PI.UMultOne.ConvComm) : PI.UMultOne.GelfandCompact := by
  intro G _ _ _ _ _ _ H τ hH hτc hτa hτi hτH N ρ hc hirr A B hA hB
  borelize G
  let μ : Measure G := Measure.haar
  obtain ⟨a, ha, hAa⟩ := hSpan G μ N ρ hc hirr A
  obtain ⟨b, hb, hBb⟩ := hSpan G μ N ρ hc hirr B
  have eA : A = intMat μ ρ a := by ext i j; exact hAa i j
  have eB : B = intMat μ ρ b := by ext i j; exact hBb i j
  subst eA eB
  obtain ⟨a', ha'c, ha'i, ea'⟩ := hAvg G μ H hH N ρ hc a ha hA
  obtain ⟨b', hb'c, hb'i, eb'⟩ := hAvg G μ H hH N ρ hc b hb hB
  rw [← ea', ← eb', hMul G μ N ρ hc a' b' ha'c hb'c, hMul G μ N ρ hc b' a' hb'c ha'c]
  congr 1
  funext z
  exact hConv G μ H τ hτc hτa hτi hτH a' b' ha'c hb'c ha'i hb'i z
end PI.UnitaryGroupMassFormula.GelfCpt
