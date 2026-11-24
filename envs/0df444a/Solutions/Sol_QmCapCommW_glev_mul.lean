-- Prove2me | solution 1 for QmCapCommW.glev_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:55:21.797256+00:00
-- url     : https://prove2.me/submissions/71596195-9668-42b7-9272-d3b8ad20df3b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_CapelliOperatorCongruence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
noncomputable section
open QmCapCommW
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace QmCapCommW
theorem _root_.solution {k r : ℕ} {i : Fin (r + 1)} {g h : Mx k r} (hg : g ∈ Glev k r i) (hh : h ∈ Glev k r i) :
    g * h ∈ Glev k r i := by
  simp only [Glev, UH, Set.mem_setOf_eq] at hg hh ⊢
  obtain ⟨hg1, hg2⟩ := hg
  obtain ⟨hh1, hh2⟩ := hh
  refine ⟨?_, fun a ha => ⟨?_, ?_⟩⟩
  · rw [Matrix.conjTranspose_mul]
    calc hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [hg1, hh1]
  · rw [← Matrix.mulVec_mulVec, (hh2 a ha).1, (hg2 a ha).1]
  · rw [← Matrix.mulVec_mulVec, (hh2 a ha).2, (hg2 a ha).2]
end QmCapCommW
