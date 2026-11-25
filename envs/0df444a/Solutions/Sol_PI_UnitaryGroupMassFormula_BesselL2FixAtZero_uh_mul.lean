-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BesselL2FixAtZero.uh_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:37:45.3467+00:00
-- url     : https://prove2.me/submissions/da3cd722-417b-4f2d-9ac6-8fa0972bb05c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselL2FixAtZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselSquareIntegrable_SigmaMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.BesselL2FixAtZero
open MeasureTheory Matrix
open scoped InnerProductSpace
open PI.UpqRep PI.BesselL2FixAtZero
namespace PI.UnitaryGroupMassFormula.BesselL2FixAtZero
theorem _root_.solution {k r : ℕ} {a b : Mat k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hb : b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : a * b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
  have hb' : bᴴ * Formalism.QuantumDeterminants.Hpk k r * b = Formalism.QuantumDeterminants.Hpk k r := hb
  show (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = Formalism.QuantumDeterminants.Hpk k r
  have e : (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * b := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e, ha', hb']
end PI.UnitaryGroupMassFormula.BesselL2FixAtZero
