-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.FibOrbAsmW.UH_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:45:25.885884+00:00
-- url     : https://prove2.me/submissions/545cabb3-d263-45e9-ab8a-9d10dcc0b1fe

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FibreOrbits_FibreOrbitOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FibOrbAsmW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace PI.UnitaryGroupMassFormula.FibOrbAsmW
theorem _root_.solution {H a b : Matrix ι ι ℂ} (ha : a ∈ UH H) (hb : b ∈ UH H) : a * b ∈ UH H := by
  have ha' : aᴴ * H * a = H := ha
  have hb' : bᴴ * H * b = H := hb
  show (a * b)ᴴ * H * (a * b) = H
  rw [conjTranspose_mul]
  calc bᴴ * aᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by simp only [Matrix.mul_assoc]
    _ = H := by rw [ha', hb']
end PI.UnitaryGroupMassFormula.FibOrbAsmW
