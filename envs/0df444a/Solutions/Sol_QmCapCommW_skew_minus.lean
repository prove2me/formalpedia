-- Prove2me | solution 1 for QmCapCommW.skew_minus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:03:28.933856+00:00
-- url     : https://prove2.me/submissions/67b761be-ceb8-4c2a-bb92-04f8e48d52b6

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
theorem _root_.solution {n : ℕ} (H Z : Matrix (Fin n) (Fin n) ℂ) (hh : Hᴴ = H) (hHH : H * H = 1) :
    (Z - H * Zᴴ * H)ᴴ * H + H * (Z - H * Zᴴ * H) = 0 := by
  have e1 : (Z - H * Zᴴ * H)ᴴ = Zᴴ - H * Z * H := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hh, Matrix.mul_assoc H Z H]
  rw [e1, Matrix.sub_mul, Matrix.mul_sub]
  have e2 : H * Z * H * H = H * Z := by rw [Matrix.mul_assoc (H * Z) H H, hHH, Matrix.mul_one]
  have e3 : H * (H * Zᴴ * H) = Zᴴ * H := by
    rw [← Matrix.mul_assoc H (H * Zᴴ) H, ← Matrix.mul_assoc H H Zᴴ, hHH, Matrix.one_mul]
  rw [e2, e3]
  abel
end QmCapCommW
