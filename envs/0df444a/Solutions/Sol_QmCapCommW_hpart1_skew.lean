-- Prove2me | solution 1 for QmCapCommW.hpart1_skew
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:10:47.968964+00:00
-- url     : https://prove2.me/submissions/2f06905b-681c-49c1-a782-a01f6428476a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_CapelliOperatorCongruence
import Theorems.Thm_QmCapCommW_skew_minus

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
    (hpart1 H Z)ᴴ * H + H * hpart1 H Z = 0 := by
  have hinv : H⁻¹ = H := Matrix.inv_eq_left_inv hHH
  unfold hpart1
  rw [hinv, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul]
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by
    have h1 := Complex.conj_ofReal (1 / 2 : ℝ)
    push_cast at h1
    exact h1
  rw [hs, ← smul_add, skew_minus H Z hh hHH, smul_zero]
end QmCapCommW
