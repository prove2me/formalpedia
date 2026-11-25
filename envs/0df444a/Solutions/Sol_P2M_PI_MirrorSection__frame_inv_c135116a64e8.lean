-- Prove2me | solution 1 for P2M_PI_MirrorSection__frame_inv_c135116a64e8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:46:50.883905+00:00
-- url     : https://prove2.me/submissions/47bef0b1-d964-4dd2-bcb2-73dcd5bb158f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_HpkRowEsI
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_IsMonomialConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_Forward
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_MirrorDecompOf

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
open PI PI.MirrorSection₂
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 PI.StabPairsW
variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
namespace PI.MirrorSection₂
theorem _root_.solution {s : Matrix n n ℂ} {x : Matrix m m ℂ} {F : Matrix n m ℂ}
    (hs : IsUnit s.det) (hx : IsUnit x.det) (h : s * F = F * x) : s⁻¹ * F = F * x⁻¹ := by
  calc s⁻¹ * F = s⁻¹ * (F * x * x⁻¹) := by rw [Matrix.mul_assoc F, mul_nonsing_inv x hx, Matrix.mul_one]
    _ = s⁻¹ * (s * F) * x⁻¹ := by rw [h]; simp only [Matrix.mul_assoc]
    _ = F * x⁻¹ := by rw [← Matrix.mul_assoc s⁻¹, nonsing_inv_mul s hs, Matrix.one_mul]
end PI.MirrorSection₂
