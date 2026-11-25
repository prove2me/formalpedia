-- Prove2me | solution 1 for P2M_PI_MirrorSection__pair_of_lt_a26c1bd2bfcb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:00:33.899013+00:00
-- url     : https://prove2.me/submissions/56e8e235-3326-4922-b829-67411fbfabaa

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_HpkRowEsI
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_IsMonomialConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_Forward
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_MirrorDecompOf
import Theorems.Thm_P2M_PI_MirrorSection__lt_conjTranspose_880787298ed1
import Theorems.Thm_P2M_PI_MirrorSection__lt_inv_ad263186a75e


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
variable {k r : ℕ}
namespace PI.MirrorSection₂
theorem _root_.solution {m : ℕ} {P a : Matrix (Fin m) (Fin m) ℂ} (hP : IsUnit P.det) (ha : P * a * P⁻¹ ∈ LTset m) :
    ∃ b, b ∈ UTset m ∧ bᴴ * P * a = P := by
  have iA := lt_inv ha
  refine ⟨((P * a * P⁻¹)⁻¹)ᴴ, lt_conjTranspose iA.2.2, ?_⟩
  rw [conjTranspose_conjTranspose]
  calc (P * a * P⁻¹)⁻¹ * P * a = (P * a * P⁻¹)⁻¹ * (P * a * P⁻¹) * P := by
        simp only [Matrix.mul_assoc]; rw [nonsing_inv_mul P hP, Matrix.mul_one]
    _ = P := by rw [iA.2.1, Matrix.one_mul]
end PI.MirrorSection₂
