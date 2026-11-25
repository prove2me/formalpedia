-- Prove2me | solution 1 for P2M_PI_MirrorSection__pair_lt_5ab1db9d22d9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:46:54.239586+00:00
-- url     : https://prove2.me/submissions/92531107-b7fc-4111-8899-a2dcc9d13cba

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_HpkRowEsI
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_IsMonomialConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_Forward
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_MirrorDecompOf
import Theorems.Thm_P2M_PI_MirrorSection__lt_inv_ad263186a75e
import Theorems.Thm_P2M_PI_MirrorSection__ut_conjTranspose_65da1bf78ca4


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
theorem _root_.solution {m : ℕ} {P b u' : Matrix (Fin m) (Fin m) ℂ} (hb : b ∈ UTset m) (h : bᴴ * P * u' = P)
    (hP : IsUnit P.det) : P * u' * P⁻¹ ∈ LTset m := by
  have iL := lt_inv (ut_conjTranspose hb)
  have e : P * u' * P⁻¹ = (bᴴ)⁻¹ := by
    calc P * u' * P⁻¹ = (bᴴ)⁻¹ * (bᴴ * P * u') * P⁻¹ := by
          rw [show (bᴴ)⁻¹ * (bᴴ * P * u') = ((bᴴ)⁻¹ * bᴴ) * P * u' by simp only [Matrix.mul_assoc], iL.2.1,
            Matrix.one_mul]
      _ = (bᴴ)⁻¹ := by rw [h, Matrix.mul_assoc, mul_nonsing_inv P hP, Matrix.mul_one]
  rw [e]; exact iL.2.2
end PI.MirrorSection₂
