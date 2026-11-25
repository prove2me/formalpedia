-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.sc_inLieP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:52:45.672676+00:00
-- url     : https://prove2.me/submissions/1227dbed-f22f-4a13-ae56-4fb95a69954a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_EntryLeLsz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost
namespace PI.UnitaryGroupMassFormula.UsCost
theorem _root_.solution {k j ρ : ℕ} {X : B.Mat k (j + ρ)} (hX : inLieP k j ρ X) : inLieP k j ρ (sc X) := by
  obtain ⟨h1, h2⟩ := hX
  have hs : star ((((lsz X)⁻¹ : ℝ) : ℂ)) = (((lsz X)⁻¹ : ℝ) : ℂ) := Complex.conj_ofReal _
  refine ⟨?_, fun i b hb hi => ?_⟩
  · unfold B.inLie at h1 ⊢
    unfold sc
    rw [Matrix.conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1, smul_zero]
  · have e : sc X i b = (((lsz X)⁻¹ : ℝ) : ℂ) * X i b := rfl
    rw [e, h2 i b hb hi, mul_zero]
end PI.UnitaryGroupMassFormula.UsCost
