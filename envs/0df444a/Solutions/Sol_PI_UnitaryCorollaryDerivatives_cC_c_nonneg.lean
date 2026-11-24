-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.cC_c_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:56:31.722171+00:00
-- url     : https://prove2.me/submissions/cc67d1aa-0ebc-4d5e-b911-f0ba8fd43344

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CBLamnorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CCCNonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_pos
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open PI PI.UnitaryCorollaryDerivatives
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
open Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k j ρ : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace PI.UnitaryCorollaryDerivatives
theorem _root_.solution {r : ℕ} {A : ℝ} {m : ℕ} {f : B.Mat k r → E} {c : ℝ} (hf : B.CCle A m f c) : 0 ≤ c := by
  have h1 := Formalism.QuantumDeterminants.WeylGroupFacts.uh_one (k := k) (r := r)
  have h := hf.2 [] [] (by simp) (by simp) (by simp) 1 h1
  have hpos := gN_pos h1
  exact le_trans (mul_nonneg (Real.rpow_nonneg hpos.le _) (norm_nonneg _)) h
end PI.UnitaryCorollaryDerivatives
