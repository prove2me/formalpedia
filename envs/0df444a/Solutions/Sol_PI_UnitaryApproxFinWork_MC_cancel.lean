-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.MC_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:33:49.214238+00:00
-- url     : https://prove2.me/submissions/1d6b10f1-f6a9-4fa6-8a48-13cd99312124

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_MemIntOEOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_SigmaMemIntOE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open PI PI.UnitaryApproxFinWork
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {n : Type} [Fintype n] [DecidableEq n]
variable {v : HeightOneSpectrum (𝓞 F)}
namespace PI.UnitaryApproxFinWork
theorem _root_.solution {c e : 𝓞 F} (hc : c ≠ 0) {M A : Matrix n n (E ⊗[F] v.adicCompletion F)}
    (h : dv E v c • M = dv E v (c * e) • A) : M = dv E v e • A := by
  have hx : algebraMap F E (c : F) ≠ 0 := by simpa using hc
  have hu : IsUnit (dv E v c) :=
    (IsUnit.mk0 _ hx).map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F))
  have hmul : dv E v (c * e) = dv E v c * dv E v e := by simp [dv]
  rw [hmul, mul_smul] at h
  exact hu.smul_left_cancel.1 h
end PI.UnitaryApproxFinWork
