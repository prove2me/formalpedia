-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.MC_entries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:33:55.075463+00:00
-- url     : https://prove2.me/submissions/d305463d-881a-462c-82e7-33967dc07e93

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
theorem _root_.solution {d : 𝓞 F} {M : Matrix n n (E ⊗[F] v.adicCompletion F)} (h : MC E v d M) (i j : n) :
    Cong E v d (M i j) := by
  obtain ⟨A, hA, rfl⟩ := h
  exact ⟨A i j, hA i j, by rw [Matrix.smul_apply, smul_eq_mul]⟩
end PI.UnitaryApproxFinWork
