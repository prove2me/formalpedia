-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.MC_of_entries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:33:58.798177+00:00
-- url     : https://prove2.me/submissions/5c627cb1-bf36-4d85-ad98-ab19c323ad83

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
theorem _root_.solution {d : 𝓞 F} {M : Matrix n n (E ⊗[F] v.adicCompletion F)}
    (h : ∀ i j, Cong E v d (M i j)) : MC E v d M := by
  choose t ht heq using h
  refine ⟨Matrix.of fun i j => t i j, fun i j => ht i j, ?_⟩
  ext i j
  rw [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  exact heq i j
end PI.UnitaryApproxFinWork
