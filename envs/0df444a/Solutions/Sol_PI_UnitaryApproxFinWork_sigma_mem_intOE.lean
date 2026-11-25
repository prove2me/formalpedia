-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.sigma_mem_intOE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:35:06.665225+00:00
-- url     : https://prove2.me/submissions/a4dc5d52-1aaa-467f-a3c0-eb2a0726f668

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
theorem _root_.solution (σ : E →ₐ[F] E) {x : E} (hx : x ∈ PI.UnitaryApproxDefs.intOE E) : σ x ∈ PI.UnitaryApproxDefs.intOE E := by
  simp only [PI.UnitaryApproxDefs.intOE, RingHom.mem_range] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  exact ⟨⟨σ y, (RingOfIntegers.isIntegral_coe y).map σ.toRingHom.toIntAlgHom⟩, rfl⟩
end PI.UnitaryApproxFinWork
