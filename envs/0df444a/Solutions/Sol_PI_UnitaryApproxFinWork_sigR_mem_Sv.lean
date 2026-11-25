-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.sigR_mem_Sv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:39:53.957896+00:00
-- url     : https://prove2.me/submissions/3ba23d5d-99f8-4432-b3a4-760b9a9d45bc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_MemIntOEOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_SigmaMemIntOE
import Theorems.Thm_PI_UnitaryApproxFinWork_sigma_mem_intOE

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
theorem _root_.solution (σ : E →ₐ[F] E) {s : E ⊗[F] v.adicCompletion F} (hs : s ∈ Sv E v) :
    PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F) s ∈ Sv E v := by
  have h : Sv E v ≤ (Sv E v).comap (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F)) := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · simp only [Subring.coe_comap, Set.mem_preimage]
      apply Subring.subset_closure
      left
      exact ⟨⟨σ x, sigma_mem_intOE σ hx⟩, by simp [PI.UnitaryApproxDefs.sigR]⟩
    · simp only [Subring.coe_comap, Set.mem_preimage]
      apply Subring.subset_closure
      right
      exact ⟨⟨y, hy⟩, by simp [PI.UnitaryApproxDefs.sigR]⟩
  exact h hs
end PI.UnitaryApproxFinWork
