-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.tensor_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:35:11.120388+00:00
-- url     : https://prove2.me/submissions/986089a9-3239-4e1d-9139-c07d0a18462c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_MemIntOEOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_ApproxE

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
namespace PI.UnitaryApproxFinWork
theorem _root_.solution {d : ℕ} (b : Fin d → E) (hb : ∀ e : E, ∃ f : Fin d → F, e = ∑ k, f k • b k)
    {R : Type} [CommRing R] [Algebra F R] (x : E ⊗[F] R) :
    ∃ c : Fin d → R, x = ∑ k, b k ⊗ₜ[F] c k := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul e r =>
    obtain ⟨f, hf⟩ := hb e
    refine ⟨fun k => f k • r, ?_⟩
    rw [hf, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨c1, h1⟩ := hx
    obtain ⟨c2, h2⟩ := hy
    refine ⟨c1 + c2, ?_⟩
    simp [h1, h2, TensorProduct.tmul_add, Finset.sum_add_distrib]
end PI.UnitaryApproxFinWork
