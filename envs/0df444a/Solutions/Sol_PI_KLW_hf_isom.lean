-- Prove2me | solution 1 for PI.KLW.hf_isom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:47:53.005953+00:00
-- url     : https://prove2.me/submissions/8754c533-b08f-49f0-b4a9-a7baaff52c7a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_RpOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_EquivariantPartsOfFiniteType
import Theorems.Thm_PI_KLW_sum_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW
variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
namespace PI.KLW
theorem _root_.solution (cj : E ≃ₐ[ℚ] E)
    (h : ∀ k : K, ∃ k' : K, cj (algebraMap K E k) = algebraMap K E k') {n : Type} [Fintype n]
    (g₀ : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)) (hg : PI.KerIso.IsIsom cj g₀) (x y : Fin 4 → E) :
    hf (conjK cj h) (g₀ x) (g₀ y) = ∑ a, Algebra.trace K E (x a * cj (y a)) :=
  (algebraMap K E).injective (by rw [← sum_conj, hg])
end PI.KLW
