-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.FlagGramNonneg.tau_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:40:38.768155+00:00
-- url     : https://prove2.me/submissions/45d1ec8c-32f5-480d-ba6f-bda0d609cddf

import Definitions.Def_Formalism_PeriodIntegrals_FlagGramNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FlagGramNonnegativity_ConjTMulMulApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PI.FlagGramNonneg
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FlagGramNonneg
namespace PI.UnitaryGroupMassFormula.FlagGramNonneg
theorem _root_.solution {E : Type} [Field E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
    (hT : V →ₗ⋆[E] V →ₗ[E] E) {N : ℕ} (b : Module.Basis (Fin N) E V) (τ : E →+* ℂ)
    (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) (v w : V) :
    τ (hT v w) = star (fun n => τ (b.repr v n)) ⬝ᵥ
      (((PI.FlagGramNonneg.gram hT b).map τ) *ᵥ (fun n => τ (b.repr w n))) := by
  conv_lhs => rw [← b.sum_repr v, ← b.sum_repr w]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ₂, LinearMap.map_smul, smul_eq_mul,
    map_mul, starRingEnd_apply, hτ, dotProduct, mulVec, Matrix.map_apply, PI.FlagGramNonneg.gram,
    Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end PI.UnitaryGroupMassFormula.FlagGramNonneg
