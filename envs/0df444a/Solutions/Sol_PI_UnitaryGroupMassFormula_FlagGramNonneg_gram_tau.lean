-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.FlagGramNonneg.gram_tau
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:47:28.578419+00:00
-- url     : https://prove2.me/submissions/62d884fe-c863-4d82-bdd4-86ed4dd96e98

import Definitions.Def_Formalism_PeriodIntegrals_FlagGramNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FlagGramNonnegativity_ConjTMulMulApply
import Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_tau_form
import Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_conjT_mul_mul_apply

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
    (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) {ι : Type} (y : ι → V) (i j : ι) :
    ((Matrix.of fun n k => τ (b.repr (y k) n))ᴴ * ((PI.FlagGramNonneg.gram hT b).map τ) *
      (Matrix.of fun n k => τ (b.repr (y k) n))) i j = τ (hT (y i) (y j)) := by
  rw [conjT_mul_mul_apply, tau_form hT b τ hτ]
  rfl
end PI.UnitaryGroupMassFormula.FlagGramNonneg
