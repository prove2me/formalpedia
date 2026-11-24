-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.nat_mult
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:51:56.294829+00:00
-- url     : https://prove2.me/submissions/e4ee15c0-c4d2-4506-8880-a03f1c72c316

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictRing
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_IsIntegralOfIntOE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
open PI.UJClassFin
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PI.UnitaryGroupMassFormula.UJClassFin
theorem _root_.solution (c : 𝓞 F) (hc : c ≠ 0) : ∃ k : ℕ, 0 < k ∧ ∃ c' : 𝓞 F, (k : 𝓞 F) = c * c' := by
  obtain ⟨c', h⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {c}))
  refine ⟨Ideal.absNorm (Ideal.span {c}), ?_, c', by rw [← h, mul_comm]⟩
  rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
  exact hc
end PI.UnitaryGroupMassFormula.UJClassFin
