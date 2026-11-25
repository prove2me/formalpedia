-- Prove2me | solution 1 for PI.LocalEndW.mem_pow_smul_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:50:48.199122+00:00
-- url     : https://prove2.me/submissions/c6dd1189-07ff-4de4-955c-3370b1cf6866

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_ValSurjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_HenselRoot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Filter Topology
open PI PI.LocalEndW
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace PI.LocalEndW
theorem _root_.solution (ϖ : v.adicCompletionIntegers F) (hϖ : ϖ ≠ 0) (n : ℕ)
    (x : v.adicCompletionIntegers F) :
    x ∈ ((Ideal.span {ϖ}) ^ n • ⊤ : Submodule (v.adicCompletionIntegers F) (v.adicCompletionIntegers F)) ↔
      ‖(x : v.adicCompletion F)‖ ≤ ‖(ϖ : v.adicCompletion F)‖ ^ n := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    (HeightOneSpectrum.adicCompletionIntegers.integers (K := F) (v := v)).dvd_iff_le, ← norm_pow,
    Valued.toNormedField.norm_le_iff]
  simp
end PI.LocalEndW
