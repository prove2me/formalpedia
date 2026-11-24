-- Prove2me | solution 1 for PI.WAU.exists_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:43:58.339413+00:00
-- url     : https://prove2.me/submissions/ac1e8371-b09a-42d1-917c-5fee358b8ee0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CartierFrobeniusFormLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CoordTmulOneMul
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_SmulEqAlgebraMapMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped TensorProduct
namespace PI.WAU
theorem _root_.solution {K : Type} [Field K] [NumberField K] (x : K) :
    ∃ m : ℕ, 0 < m ∧ ∃ a : 𝓞 K, (m : K) * x = algebraMap (𝓞 K) K a := by
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hN0 : Ideal.absNorm (Ideal.span {s}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hs0
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {s}))
  refine ⟨Ideal.absNorm (Ideal.span {s}), Nat.pos_of_ne_zero hN0, t * a, ?_⟩
  have hsK : algebraMap (𝓞 K) K s ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)]
  have : ((Ideal.absNorm (Ideal.span {s}) : ℕ) : K) = algebraMap (𝓞 K) K t * algebraMap (𝓞 K) K s := by
    rw [← map_mul, ht, map_natCast]
  rw [this, map_mul]
  field_simp
end PI.WAU
