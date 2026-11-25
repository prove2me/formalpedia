-- Prove2me | solution 1 for PI.UnipApproxD.IntegersDenseFiniteAdeles.exists_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:33:38.642005+00:00
-- url     : https://prove2.me/submissions/6ecafee7-1e14-47e3-8dc4-0dd49849061f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentApproximation_MemZeroLocusGLIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentApproximation_AddDense

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnipApproxD PI.UnipApproxD.IntegersDenseFiniteAdeles
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]
namespace PI.UnipApproxD.IntegersDenseFiniteAdeles
theorem _root_.solution (v : HeightOneSpectrum R) {U : Set (v.adicCompletion K)}
    (hU : U ∈ nhds (0 : v.adicCompletion K)) :
    ∃ r : R, r ≠ 0 ∧ ∀ y : v.adicCompletion K, Valued.v y ≤ v.intValuation r → y ∈ U := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hU
  have hpos : (0 : WithZero (Multiplicative ℤ)) < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
    have := MonoidWithZeroHom.ValueGroup₀.embedding_strictMono (zero_lt_iff.mpr γ.ne_zero)
    simpa using this
  obtain ⟨k, hk⟩ := WithZero.exists_exp_neg_natCast_lt hpos.ne'
  have hI : v.asIdeal ^ k ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot]; exact pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact v.ne_bot)
  obtain ⟨r, hrI, hr⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  refine ⟨r, hr, fun y hy => hγ ?_⟩
  show Valued.v.restrict y < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  exact lt_of_le_of_lt (hy.trans ((v.intValuation_le_pow_iff_mem r k).mpr hrI)) hk
end PI.UnipApproxD.IntegersDenseFiniteAdeles
